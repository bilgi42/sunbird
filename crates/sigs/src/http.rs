//! Build-independent discovery of Desktop Phoenix's `libdiscord/crates/http`
//! `ReqwestTransport` and `SendFuture` vtable slots.
//!
//! Desktop Phoenix routes all Discord REST traffic through a single-method
//! `dyn Transport` trait (`ReqwestTransport::send(&self, req) -> Pin<Box<dyn
//! Future>>`). Swapping the `send` and `poll` vtable slots in `.rdata`
//! intercepts every outgoing request and incoming response without any inline
//! code patching.

use memchr::memchr_iter;
use phoenix_hook::{
   image::Image,
   x86::{
      Abi,
      Store,
      call_target,
      jump_target,
   },
};

use crate::Found;

/// Unique error string inside `ReqwestTransport::send` when handed a mobile
/// host-file body.
const HOST_FILE_ANCHOR: &[u8] = b"a host file body needs the host's transport";

/// The size of `http::HeaderMap`, which `send`'s request starts with.
pub const HEADER_MAP_SIZE: usize = 0x60;
/// The size of the request's body enum.
pub const BODY_SIZE: usize = 0x38;
/// The size of a `String`, and of an `http::Method`.
pub const STRING_SIZE: usize = 0x18;
/// The size of the `Poll<Result<Response>>` the runtime reads `poll`'s result
/// as on builds whose `poll` writes no further.
pub const POLL_RESULT_SIZE: usize = 0x80;
/// The size of the response's body enum: its tag and a `bytes::Bytes` or a
/// `Box<dyn Stream>`.
pub const RESPONSE_BODY_SIZE: usize = 0x28;
/// The body enum's tag for a `Box<dyn Stream>`, the one `poll` stores as a
/// constant.
pub const RESPONSE_BODY_STREAM: u64 = 1;

/// How `poll`'s `Poll<Result<Response>>` is laid out.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum ResponseLayout {
   /// The fixed [`POLL_RESULT_SIZE`] layout with the body in a `Vec<u8>`.
   Legacy,
   /// A layout read from `poll`'s stores.
   Located(ResultLayout),
}

/// Where a located `poll` result keeps the fields the runtime touches.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct ResultLayout {
   /// The whole result's size.
   pub size:    usize,
   /// Word 0 of a `Poll::Pending`.
   pub pending: u64,
   /// Word 0 of a `Poll::Ready(Err)`.
   pub err:     u64,
   /// The `u16` status.
   pub status:  usize,
   /// The body enum's tag, followed by its payload.
   pub body:    usize,
}

/// Where `send`'s request keeps the fields the runtime reads, after the
/// `http::HeaderMap` it starts with. Builds move them as fields are added.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct RequestLayout {
   /// The body enum's tag, followed by its `Bytes`.
   pub body:   usize,
   /// The URL `String`.
   pub url:    usize,
   /// The `http::Method`.
   pub method: usize,
}

/// Located vtable slots and host allocator entry points for Desktop Phoenix's
/// `libdiscord/crates/http` transport.
#[derive(Debug, Clone)]
pub struct DesktopHttpTransport {
   /// All `.rdata` vtable slots holding `ReqwestTransport::send` (may be
   /// duplicated across LLVM CGUs).
   pub send_slots:   Vec<usize>,
   /// Original `ReqwestTransport::send` function address.
   pub send_fn:      usize,
   /// Where `send`'s request keeps its fields.
   pub request:      RequestLayout,
   /// All `.rdata` vtable slots holding `SendFuture::poll`.
   pub poll_slots:   Vec<usize>,
   /// Original `SendFuture::poll` function address.
   pub poll_fn:      usize,
   /// How `poll` lays out its result.
   pub responses:    Found<ResponseLayout>,
   /// The `SendFuture`'s drop, beside every poll slot.
   pub poll_drop:    Found<usize>,
   /// Host's `__rust_alloc(size, align)` if located.
   pub host_alloc:   Option<usize>,
   /// Host's `__rust_dealloc(ptr, size, align)` if located.
   pub host_dealloc: Option<usize>,
}

impl DesktopHttpTransport {
   /// Scans a 64-bit PE or ELF `Image` for `ReqwestTransport::send`, its
   /// returned `SendFuture::poll` vtable, and the host's Rust allocator
   /// functions.
   pub fn locate(image: &Image<'_>) -> Found<Self> {
      if image.pointer_width != 8 {
         return Err("not a 64-bit image".to_owned());
      }
      let abi = Abi::of(image);

      // 1. The unique anchor string inside `ReqwestTransport::send`.
      let anchor = crate::one("transport anchor", &image.find_bytes(HOST_FILE_ANCHOR))?;
      let lea = *crate::desktop::lea_refs(image, anchor)
         .first()
         .ok_or("transport anchor is never loaded")?;
      let (send_fn, send_end) = image
         .function_bounds(lea)
         .ok_or("ReqwestTransport::send has no unwind entry")?;
      let request = request_layout(
         abi,
         image
            .read(send_fn, send_end - send_fn)
            .ok_or("send is unreadable")?,
         send_fn,
      )?;

      // 2. Every `dyn Transport` vtable slot in `.rdata` pointing to `send_fn`.
      let send_slots = find_vtable_method_slots(image, send_fn, 1..=0x2000);
      if send_slots.is_empty() {
         return Err("no Transport vtable holds ReqwestTransport::send".to_owned());
      }

      // 3. The `Box::pin` of the async state machine returns `(ptr,
      //    poll_vtable)`, from `send_fn` itself or a small helper it calls.
      let (poll_fn, poll_vtable, box_future) = find_poll_vtable(image, send_fn, send_end)?;
      let mut poll_slots = find_vtable_method_slots(image, poll_fn, 0x100..=0x4000);
      // shortcut: a result pointer `poll` keeps on the stack is not
      // followed, so a build that writes past the legacy layout is only told
      // apart when it writes through a register, as the ones from 2026-11-23
      // on do.
      let responses = image
         .function_bounds(poll_fn)
         .and_then(|(start, end)| image.read(start, end - start).map(|code| (start, code)))
         .map_or(Ok(ResponseLayout::Legacy), |(start, code)| {
            response_layout(&phoenix_hook::x86::arg_use(abi, 0, code, start))
         });
      let direct_slot = poll_vtable + 24;
      if !poll_slots.contains(&direct_slot) {
         poll_slots.push(direct_slot);
      }
      let mut drops: Vec<usize> = poll_slots
         .iter()
         .filter_map(|&slot| image.read_usize(slot.checked_sub(24)?))
         .collect();
      drops.sort_unstable();
      drops.dedup();
      let poll_drop = match drops[..] {
         [drop] if image.is_function(drop) => Ok(drop),
         _ => Err(format!("poll's vtables hold {drops:#x?} as their drop")),
      };

      // 4. The host's own `__rust_alloc` and `__rust_dealloc`, so response body
      //    growth stays allocator-compatible. Both hand the same global
      //    allocator static to its implementation.
      let host_alloc = box_future.and_then(|box_future| find_host_alloc(image, abi, box_future));
      let host_dealloc = find_host_dealloc(image, abi, send_fn, send_end)
         .or_else(|| host_alloc.and_then(|alloc| dealloc_beside(image, abi, alloc)));
      let (host_alloc, host_dealloc) = match (host_alloc, host_dealloc) {
         (Some(alloc), Some(dealloc))
            if allocator_static(image, abi, alloc).is_none()
               || allocator_static(image, abi, alloc) != allocator_static(image, abi, dealloc) =>
         {
            (None, None)
         },
         pair => pair,
      };

      Ok(Self {
         send_slots,
         send_fn,
         request,
         poll_slots,
         poll_fn,
         responses,
         poll_drop,
         host_alloc,
         host_dealloc,
      })
   }
}

/// Reads where `send` at `ip` keeps its request's fields. It moves the
/// headers out whole right after the call that starts the `reqwest` request
/// from the method and URL, and dispatches on the body's tag through a jump
/// table.
fn request_layout(abi: Abi, code: &[u8], ip: usize) -> Found<RequestLayout> {
   let used = phoenix_hook::x86::arg_use(abi, 1, code, ip);
   let copy = used
      .copies
      .iter()
      .find(|copy| copy.offset == 0 && copy.len == HEADER_MAP_SIZE)
      .ok_or("send never moves the request's headers out")?;
   let call = copy
      .after_calls
      .checked_sub(1)
      .and_then(|at| used.calls.get(at))
      .ok_or("no call before the headers move")?;
   let (Some(method), Some(url)) = (call[2], call[3]) else {
      return Err(format!(
         "the request call takes {call:?}, not a method and URL"
      ));
   };
   let mut dispatches = used.dispatches.clone();
   dispatches.sort_unstable();
   dispatches.dedup();
   let [body] = dispatches[..] else {
      return Err(format!("{dispatches:#x?} could each be the body's tag"));
   };
   // The runtime takes a reference to each field, so they must not overlap.
   let mut fields = [
      (0, HEADER_MAP_SIZE),
      (body, BODY_SIZE),
      (url, STRING_SIZE),
      (method, STRING_SIZE),
   ];
   fields.sort_unstable();
   if fields
      .windows(2)
      .any(|pair| pair[0].0 + pair[0].1 > pair[1].0)
      || fields.iter().any(|&(offset, _)| offset % 8 != 0)
   {
      return Err(format!(
         "body {body:#x}, url {url:#x} and method {method:#x} overlap"
      ));
   }
   Ok(RequestLayout { body, url, method })
}

/// Reads how `poll` lays out its result from the stores it makes through it.
///
/// Every return writes its tag to word 0: Pending a constant on its own, and
/// Err a constant in the tail it shares with Ok, which goes on to store the
/// status, the one `u16`. The body enum's stream case stores its tag as a
/// constant, then the box's data pointer and vtable.
fn response_layout(used: &phoenix_hook::x86::ArgUse) -> Found<ResponseLayout> {
   if used.extent <= POLL_RESULT_SIZE {
      return Ok(ResponseLayout::Legacy);
   }
   let stores = &used.stores;
   let size = stores
      .iter()
      .map(|store| store.offset + store.size)
      .max()
      .unwrap_or(0)
      .next_multiple_of(8);

   let mut statuses: Vec<(usize, usize)> = stores
      .iter()
      .enumerate()
      .filter(|(_, store)| store.size == 2)
      .map(|(at, store)| (store.offset, at))
      .collect();
   statuses.sort_unstable();
   statuses.dedup_by_key(|&mut (offset, _)| offset);
   let [(status, status_at)] = statuses[..] else {
      return Err(format!(
         "{} word stores could each be the status",
         statuses.len()
      ));
   };

   let tag = |store: &Store| (store.offset == 0 && store.size == 8).then_some(store.constant);
   let mut tags: Vec<u64> = stores.iter().filter_map(tag).flatten().collect();
   tags.sort_unstable();
   tags.dedup();
   let err = stores[..status_at]
      .iter()
      .rev()
      .find_map(tag)
      .flatten()
      .ok_or("the status is not stored after a constant tag")?;
   let others: Vec<u64> = tags.iter().copied().filter(|&value| value != err).collect();
   let [pending] = others[..] else {
      return Err(format!("tags {tags:#x?} are not one Pending and one Err"));
   };

   let written = |offset: usize| {
      stores
         .iter()
         .any(|store| store.offset == offset && store.size == 8)
   };
   let mut bodies: Vec<usize> = stores
      .iter()
      .filter(|store| {
         store.offset != 0
            && store.size == 8
            && store.constant == Some(RESPONSE_BODY_STREAM)
            && written(store.offset + 8)
            && written(store.offset + 0x10)
      })
      .map(|store| store.offset)
      .collect();
   bodies.sort_unstable();
   bodies.dedup();
   let [body] = bodies[..] else {
      return Err(format!("{bodies:#x?} could each be the body's tag"));
   };

   // The runtime takes a reference to each field, so they must not overlap.
   let mut fields = [(0, 8), (body, RESPONSE_BODY_SIZE), (status, 2)];
   fields.sort_unstable();
   if fields
      .windows(2)
      .any(|pair| pair[0].0 + pair[0].1 > pair[1].0)
      || fields.iter().any(|&(offset, len)| offset + len > size)
      || body % 8 != 0
      || status % 2 != 0
   {
      return Err(format!(
         "body {body:#x} and status {status:#x} overlap in {size:#x} bytes"
      ));
   }
   Ok(ResponseLayout::Located(ResultLayout {
      size,
      pending,
      err,
      status,
      body,
   }))
}

/// Finds all `.rdata` vtable method-0 slots (`vtable + 24`) holding `method_fn`
/// where `[drop_fn, size, align, method_fn]` passes Rust trait vtable checks.
fn find_vtable_method_slots(
   image: &Image<'_>,
   method_fn: usize,
   size_range: std::ops::RangeInclusive<usize>,
) -> Vec<usize> {
   let mut slots = Vec::new();
   for slot in image.pointers_to(method_fn) {
      let Some(vtable) = slot.checked_sub(24) else {
         continue;
      };
      let (Some(drop_fn), Some(size), Some(align)) = (
         image.read_usize(vtable),
         image.read_usize(vtable + 8),
         image.read_usize(vtable + 16),
      ) else {
         continue;
      };
      if image.is_function(drop_fn)
         && size_range.contains(&size)
         && align.is_power_of_two()
         && align <= 64
      {
         slots.push(slot);
      }
   }
   slots.sort_unstable();
   slots.dedup();
   slots
}

/// The functions called inside `[start, end)`.
fn calls(image: &Image<'_>, start: usize, end: usize) -> Vec<usize> {
   crate::desktop::callees(image, start, end)
      .into_iter()
      .filter(|&callee| image.is_function(callee))
      .collect()
}

/// The bounds of `func` when it is at most `max` bytes long.
fn small(image: &Image<'_>, func: usize, max: usize) -> Option<(usize, usize)> {
   image
      .function_bounds(func)
      .filter(|&(start, end)| end - start <= max)
}

/// The `SendFuture` vtable loaded with `lea rdx, [rip + disp32]` (`48 8D 15`),
/// the high half of the returned fat pointer, in a small callee of `send_fn`
/// that boxes the future, or else in `send_fn`. Returns `(poll_fn, vtable,
/// box_future)`, where `box_future` is the callee that boxes it, when one does.
///
/// `lea rdx` also passes an argument, so the vtable must be the only one in
/// whichever of the two places has any.
fn find_poll_vtable(
   image: &Image<'_>,
   send_fn: usize,
   send_end: usize,
) -> Found<(usize, usize, Option<usize>)> {
   let boxers: Vec<(usize, usize)> = calls(image, send_fn, send_end)
      .into_iter()
      .filter_map(|callee| small(image, callee, 0x80))
      .collect();
   for group in [boxers, vec![(send_fn, send_end)]] {
      let mut found: Vec<(usize, usize, usize)> = group
         .into_iter()
         .flat_map(|(cs, ce)| {
            future_vtables(image, cs, ce).map(move |(vtable, poll_fn)| (vtable, poll_fn, cs))
         })
         .collect();
      found.sort_unstable();
      found.dedup_by_key(|&mut (vtable, ..)| vtable);
      match found[..] {
         [] => {},
         [(vtable, poll_fn, cs)] => return Ok((poll_fn, vtable, (cs != send_fn).then_some(cs))),
         _ => return Err(format!("{} SendFuture vtable candidates", found.len())),
      }
   }
   Err("SendFuture vtable not found".to_owned())
}

/// `(vtable, poll_fn)` for each `lea rdx, [rip + vtable]` in `[cs, ce)` whose
/// target reads as a future's vtable.
fn future_vtables(image: &Image<'_>, cs: usize, ce: usize) -> impl Iterator<Item = (usize, usize)> {
   let code = image.read(cs, ce - cs).unwrap_or_default();
   memchr_iter(0x8D, code)
      .filter(move |&pos| {
         pos > 0 && pos + 6 <= code.len() && code[pos - 1] == 0x48 && code[pos + 1] == 0x15
      })
      .filter_map(move |pos| {
         let disp = i32::from_le_bytes(code[pos + 2..pos + 6].try_into().ok()?);
         let vtable = (cs + pos + 6).checked_add_signed(disp as isize)?;
         let (drop_fn, size, align, poll_fn) = (
            image.read_usize(vtable)?,
            image.read_usize(vtable + 8)?,
            image.read_usize(vtable + 16)?,
            image.read_usize(vtable + 24)?,
         );
         (image.is_function(drop_fn)
            && image.is_function(poll_fn)
            && (0x100..=0x4000).contains(&size)
            && align == 8)
            .then_some((vtable, poll_fn))
      })
      .collect::<Vec<_>>()
      .into_iter()
}

/// `__rust_alloc(size, align)`, reached from `box_future`.
///
/// Some call in `box_future` or a small callee passes the future's alignment,
/// a constant 8, in an argument register. Win64 builds make that the call to
/// `__rust_alloc`, System V ones a call to `Layout` wrappers that forward to
/// it, so small callees are followed breadth-first to the first function
/// shaped like `__rust_alloc`: its first call, whether the allocator is set
/// up, is followed by `test al, al`. Bool helpers share that shape, so the
/// first level with any must have exactly one.
fn find_host_alloc(image: &Image<'_>, abi: Abi, box_future: usize) -> Option<usize> {
   let (bs, be) = image.function_bounds(box_future)?;
   let align_8: Vec<Vec<u8>> = (0..2)
      .flat_map(|index| crate::desktop::imm_loads(abi.arg(index), 8))
      .collect();
   let mut frontier = Vec::new();
   for (ws, we) in std::iter::once((bs, be)).chain(
      calls(image, bs, be)
         .into_iter()
         .filter_map(|f| small(image, f, 0x60)),
   ) {
      let code = image.read(ws, we - ws)?;
      for pos in 0..code.len() {
         let Some((_, callee)) = call_target(image, &code[pos..], ws + pos) else {
            continue;
         };
         let before = &code[pos.saturating_sub(12)..pos];
         if align_8
            .iter()
            .any(|load| before.windows(load.len()).any(|w| w == load))
            && image.is_function(callee)
         {
            frontier.push(callee);
         }
      }
   }
   for _ in 0..3 {
      let mut found: Vec<usize> = frontier
         .iter()
         .copied()
         .filter(|&func| checks_allocator(image, func))
         .collect();
      found.sort_unstable();
      found.dedup();
      match found[..] {
         [] => {},
         [alloc] => return Some(alloc),
         _ => return None,
      }
      frontier = frontier
         .iter()
         .filter_map(|&func| small(image, func, 0x60))
         .flat_map(|(start, end)| calls(image, start, end))
         .collect();
   }
   None
}

/// Whether the first call in `func` is followed by `test al, al`.
fn checks_allocator(image: &Image<'_>, func: usize) -> bool {
   let Some(code) = image.read(func, 0x20) else {
      return false;
   };
   phoenix_hook::x86::disasm(code, func, 12)
      .iter()
      .find(|line| line.text.starts_with("call "))
      .is_some_and(|call| image.read(call.addr + call.len, 2) == Some(&[0x84, 0xC0]))
}

/// Follows `send_fn` → request builder helper → leaf `Method::drop`, a tail
/// call `__rust_dealloc(ptr, size, 1)` that sets only the alignment
/// argument. Leaf functions have no `.pdata` entry on Windows x64, so inner
/// call targets are checked via `is_code`. Other leaves end the same way, so
/// the target must also count the freed bytes down with `lock sub`.
fn find_host_dealloc(
   image: &Image<'_>,
   abi: Abi,
   send_fn: usize,
   send_end: usize,
) -> Option<usize> {
   let tails = crate::desktop::imm_loads(abi.arg(2), 1);
   let dealloc_in = |code: &[u8], ip: usize| {
      tails.iter().find_map(|tail| {
         memchr::memmem::find_iter(code, tail).find_map(|hit| {
            // A size-optimized leaf may load the pointer between the two.
            let after = hit + tail.len();
            (after..code.len().min(after + 8)).find_map(|at| {
               jump_target(image, &code[at..], ip + at)
                  .filter(|&dealloc| image.is_function(dealloc) && counts_down(image, dealloc))
            })
         })
      })
   };
   for callee in calls(image, send_fn, send_end) {
      let Some((cs, ce)) = small(image, callee, 0x400) else {
         continue;
      };
      let Some(callee_code) = image.read(cs, ce - cs) else {
         continue;
      };
      for pos in 0..callee_code.len() {
         let Some((_, inner)) = call_target(image, &callee_code[pos..], cs + pos) else {
            continue;
         };
         if let Some(code) = image.read(inner, 0x30).filter(|_| image.is_code(inner))
            && let Some(dealloc) = dealloc_in(code, inner)
         {
            return Some(dealloc);
         }
      }
   }
   None
}

/// Whether `func` counts freed bytes down with `lock sub` near its start.
fn counts_down(image: &Image<'_>, func: usize) -> bool {
   image.read(func, 0x40).is_some_and(|body| {
      body
         .windows(3)
         .any(|w| w == [0xF0, 0x48, 0x29] || w == [0xF0, 0x4C, 0x29])
   })
}

/// `__rust_dealloc`, from the allocator shims emitted next to `alloc`.
///
/// System V builds free request bodies through wrappers the leaf search in
/// [`find_host_dealloc`] does not reach. `alloc` hands the global allocator
/// static to its implementation with `lea rdi, [rip + disp32]`, and so does
/// `__rust_dealloc`, without `alloc`'s set-up check and counting the freed
/// bytes down after.
fn dealloc_beside(image: &Image<'_>, abi: Abi, alloc: usize) -> Option<usize> {
   /// The shims are a few dozen bytes each.
   const NEAR: usize = 0x400;
   let global = allocator_static(image, abi, alloc)?;
   let start = alloc.saturating_sub(NEAR);
   let mut found: Vec<usize> = lea_arg0(abi, image.read(start, 2 * NEAR)?, start)
      .filter(|&(_, target)| target == global)
      .filter_map(|(lea, _)| Some(image.function_bounds(lea)?.0))
      .filter(|&func| func != alloc && !checks_allocator(image, func) && counts_down(image, func))
      .collect();
   found.dedup();
   match found[..] {
      [dealloc] => Some(dealloc),
      _ => None,
   }
}

/// The global allocator static an allocator shim hands its implementation:
/// the first `lea` of it into the first argument register.
fn allocator_static(image: &Image<'_>, abi: Abi, shim: usize) -> Option<usize> {
   lea_arg0(abi, image.read(shim, 0x40)?, shim)
      .next()
      .map(|(_, target)| target)
}

/// Each `lea <first argument>, [rip + disp32]` in `code` at `ip`, as
/// (instruction, target).
fn lea_arg0(abi: Abi, code: &[u8], ip: usize) -> impl Iterator<Item = (usize, usize)> + '_ {
   let lea: &'static [u8] = match abi {
      Abi::Win64 => &[0x48, 0x8D, 0x0D],
      Abi::SysV => &[0x48, 0x8D, 0x3D],
   };
   memchr::memmem::find_iter(code, lea).filter_map(move |pos| {
      let disp = i32::from_le_bytes(code.get(pos + 3..pos + 7)?.try_into().ok()?);
      Some((ip + pos, (ip + pos + 7).checked_add_signed(disp as isize)?))
   })
}

#[cfg(test)]
mod tests {
   use super::*;

   /// The client call and headers move of `send` in the Linux build from
   /// 2026-11-23, around a body tag dispatch.
   const SEND: &[u8] = &[
      0x48, 0x89, 0xF3, // mov rbx, rsi
      0x48, 0x8B, 0x83, 0x08, 0x01, 0x00, 0x00, // mov rax, [rbx+0x108]
      0x48, 0x8D, 0x94, 0x24, 0x80, 0x09, 0x00, 0x00, // lea rdx, [rsp+0x980]
      0x48, 0x89, 0x42, 0x10, // mov [rdx+0x10], rax
      0x0F, 0x10, 0x83, 0xF8, 0x00, 0x00, 0x00, // movups xmm0, [rbx+0xF8]
      0x0F, 0x29, 0x02, // movaps [rdx], xmm0
      0x48, 0x8D, 0x8B, 0xB0, 0x00, 0x00, 0x00, // lea rcx, [rbx+0xB0]
      0xE8, 0x00, 0x00, 0x00, 0x00, // call
      0x6A, 0x60, // push 0x60
      0x59, // pop rcx
      0x48, 0x89, 0xDE, // mov rsi, rbx
      0xF3, 0xA4, // rep movsb
      0x48, 0x8B, 0x43, 0x78, // mov rax, [rbx+0x78]
      0x49, 0x63, 0x04, 0x87, // movsxd rax, [r15+rax*4]
   ];

   #[test]
   fn reads_the_request_layout_from_send() {
      assert_eq!(
         request_layout(Abi::SysV, SEND, 0x1000),
         Ok(RequestLayout {
            body:   0x78,
            url:    0xB0,
            method: 0xF8,
         })
      );
   }

   /// Pieces of `SendFuture::poll` from the Linux build 2233: its entry, its
   /// Pending return, and the tail its Err and Ok returns share.
   const POLL: &[u8] = &[
      0x49, 0x89, 0xD4, // mov r12, rdx
      0x48, 0x89, 0xF3, // mov rbx, rsi
      0x49, 0x89, 0xFE, // mov r14, rdi
      0x49, 0x83, 0xFF, 0x02, // cmp r15, 2
      0x75, 0x0B, // jne
      0x49, 0x83, 0x0E, 0xFF, // or qword [r14], -1
      0xB0, 0x03, // mov al, 3
      0xE9, 0xEB, 0x02, 0x00, 0x00, // jmp
      0x6A, 0x02, // push 2
      0x5D, // pop rbp
      0x80, 0xBB, 0x53, 0x05, 0x00, 0x00, 0x01, // cmp byte [rbx+0x553], 1
      0x75, 0x0C, // jne
      0x48, 0x8D, 0xBB, 0x10, 0x01, 0x00, 0x00, // lea rdi, [rbx+0x110]
      0xE8, 0xF2, 0x7F, 0x07, 0xFA, // call
      0x49, 0x89, 0x2E, // mov [r14], rbp
      0x4D, 0x89, 0x6E, 0x08, // mov [r14+8], r13
      0x0F, 0x28, 0x44, 0x24, 0x20, // movaps xmm0, [rsp+0x20]
      0x41, 0x0F, 0x11, 0x46, 0x10, // movups [r14+0x10], xmm0
      0x48, 0x8B, 0x44, 0x24, 0x30, // mov rax, [rsp+0x30]
      0x49, 0x89, 0x46, 0x20, // mov [r14+0x20], rax
      0x49, 0x8D, 0x7E, 0x28, // lea rdi, [r14+0x28]
      0x48, 0x8D, 0xB4, 0x24, 0x48, 0x09, 0x00, 0x00, // lea rsi, [rsp+0x948]
      0xB9, 0x50, 0x01, 0x00, 0x00, // mov ecx, 0x150
      0xF3, 0xA4, // rep movsb
      0x49, 0xC7, 0x86, 0x78, 0x01, 0x00, 0x00, 0x01, 0x00, 0x00,
      0x00, // mov qword [r14+0x178], 1
      0x4D, 0x89, 0xA6, 0x80, 0x01, 0x00, 0x00, // mov [r14+0x180], r12
      0x48, 0x8D, 0x05, 0xAC, 0xCB, 0x8F, 0x01, // lea rax, [rip+0x18FCBAC]
      0x49, 0x89, 0x86, 0x88, 0x01, 0x00, 0x00, // mov [r14+0x188], rax
      0x0F, 0x10, 0x84, 0x24, 0xF8, 0x00, 0x00, 0x00, // movups xmm0, [rsp+0xF8]
      0x0F, 0x10, 0x8C, 0x24, 0x08, 0x01, 0x00, 0x00, // movups xmm1, [rsp+0x108]
      0x41, 0x0F, 0x11, 0x86, 0x90, 0x01, 0x00, 0x00, // movups [r14+0x190], xmm0
      0x41, 0x0F, 0x11, 0x8E, 0xA0, 0x01, 0x00, 0x00, // movups [r14+0x1A0], xmm1
      0x48, 0x8B, 0x84, 0x24, 0x18, 0x01, 0x00, 0x00, // mov rax, [rsp+0x118]
      0x49, 0x89, 0x86, 0xB0, 0x01, 0x00, 0x00, // mov [r14+0x1B0], rax
      0x4D, 0x89, 0xBE, 0xB8, 0x01, 0x00, 0x00, // mov [r14+0x1B8], r15
      0x66, 0x41, 0x89, 0x96, 0xC0, 0x01, 0x00, 0x00, // mov [r14+0x1C0], dx
      0x45, 0x88, 0x86, 0xC2, 0x01, 0x00, 0x00, // mov [r14+0x1C2], r8b
      0xB0, 0x01, // mov al, 1
      0x88, 0x83, 0x51, 0x05, 0x00, 0x00, // mov [rbx+0x551], al
      0x4C, 0x89, 0xF0, // mov rax, r14
   ];

   fn layout(code: &[u8]) -> Found<ResponseLayout> {
      response_layout(&phoenix_hook::x86::arg_use(Abi::SysV, 0, code, 0x1840_2ADF))
   }

   #[test]
   fn reads_the_response_layout_from_poll() {
      assert_eq!(
         layout(POLL),
         Ok(ResponseLayout::Located(ResultLayout {
            size:    0x1C8,
            pending: u64::MAX,
            err:     2,
            status:  0x1C0,
            body:    0x178,
         }))
      );
   }

   #[test]
   fn keeps_the_legacy_layout_within_its_size() {
      let poll = [
         0x49, 0x89, 0xFE, // mov r14, rdi
         0x66, 0x41, 0x89, 0x56, 0x78, // mov [r14+0x78], dx
      ];
      assert_eq!(layout(&poll), Ok(ResponseLayout::Legacy));
   }

   #[test]
   fn refuses_a_response_without_a_stream_tag() {
      let mut poll = POLL.to_vec();
      let tag = poll
         .windows(7)
         .position(|code| code == [0x49, 0xC7, 0x86, 0x78, 0x01, 0x00, 0x00])
         .expect("POLL stores the body's tag");
      poll[tag + 7] = 3;
      assert!(layout(&poll).is_err());
   }

   #[test]
   fn refuses_overlapping_fields() {
      // The body's tag read from inside the headers instead.
      let mut send = SEND.to_vec();
      let tag = send
         .windows(4)
         .position(|code| code == [0x48, 0x8B, 0x43, 0x78])
         .expect("SEND reads the tag");
      send[tag + 3] = 0x58;
      assert!(request_layout(Abi::SysV, &send, 0x1000).is_err());
   }
}
