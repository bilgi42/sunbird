//! Locators for Desktop Phoenix on macOS, `Discord Phoenix.app`'s arm64
//! `Discord` executable.

use phoenix_hook::{
   image::Image,
   pattern::Pattern,
};

use crate::{
   Found,
   one,
};

/// The executable's file name, which iOS Phoenix's `PhoenixFatClient` never
/// shares.
pub const EXECUTABLE: &str = "Discord";

/// The body of `<ClientAccessGate as ClientSelector>::read` after its
/// prologue: `mov x19, x2; mov x20, x0; bl enforced; cbz w0, open; ldr x1,
/// [x19, #ready]; add x8, sp, #8; mov x0, x20; mov w2, #1; bl access_at; ldrb
/// w20, [sp, #8]`, then the drop and `open: mov w20, #2; mov x0, x20`.
///
/// Read on build 2233. The `ldr`'s field offset and the calls are wildcards.
const ACCESS_GATE: Pattern = Pattern::new(
   "F3 03 02 AA F4 03 00 AA ?? ?? ?? ?? ?? ?? 00 34 61 ?? ?? F9 E8 23 00 91 E0 03 14 AA 22 00 80 \
    52 ?? ?? ?? ?? F4 23 40 39 E8 13 40 B9 ?? ?? ?? 36 E1 0F 40 F9 ?? ?? ?? ?? ?? ?? ?? 14 54 00 \
    80 52 E0 03 14 AA",
);

/// The prologue's four instructions before [`ACCESS_GATE`].
const PROLOGUE_LEN: usize = 16;

/// `<ClientAccessGate as ClientSelector>::read`, `u8 read(..)` where 2 is
/// "no gate", the value it answers when access is not enforced.
pub fn access_gate(image: &Image<'_>) -> Found<usize> {
   let body = one("access gate", &image.scan(ACCESS_GATE))?;
   let entry = body
      .checked_sub(PROLOGUE_LEN)
      .ok_or("access gate: the body has no prologue")?;
   // `sub sp, sp, #imm` opens the frame.
   match image.read(entry, 4) {
      Some(&[a, b, c, d]) if u32::from_le_bytes([a, b, c, d]) & 0xFFC0_03FF == 0xD100_03FF => {
         Ok(entry)
      },
      _ => Err(format!("access gate at {entry:#x} does not open a frame")),
   }
}

/// `client_access::enforced` after its frame: `ldr x8, [x0]; add x0, x8,
/// #state; bl; ldrb w8, [x0, #flag]; mov w9, #1; bic w0, w9, w8`, then the
/// frame's `ldp` and `ret`.
///
/// Read on build 2233. The two offsets and the call are wildcards.
const ENFORCED: Pattern = Pattern::new(
   "FD 7B BF A9 FD 03 00 91 08 00 40 F9 00 ?? ?? 91 ?? ?? ?? ?? 08 ?? ?? 39 29 00 80 52 20 01 28 \
    0A FD 7B C1 A8 C0 03 5F D6",
);

/// [`ENFORCED`]'s length in bytes.
const ENFORCED_LEN: usize = 40;

/// Offset of `bl enforced` in [`ACCESS_GATE`].
const ENFORCED_CALL: usize = 8;

/// `client_access::enforced`, `bool enforced(..)`, the first call of the
/// [`access_gate`] function at `read`. `push_access` reads it too, without
/// going through `read`, and drops every message alert while it is true.
pub fn access_enforced(image: &Image<'_>, read: usize) -> Found<usize> {
   let call = read + PROLOGUE_LEN + ENFORCED_CALL;
   let enforced = image
      .read_u32(call)
      .filter(|bl| bl & 0xFC00_0000 == 0x9400_0000)
      .map(|bl| {
         // imm26 counts instructions, sign-extended.
         let words = ((bl << 6).cast_signed() >> 6) as isize;
         call.wrapping_add_signed(words * 4)
      })
      .ok_or_else(|| format!("access gate at {read:#x} does not call enforced"))?;
   match image.read(enforced, ENFORCED_LEN) {
      Some(body) if ENFORCED.find_in(body) == [0] => Ok(enforced),
      _ => Err(format!("enforced at {enforced:#x} has changed")),
   }
}
