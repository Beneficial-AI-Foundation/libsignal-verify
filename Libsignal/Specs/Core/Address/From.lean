/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Libsignal.Code.Funs

/-! # Spec Theorem for `u8::from` (From<ServiceIdKind> trait)

Specification and proof for
`U8.Insts.CoreConvertFromServiceIdKind.from`,
which implements `From<ServiceIdKind> for u8` via an explicit
`impl From<ServiceIdKind> for u8` block.

`ServiceIdKind` is a `#[repr(u8)]` enum with two variants:
  - `Aci = 0`  (Account Identity)
  - `Pni = 1`  (Phone Number Identity)

The `from` conversion encodes a `ServiceIdKind` variant as its
raw `u8` discriminant:
  - `from(Aci) = 0`
  - `from(Pni) = 1`

This is the right inverse of the `TryFrom<u8> for ServiceIdKind`
conversion (which maps `0 ↦ Ok(Aci)`, `1 ↦ Ok(Pni)`):
  `try_from(u8::from(kind)) = Ok(kind)`   for all `kind : ServiceIdKind`

The function always succeeds monadically — `value as u8` on a
`#[repr(u8)]` enum is a total operation that cannot panic.

**Source**: rust/core/src/address.rs, lines 27:4-27:41
(`impl From<ServiceIdKind> for u8 { fn from(value: ServiceIdKind) -> Self { value as u8 } }`)
-/

open Aeneas Aeneas.Std Result

namespace signal_crypto.U8.Insts.CoreConvertFromServiceIdKind

/-
natural language description:

• Takes a single `ServiceIdKind` value `value` representing one of
  the two service-identity variants (`Aci` or `Pni`).
• Reads the discriminant of `value` (the `#[repr(u8)]` tag):
    – `Aci` has discriminant `0`
    – `Pni` has discriminant `1`
• Casts the discriminant to `U8` and returns it.

natural language specs:

• The function always succeeds monadically (`ok …`) for every
  `ServiceIdKind` input — it never panics or diverges.
• When `value = Aci`, the result is `0#u8`.
• When `value = Pni`, the result is `1#u8`.
-/

@[step]
theorem from_spec (value : libsignal_core.address.ServiceIdKind) :
    «from» value ⦃ result =>
      (value = .Aci → result = 0#u8) ∧
      (value = .Pni → result = 1#u8) ⦄ := by
  unfold «from»
  step*
  cases value <;> simp only [reduceCtorEq] <;> decide

end signal_crypto.U8.Insts.CoreConvertFromServiceIdKind
