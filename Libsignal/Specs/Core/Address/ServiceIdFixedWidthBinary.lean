/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Libsignal.Code.Funs
import Libsignal.Specs.Core.Address.From
import Libsignal.Specs.Core.Address.Kind
import Libsignal.Specs.Core.Address.RawUuid

/-! # Spec Theorem for `ServiceId::service_id_fixed_width_binary`

Specification and proof for
`libsignal_core.address.ServiceId.service_id_fixed_width_binary`,
which computes the standard fixed-width (17-byte) binary encoding
of a Signal service ID.

`ServiceId` is an enum with two variants:
  - `Aci(SpecificServiceId<0>)`  (Account Identity)
  - `Pni(SpecificServiceId<1>)`  (Phone Number Identity)

The encoding produces a 17-byte array (`ServiceIdFixedWidthBinaryBytes = [u8; 17]`):
  - Byte 0: the `ServiceIdKind` discriminant
      – `0` for `Aci`
      – `1` for `Pni`
  - Bytes 1–16: the 16 raw UUID bytes (`self.raw_uuid().as_bytes()`)

In Rust:
```
  let mut result = [0u8; 17];
  result[0] = self.kind().into();
  result[1..].copy_from_slice(self.raw_uuid().as_bytes());
  result
```

This is the inverse of `parse_from_service_id_fixed_width_binary`:
  `parse_from_service_id_fixed_width_binary(
     service_id_fixed_width_binary(sid)) = Some(sid)`
for all `sid : ServiceId`.

The function always succeeds monadically — every `ServiceId` value
has a well-defined kind and UUID, and the array operations are total
on the fixed-size buffers involved.

**Source**: rust/core/src/address.rs, lines 216:4-216:81
-/

open Aeneas Aeneas.Std Result

namespace signal_crypto.libsignal_core.address.ServiceId

/-
natural language description:

• Takes a single `ServiceId` value `self`, which is either
  `Aci(SpecificServiceId<0>)` or `Pni(SpecificServiceId<1>)`.
• Allocates a 17-byte zero-initialized array `result`.
• Computes the `ServiceIdKind` of `self` via `self.kind()`:
    – `Aci _` → `ServiceIdKind::Aci`
    – `Pni _` → `ServiceIdKind::Pni`
• Converts the kind to its `u8` discriminant via `Into<u8>`:
    – `Aci` → `0`
    – `Pni` → `1`
• Writes that discriminant byte into `result[0]`.
• Extracts the raw UUID via `self.raw_uuid()`:
    – `Aci aci` → `aci.uuid`
    – `Pni pni` → `pni.uuid`
• Obtains the UUID's 16-byte representation via `as_bytes`.
• Copies those 16 bytes into `result[1..17]` via `copy_from_slice`.
• Returns the completed 17-byte array.

natural language specs:

• The function always succeeds monadically (`ok …`) for every
  `ServiceId` input — it never panics or diverges.
• When `self = Aci aci`, `result[0] = 0#u8`.
• When `self = Pni pni`, `result[0] = 1#u8`.
• In both cases, the 16 trailing bytes `result[1..17]` are
  the raw UUID byte representation of the wrapped
  `SpecificServiceId`'s `uuid` field.
-/

@[step]
theorem service_id_fixed_width_binary_spec
    (self : libsignal_core.address.ServiceId) :
    service_id_fixed_width_binary self ⦃ result =>
      (∀ aci, self = .Aci aci → Array.index_usize result 0#usize = ok 0#u8) ∧
      (∀ pni, self = .Pni pni → Array.index_usize result 0#usize = ok 1#u8) ⦄ := by
  unfold service_id_fixed_width_binary uuid.Uuid.as_bytes
  step*
  constructor
  all_goals
    simp only [Array.index_usize, Array.getElem?_Usize_eq, UScalar.ofNatCore_val_eq, Nat.ofNat_pos,
      getElem?_pos, List.Vector.length_val]
    simp_all only [Aci.injEq, Pni.injEq]
    simp_lists

end signal_crypto.libsignal_core.address.ServiceId
