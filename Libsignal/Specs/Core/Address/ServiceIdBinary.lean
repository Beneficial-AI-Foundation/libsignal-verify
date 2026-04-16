/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Libsignal.Code.Funs
import Libsignal.Specs.Core.Address.ServiceIdFixedWidthBinary

/-! # Spec Theorem for `ServiceId::service_id_binary`

Specification and proof for
`libsignal_core.address.ServiceId.service_id_binary`,
which computes the standard variable-width binary encoding
of a Signal service ID.

`ServiceId` is an enum with two variants:
  - `Aci(SpecificServiceId<0>)`  (Account Identity)
  - `Pni(SpecificServiceId<1>)`  (Phone Number Identity)

The encoding produces a `Vec<u8>` whose length depends on the variant:
  - For `Aci`: 16 bytes — the raw UUID bytes only (no kind prefix)
  - For `Pni`: 17 bytes — the full fixed-width binary encoding
      (byte 0 = `1` for `Pni`, bytes 1–16 = the 16 raw UUID bytes)

This format is not self-delimiting; the length is needed to decode it.
`Aci` identities are encoded without a prefix for compactness, while
`Pni` identities use the fixed-width encoding to preserve the kind tag.

The function always succeeds monadically — every `ServiceId` value
has a well-defined UUID, and the array/slice/vec operations are total
on the fixed-size buffers involved.

**Source**: rust/core/src/address.rs, lines 206:4-206:46
-/

open Aeneas Aeneas.Std Result

namespace signal_crypto.libsignal_core.address.ServiceId

/-
natural language description:

• Takes a single `ServiceId` value `self`, which is either
  `Aci(SpecificServiceId<0>)` or `Pni(SpecificServiceId<1>)`.
• Pattern-matches on `self`:
    – `Aci aci` → extracts the raw UUID via `aci.uuid`,
      obtains the 16-byte representation via `as_bytes`,
      converts the resulting array to a slice, then to a `Vec<u8>`.
    – `Pni _`  → delegates to `service_id_fixed_width_binary(self)`
      to compute the 17-byte fixed-width encoding, converts the
      resulting array to a slice, then to a `Vec<u8>`.

natural language specs:

• The function always succeeds monadically (`ok …`) for every
  `ServiceId` input — it never panics or diverges.
• When `self = Aci aci`, the result Vec contains exactly the
  16 raw UUID bytes of `aci.uuid` — i.e. `result.val = aci.uuid.bytes.val`.
• When `self = Pni pni`, the result Vec is the fixed-width
  encoding whose first byte is `1#u8` (the `Pni` discriminant).
-/

@[step]
theorem service_id_binary_spec
    (self : libsignal_core.address.ServiceId) :
    service_id_binary self ⦃ result =>
      (∀ aci, self = .Aci aci → result.val = aci.uuid.bytes.val) ∧
      (∀ pni, self = .Pni pni → alloc.vec.Vec.index_usize result 0#usize = ok 1#u8) ⦄ := by
  unfold service_id_binary uuid.Uuid.as_bytes
  step*
  constructor
  · intro aci h
    simp_all
  · intro pni h
    simp only [reduceCtorEq] at *
  · simp_all only [reduceCtorEq, Pni.injEq, ok.injEq, Nat.not_eq,
    UScalar.ofNatCore_val_eq, ne_eq, one_ne_zero,
    not_true_eq_false, zero_ne_one, not_lt_zero,
    zero_lt_one, or_self, UScalar.val_not_eq_imp_not_eq, implies_true,
    forall_eq', Array.val_to_slice, IsEmpty.forall_iff, true_and]
    simp only [Array.index_usize, Array.getElem?_Usize_eq,
    UScalar.ofNatCore_val_eq, List.Vector.length_val,
    Nat.ofNat_pos, getElem?_pos, ok.injEq, alloc.vec.Vec.index_usize, alloc.vec.Vec.getElem?_Nat_eq,
    Array.val_to_slice] at *
    exact a_post2

end signal_crypto.libsignal_core.address.ServiceId
