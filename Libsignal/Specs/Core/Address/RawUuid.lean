/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Libsignal.Code.Funs
import Libsignal.Specs.Core.Address.From

/-! # Spec Theorem for `ServiceId::raw_uuid`

Specification and proof for
`libsignal_core.address.ServiceId.raw_uuid`,
which returns the UUID inside a `ServiceId` value, discarding the
variant tag (kind).

`ServiceId` is an enum with two variants:
  - `Aci(SpecificServiceId<0>)`  (Account Identity)
  - `Pni(SpecificServiceId<1>)`  (Phone Number Identity)

Each variant wraps a `SpecificServiceId<KIND>`, which is a newtype
around a `uuid.Uuid`.  The `raw_uuid` method pattern-matches on
`self` and converts the inner `SpecificServiceId` into its `Uuid`
via the `Into<Uuid>` trait (which simply projects the `.uuid` field):
  - `raw_uuid(Aci aci) = aci.uuid`
  - `raw_uuid(Pni pni) = pni.uuid`

This is the payload-extraction half of the `ServiceId` representation:
`ServiceId` pairs a `ServiceIdKind` tag with a UUID payload, and
`raw_uuid` projects out the payload.  It is the dual of `kind`, which
projects out the tag.

The function is used by `service_id_fixed_width_binary` to obtain the
16 raw UUID bytes for serialization, and by other helpers that need
access to the underlying UUID regardless of the identity type.

The function always succeeds monadically — the match is exhaustive
and every branch immediately delegates to the total `Into<Uuid>`
conversion.

**Source**: rust/core/src/address.rs, lines 288:4-288:33
(`pub fn raw_uuid(self) -> Uuid { match self { … } }`)
-/

open Aeneas Aeneas.Std Result

namespace signal_crypto.libsignal_core.address.ServiceId

/-
natural language description:

• Takes a single `ServiceId` value `self`, which is either
  `Aci(SpecificServiceId<0>)` or `Pni(SpecificServiceId<1>)`.
• Pattern-matches on `self`:
    – `Aci aci` → converts `aci` into `Uuid` via `Into<Uuid>`,
      which returns `aci.uuid`
    – `Pni pni` → converts `pni` into `Uuid` via `Into<Uuid>`,
      which returns `pni.uuid`

natural language specs:

• The function always succeeds monadically (`ok …`) for every
  `ServiceId` input — it never panics or diverges.
• When `self = Aci aci`, the result is `aci.uuid`.
• When `self = Pni pni`, the result is `pni.uuid`.
-/

@[step]
theorem raw_uuid_spec (self : libsignal_core.address.ServiceId) :
    raw_uuid self ⦃ result =>
      (∀ aci, self = .Aci aci → result = aci.uuid) ∧
      (∀ pni, self = .Pni pni → result = pni.uuid) ⦄ := by
  unfold raw_uuid
  step* <;> (unfold uuid.Uuid.Insts.CoreConvertFromSpecificServiceId.from; step*; simp_all)

end signal_crypto.libsignal_core.address.ServiceId
