/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hoang Le Truong
-/
import Libsignal.Code.Funs

/-! # Spec Theorem for `ServiceId::kind`

Specification and proof for
`libsignal_core.address.ServiceId.kind`,
which returns the `ServiceIdKind` discriminant of a `ServiceId` value.

`ServiceId` is an enum with two variants:
  - `Aci(SpecificServiceId<0>)`  (Account Identity)
  - `Pni(SpecificServiceId<1>)`  (Phone Number Identity)

`ServiceIdKind` is a `#[repr(u8)]` enum with two variants:
  - `Aci = 0`
  - `Pni = 1`

The `kind` method pattern-matches on `self` and returns the
corresponding `ServiceIdKind` variant:
  - `kind(Aci _) = Aci`
  - `kind(Pni _) = Pni`

This is the tag-extraction half of the `ServiceId` representation:
`ServiceId` pairs a `ServiceIdKind` tag with a UUID payload, and
`kind` projects out the tag.  It is used by
`service_id_fixed_width_binary` to write the discriminant byte, and
by other serialization helpers that need to distinguish account
identities from phone-number identities.

The function always succeeds monadically — the match is exhaustive
and every branch immediately returns `ok`.

**Source**: rust/core/src/address.rs, lines 195:4-195:39
-/

open Aeneas Aeneas.Std Result

namespace signal_crypto.libsignal_core.address.ServiceId

/-
natural language description:

• Takes a single `ServiceId` value `self`, which is either
  `Aci(SpecificServiceId<0>)` or `Pni(SpecificServiceId<1>)`.
• Pattern-matches on `self`:
    – `Aci _` → returns `ServiceIdKind::Aci`
    – `Pni _` → returns `ServiceIdKind::Pni`

natural language specs:

• The function always succeeds monadically (`ok …`) for every
  `ServiceId` input — it never panics or diverges.
• When `self = Aci aci`, the result is `ServiceIdKind.Aci`.
• When `self = Pni pni`, the result is `ServiceIdKind.Pni`.
-/

@[step]
theorem kind_spec (self : libsignal_core.address.ServiceId) :
    kind self ⦃ result =>
      (∀ aci, self = .Aci aci → result = .Aci) ∧
      (∀ pni, self = .Pni pni → result = .Pni) ⦄ := by
  unfold kind
  step*

end signal_crypto.libsignal_core.address.ServiceId
