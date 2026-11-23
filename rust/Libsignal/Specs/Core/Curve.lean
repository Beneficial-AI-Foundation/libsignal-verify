/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Libsignal.Proofs.Core.Curve.PublicKey

/-!
# Spec summary: `rust/core/src/curve.rs`

This file freezes the specifications of the items of `rust/core/src/curve.rs`. Each theorem is
restated with `recall` and has a `#guard_msgs` check on the axioms it depends on.

The one theorem covers the serialization of a curve25519 public key.
-/

/-! ## `PublicKey::serialize` -/

open Aeneas Aeneas.Std Result libsignal_core in
recall libsignal_core.curve.PublicKey.serialize_spec (pk : curve.PublicKey) :
    curve.PublicKey.serialize pk ⦃ s =>
      ∀ v, pk.key = .DjbPublicKey v → s.val = 5#u8 :: v.val ⦄

/--
info: 'libsignal_core.curve.PublicKey.serialize_spec' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_core.curve.PublicKey.serialize_spec
