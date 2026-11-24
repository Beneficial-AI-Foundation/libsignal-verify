/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Libsignal.Proofs.Core.Curve.KeyPair
import Libsignal.Proofs.Core.Curve.PrivateKey
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

/-! ## `PrivateKey::public_key` -/

open Aeneas Aeneas.Std Result libsignal_core in
recall libsignal_core.curve.PrivateKey.public_key_djb_eq (b : Array U8 32#usize) :
    libsignal_core.curve.PrivateKey.public_key { key := .DjbPrivateKey b } = (do
      let c ← curve25519_dalek.scalar.clamp_integer b
      let sec ← x25519_dalek.x25519.StaticSecret.Insts.CoreConvertFromArrayU832.from c
      let pk ← x25519_dalek.x25519.PublicKey.Insts.CoreConvertFromSharedAStaticSecret.from sec
      let a ← x25519_dalek.x25519.PublicKey.as_bytes pk
      ok (.Ok { key := .DjbPublicKey a }))

/--
info: 'libsignal_core.curve.PrivateKey.public_key_djb_eq' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 curve25519_dalek.scalar.clamp_integer,
 x25519_dalek.x25519.PublicKey,
 x25519_dalek.x25519.StaticSecret,
 x25519_dalek.x25519.PublicKey.as_bytes,
 x25519_dalek.x25519.PublicKey.Insts.CoreConvertFromSharedAStaticSecret.from,
 x25519_dalek.x25519.StaticSecret.Insts.CoreConvertFromArrayU832.from]
-/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_core.curve.PrivateKey.public_key_djb_eq

/-! ## `KeyPair::generate` -/

open Aeneas Aeneas.Std Result libsignal_core in
recall libsignal_core.curve.KeyPair.readClampDerive {R : Type _} (crng : rand_core_1.CryptoRng R)
    (r : R) : Result (curve.KeyPair × R) := do
  let buf := Array.repeat 32#usize 0#u8
  let (r₁, s) ← crng.RngCoreInst.fill_bytes r (Array.to_slice buf)
  let c ← curve25519_dalek.scalar.clamp_integer (Array.from_slice buf s)
  let sec ← x25519_dalek.x25519.StaticSecret.Insts.CoreConvertFromArrayU832.from c
  let pk ← x25519_dalek.x25519.PublicKey.Insts.CoreConvertFromSharedAStaticSecret.from sec
  let pubBytes ← x25519_dalek.x25519.PublicKey.as_bytes pk
  let privBytes ← x25519_dalek.x25519.StaticSecret.to_bytes sec
  ok ({ public_key := { key := .DjbPublicKey pubBytes },
        private_key := { key := .DjbPrivateKey privBytes } }, r₁)

/--
info: 'libsignal_core.curve.KeyPair.readClampDerive' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 curve25519_dalek.scalar.clamp_integer,
 x25519_dalek.x25519.PublicKey,
 x25519_dalek.x25519.StaticSecret,
 x25519_dalek.x25519.PublicKey.as_bytes,
 x25519_dalek.x25519.StaticSecret.to_bytes,
 x25519_dalek.x25519.PublicKey.Insts.CoreConvertFromSharedAStaticSecret.from,
 x25519_dalek.x25519.StaticSecret.Insts.CoreConvertFromArrayU832.from]
-/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_core.curve.KeyPair.readClampDerive

open Aeneas Aeneas.Std Result libsignal_core in
recall libsignal_core.curve.KeyPair.generate_eq_readClampDerive {R : Type _}
    (rng : rand.rng.Rng R) (crng : rand_core_1.CryptoRng R) (r : R) :
    libsignal_core.curve.KeyPair.generate rng crng r =
      libsignal_core.curve.KeyPair.readClampDerive crng r

/--
info: 'libsignal_core.curve.KeyPair.generate_eq_readClampDerive' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound,
 curve25519_dalek.scalar.clamp_integer,
 x25519_dalek.x25519.PublicKey,
 x25519_dalek.x25519.StaticSecret,
 x25519_dalek.x25519.PublicKey.as_bytes,
 x25519_dalek.x25519.StaticSecret.to_bytes,
 x25519_dalek.x25519.PublicKey.Insts.CoreConvertFromSharedAStaticSecret.from,
 x25519_dalek.x25519.StaticSecret.Insts.CoreConvertFromArrayU832.from]
-/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_core.curve.KeyPair.generate_eq_readClampDerive
