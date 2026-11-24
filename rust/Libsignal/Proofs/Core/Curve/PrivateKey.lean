/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Libsignal.Translated.Core.Funs

/-! # Equation for `curve::PrivateKey::public_key`

Core's `PrivateKey::public_key` on a Djb key clamps the 32 bytes of the key, stores the result in
an x25519-dalek `StaticSecret`, derives the public bytes from it, and returns them as `Ok`.
`public_key_djb_eq` states this as an equality of `Result` values. The function has no `Err`
branch. The equation is proved from the extracted code and uses no behavioral law for the dalek
calls.

The calls into curve25519-dalek and x25519-dalek stay opaque, so the equation says nothing about
what they return: not that `clamp_integer` clamps, not which point `PublicKey::from` computes, and
not that any of them returns.

**Source**: rust/core/src/curve.rs, lines 259:4-267:5 (`PrivateKey::public_key`), and
rust/core/src/curve/curve25519.rs, lines 161:4-163:5 (`PrivateKey::derive_public_key_bytes`) and
171:4-174:5 (`PrivateKey::from`) of the work copy that Aeneas reads.
-/

open Aeneas Aeneas.Std Result

namespace libsignal_core.curve.PrivateKey

/-
natural language description:

• Reads the 32 bytes of the Djb key and clamps them with `clamp_integer`. Stores the result in a
  `StaticSecret`, derives the public bytes with `PublicKey::from` and `as_bytes`, wraps them as a
  Djb public key, and returns it as `Ok`.

natural language specs:

• For a Djb key with the bytes `b`, the call equals the sequence of these outside calls on `b`,
  ending in `Ok` of the Djb public key with the derived bytes. It never returns `Err`.
-/

/-- `PrivateKey::public_key` on a Djb key with the bytes `b` clamps `b`, stores it in a
`StaticSecret`, derives the public bytes and returns them as `Ok`. It never returns `Err`. -/
theorem public_key_djb_eq (b : Array U8 32#usize) :
    libsignal_core.curve.PrivateKey.public_key { key := .DjbPrivateKey b } = (do
      let c ← curve25519_dalek.scalar.clamp_integer b
      let sec ← x25519_dalek.x25519.StaticSecret.Insts.CoreConvertFromArrayU832.from c
      let pk ← x25519_dalek.x25519.PublicKey.Insts.CoreConvertFromSharedAStaticSecret.from sec
      let a ← x25519_dalek.x25519.PublicKey.as_bytes pk
      ok (.Ok { key := .DjbPublicKey a })) := by
  simp [libsignal_core.curve.PrivateKey.public_key,
    curve.curve25519.PrivateKey.Insts.CoreConvertFromArrayU832.from,
    curve.curve25519.PrivateKey.derive_public_key_bytes, curve.PublicKey.new]

end libsignal_core.curve.PrivateKey
