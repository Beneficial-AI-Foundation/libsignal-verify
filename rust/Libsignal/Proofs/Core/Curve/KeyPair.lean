/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Libsignal.Translated.Core.Funs

/-! # Equation for `curve::KeyPair::generate`

Core's `KeyPair::generate` fills a zeroed 32-byte buffer from the generator, clamps it, and builds
the key pair from it with x25519-dalek. `readClampDerive` lists the outside calls of the extracted
body of `generate`, in the order of that body, with nothing else. `generate_eq_readClampDerive`
states that `generate` equals it, for every generator and every state, as an equality of `Result`
values: the same key pair and state, the same fault, or divergence on both sides. Such an equality
compares outcomes, not the number of calls. The equation is proved from the extracted code and
uses no behavioral law for the generator or the dalek calls.

The calls into curve25519-dalek and x25519-dalek stay opaque, so the equation says nothing about
what they return:

* not that `clamp_integer` clamps;
* not that `to_bytes` returns the bytes that `StaticSecret::from` stored;
* not which point `PublicKey::from` computes;
* not that any of them returns.

It says nothing about what `fill_bytes` returns or about its law on any state. Only the
`CryptoRng` view of the generator is read. The extracted function also takes the `rand::Rng` view
and does not use it; Lean has two views of the generator with no stated relation, where Rust has
one generator. If `fill_bytes` returns a slice of a length other than 32, the array that
`Array.from_slice` rebuilds is the zero buffer, as in the extracted code. Rust cannot change the
length of the buffer.

**Source**: rust/core/src/curve.rs, lines 327:4-341:5 (`KeyPair::generate`), and
rust/core/src/curve/curve25519.rs, lines 27:4-38:5 (`PrivateKey::new`), 161:4-163:5
(`PrivateKey::derive_public_key_bytes`) and 165:4-167:5 (`PrivateKey::private_key_bytes`) of the
work copy that Aeneas reads.
-/

open Aeneas Aeneas.Std Result

namespace libsignal_core.curve.KeyPair

/-
natural language description:

• Makes a zeroed 32-byte buffer and fills it with the `fill_bytes` of the generator. Rebuilds the
  array from the slice that `fill_bytes` returns and clamps it with `clamp_integer`. Stores the
  result in a `StaticSecret`, derives the public bytes with `PublicKey::from` and `as_bytes`, and
  reads the private bytes back with `to_bytes`. Returns the key pair of these two byte arrays and
  the state that `fill_bytes` returned.

natural language specs:

• For every generator and every state, `generate` returns the same key pair and state as
  `readClampDerive` when either returns, and faults exactly when `readClampDerive` does.
-/

/-- Read, clamp, derive. Fill a zeroed 32-byte buffer with the `fill_bytes` of the generator's
`CryptoRng` view and rebuild the array from the slice it returns. Clamp the array with
curve25519-dalek's `clamp_integer`, store it in an x25519-dalek `StaticSecret`, derive the
public bytes with `PublicKey::from(&StaticSecret)` and `PublicKey::as_bytes`, and read the
private bytes back with `StaticSecret::to_bytes`. The returned state is the one that `fill_bytes`
returns. If `fill_bytes` returns a slice of another length, the rebuilt array is the zero buffer,
as in the extracted code; Rust cannot change the length of the buffer. -/
noncomputable def readClampDerive {R : Type _} (crng : rand_core_1.CryptoRng R) (r : R) :
    Result (curve.KeyPair × R) := do
  let buf := Array.repeat 32#usize 0#u8
  let (r₁, s) ← crng.RngCoreInst.fill_bytes r (Array.to_slice buf)
  let c ← curve25519_dalek.scalar.clamp_integer (Array.from_slice buf s)
  let sec ← x25519_dalek.x25519.StaticSecret.Insts.CoreConvertFromArrayU832.from c
  let pk ← x25519_dalek.x25519.PublicKey.Insts.CoreConvertFromSharedAStaticSecret.from sec
  let pubBytes ← x25519_dalek.x25519.PublicKey.as_bytes pk
  let privBytes ← x25519_dalek.x25519.StaticSecret.to_bytes sec
  ok ({ public_key := { key := .DjbPublicKey pubBytes },
        private_key := { key := .DjbPrivateKey privBytes } }, r₁)

/-- For every generator and every state, Core's `KeyPair::generate` is `readClampDerive` on the
same state: it returns the same key pair and state when either returns, and it faults exactly when
`readClampDerive` does. The generator's `rand::Rng` view is not used. The equation says nothing
about what the outside calls return. -/
theorem generate_eq_readClampDerive {R : Type _} (rng : rand.rng.Rng R)
    (crng : rand_core_1.CryptoRng R) (r : R) :
    libsignal_core.curve.KeyPair.generate rng crng r = readClampDerive crng r := by
  simp only [libsignal_core.curve.KeyPair.generate, curve.curve25519.PrivateKey.new, lift,
    Array.to_slice_mut, bind_ok, uncurry_apply_pair,
    curve.curve25519.PrivateKey.derive_public_key_bytes,
    curve.PublicKey.Insts.CoreConvertFromPublicKeyData.from,
    curve.curve25519.PrivateKey.private_key_bytes,
    curve.PrivateKey.Insts.CoreConvertFromPrivateKeyData.from, Std.bind_assoc, readClampDerive]
  congr 1
  funext ⟨r1, s1⟩
  simp

end libsignal_core.curve.KeyPair
