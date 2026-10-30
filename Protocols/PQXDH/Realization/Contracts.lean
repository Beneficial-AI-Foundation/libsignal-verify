/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Alessandro D'Angelo
-/
import Libsignal.Spec.Protocol.Crypto.HkdfSha256
import Libsignal.Translated.Protocol.Funs
import Protocols.PQXDH.Realization.Defs

/-!
# Contracts for the opaque leaves of the PQXDH entry points

The extraction leaves the cryptographic primitives that `pqxdh_initiate` and `pqxdh_accept` call
opaque: curve25519 agreement and signatures, the Kyber1024 backend, the random-number generator
and a few conversions of the Rust standard library are `axiom` declarations in the hand-maintained
external files, so Lean knows only their types. A **contract** states what such a leaf does: its
success and error behaviour on an explicit domain, and that it terminates without panicking there.
Every contract here is a proposition, used as a named hypothesis of the theorems that need it,
never an `axiom` and never a `sorry`. Nothing is inferred from the type of a leaf: a `Result`
type allows a panic and a loop, and a contract excludes them only where it says so.

Each contract cites the Rust code it describes. The source was read, not verified: the contracts
are trusted, each has its own row on the ledger, and the plan is to discharge the curve contracts
from the verified curve25519 implementation and the Kyber contracts from a model of libcrux.

The contracts fall into four groups.

* **Curve25519** (`rust/core/src/curve.rs`, `rust/core/src/curve/curve25519.rs`). Agreement
  between two keys whose public halves were derived from their private halves succeeds with 32
  bytes and gives the same value from either side (`AgreementDerived`). This replaces an
  assumption that agreement commutes on all key pairs, which is false of production on low-order
  points. On arbitrary inputs, agreement returns either 32 bytes or the error
  `InvalidKeyAgreement` (`AgreementTotal`). The torsion check always returns a Boolean
  (`TorsionFreeTotal`), and a derived public key passes the canonicality check that
  `pqxdh_accept` applies to the initiator's ephemeral key (`DerivedCanonical`).
* **Signatures** on the same curve25519 keys (XEdDSA). Signing terminates with a 64-byte
  signature when the random-number generator is total (`SignTotal`), a signature verifies under
  the derived public key (`SignVerify`), and verification always returns a Boolean
  (`VerifyTotal`).
* **Kyber1024** (`rust/protocol/src/kem/kyber1024.rs`). Encapsulation on a key whose length is not
  1568 bytes returns `BadKEMKeyLength` and leaves the generator state unchanged
  (`KyberEncapsBadLength`); on a 1568-byte key, when the generator is total, it terminates with a
  32-byte secret and a 1568-byte ciphertext (`KyberEncapsBackend`). Decapsulation has three exact
  branches (`KyberDecaps`).
* **Randomness and the standard library.** `RngTotal core Dom` says that the generator's methods
  terminate without panicking on the states in `Dom` and stay in `Dom`; it is the named
  RNG-totality hypothesis, because a `CryptoRng` adapter may panic (`rand_core` 0.9.3,
  `UnwrapErr`, `src/lib.rs:300-317`). The remaining contracts describe a vector turned into a
  boxed slice, a boxed slice copied from a slice, slice equality and string allocation.

`CoreContracts` and `SignatureContracts` bundle the contracts as named fields.

## Fault-or-value contracts

The contracts above are total: each says that a leaf returns, and what it returns. The security
statements count every faulted run in a separate term (`Pr[⊥]`), so they do not need totality,
and they must not depend on the list of totality contracts being complete. They use instead the
**fault-or-value** form of each contract, bundled in `PartialContracts`: *if* the leaf returns,
it returns the value described above. A fault-or-value contract says nothing about termination;
each one follows from the corresponding total contract.
-/

open Aeneas Aeneas.Std Result
open libsignal_protocol

namespace Protocols.PQXDH.Realization

section Rng

variable {R : Type}

/-- **RNG totality.** On every state in `Dom`, the three methods of the random-number generator
terminate without panicking and return a state in `Dom`; `fill_bytes` keeps the length of the
buffer. This is the hypothesis that the generator instance chosen by the caller is total, which
the type `rand_core::CryptoRng` does not guarantee. -/
def RngTotal (core : rand_core_1.RngCore R) (Dom : R → Prop) : Prop :=
  ∀ r, Dom r →
    (core.next_u32 r ⦃ _ r' => Dom r' ⦄) ∧ (core.next_u64 r ⦃ _ r' => Dom r' ⦄) ∧
      ∀ buf, core.fill_bytes r buf ⦃ r' buf' => buf'.length = buf.length ∧ Dom r' ⦄

end Rng

section Curve

/-- **Agreement on derived keys.** If the public keys `pk₁` and `pk₂` are those derived from the
private keys `sk₁` and `sk₂`, then agreement of `sk₁` with `pk₂` and of `sk₂` with `pk₁` both
succeed with the same 32 bytes.

Source: `PrivateKey::calculate_agreement` (`rust/core/src/curve.rs:296-309`) clamps its scalar
(`rust/core/src/curve/curve25519.rs:170-174`) and computes X25519, and `PrivateKey::public_key`
(`rust/core/src/curve.rs:259-267`) multiplies the clamped scalar into the base point. Both values
are therefore the u-coordinate of the product of the two clamped scalars with the base point. A
clamped scalar is a nonzero multiple of 8 below the group order, so the product is not the
identity and its u-coordinate is not zero: the all-zero rejection never triggers. -/
def AgreementDerived : Prop :=
  ∀ (sk₁ sk₂ : ECPriv) (pk₁ pk₂ : ECPub),
    curve.PrivateKey.public_key sk₁ = .ok (.Ok pk₁) →
      curve.PrivateKey.public_key sk₂ = .ok (.Ok pk₂) →
        ∃ s : Slice U8, s.length = 32 ∧
          curve.PrivateKey.calculate_agreement sk₁ pk₂ = .ok (.Ok s) ∧
          curve.PrivateKey.calculate_agreement sk₂ pk₁ = .ok (.Ok s)

/-- **Agreement terminates.** On every private and public key, agreement terminates without
panicking and returns either 32 bytes or the error `InvalidKeyAgreement`, which it returns for
the all-zero shared value (`rust/core/src/curve.rs:296-309`). -/
def AgreementTotal : Prop :=
  ∀ (sk : ECPriv) (pk : ECPub),
    curve.PrivateKey.calculate_agreement sk pk ⦃ r =>
      (∃ s, r = .Ok s ∧ s.length = 32) ∨ r = .Err .InvalidKeyAgreement ⦄

/-- **The torsion check terminates.** On every public key, `is_torsion_free` returns a Boolean
(`rust/core/src/curve.rs:165-174`). -/
def TorsionFreeTotal : Prop :=
  ∀ pk : ECPub, ∃ b, curve.PublicKey.is_torsion_free pk = .ok b

/-- **Derived public keys are canonical.** A public key derived from a private key passes the
check `is_canonical` that `pqxdh_accept` applies to the initiator's ephemeral key
(`rust/protocol/src/pqxdh.rs:339`): it is torsion-free and its encoding is reduced
(`rust/core/src/curve.rs:165-190`). A derived key is a multiple of the base point, which lies in
the prime-order subgroup, and its u-coordinate is encoded below `2^255 - 19`. -/
def DerivedCanonical : Prop :=
  ∀ (sk : ECPriv) (pk : ECPub), curve.PrivateKey.public_key sk = .ok (.Ok pk) →
    libsignal_core.curve.PublicKey.is_canonical pk = .ok true

end Curve

section Signature

/-- **Signing terminates.** When both views of the generator are total on `Dom` and the state is
in `Dom`, signing returns a 64-byte signature and a state in `Dom`. The signature first draws 64
random bytes (`rust/core/src/curve/curve25519.rs:66-75`); otherwise its `Result` is always
`Ok` (`rust/core/src/curve.rs:283-294`). -/
def SignTotal : Prop :=
  ∀ {R : Type} (crng : rand_core_1.CryptoRng R) (rng : rand.rng.Rng R) (Dom : R → Prop),
    RngTotal crng.RngCoreInst Dom → RngTotal rng.rand_core_1RngCoreInst Dom →
      ∀ (sk : ECPriv) (msg : Slice U8) (r : R), Dom r →
        curve.PrivateKey.calculate_signature crng rng sk msg r ⦃ res r' =>
          (∃ σ, res = .Ok σ ∧ σ.length = 64) ∧ Dom r' ⦄

/-- **Signature completeness on derived keys.** A signature that the private key `sk` computes
on `msg` verifies under the public key derived from `sk` (XEdDSA,
`rust/core/src/curve/curve25519.rs:66-158`). One key both signs and agrees: this is the
completeness half of the single identity key. -/
def SignVerify : Prop :=
  ∀ {R : Type} (crng : rand_core_1.CryptoRng R) (rng : rand.rng.Rng R) (sk : ECPriv)
    (pk : ECPub) (msg σ : Slice U8) (r r' : R),
    curve.PrivateKey.public_key sk = .ok (.Ok pk) →
      curve.PrivateKey.calculate_signature crng rng sk msg r = .ok (.Ok σ, r') →
        libsignal_core.curve.PublicKey.verify_signature pk msg σ = .ok true

/-- **Verification terminates.** On every public key, message and signature, verification
returns a Boolean: a malformed signature or key is rejected with `false`
(`rust/core/src/curve.rs:138-151`; `rust/core/src/curve/curve25519.rs:119-139`). -/
def VerifyTotal : Prop :=
  ∀ (pk : ECPub) (parts : Slice (Slice U8)) (σ : Slice U8),
    ∃ b, curve.PublicKey.verify_signature_for_multipart_message pk parts σ = .ok b

end Signature

section Kyber

/-- **Encapsulation rejects a wrong length first.** On a key whose length is not 1568 bytes,
encapsulation returns `BadKEMKeyLength` and leaves the generator state unchanged: the length is
checked before any randomness is drawn (`rust/protocol/src/kem/kyber1024.rs:31-40`). -/
def KyberEncapsBadLength : Prop :=
  ∀ {R : Type} (crng : rand_core_1.CryptoRng R) (key : kem.KeyMaterial kem.Public) (r : R),
    key.data.length ≠ 1568 →
      kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate crng key r =
        .ok (.Err (), r)

/-- **Backend contract for encapsulation.** When the generator is total on `Dom` and the state
is in `Dom`, encapsulation on a 1568-byte key terminates without panicking, with a 32-byte shared
secret, a 1568-byte ciphertext and a state in `Dom`. libcrux 0.0.10 converts the key by length
only (`libcrux-ml-kem-0.0.10/src/types.rs:45-54`) and validates nothing else; its rejection
sampling loop has no proved bound (`src/sampling.rs:74`, `:95-102`), so termination is part of the
trusted content. -/
def KyberEncapsBackend : Prop :=
  ∀ {R : Type} (crng : rand_core_1.CryptoRng R) (Dom : R → Prop), RngTotal crng.RngCoreInst Dom →
    ∀ (key : kem.KeyMaterial kem.Public) (r : R), key.data.length = 1568 → Dom r →
      kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate crng key r
        ⦃ res r' => (∃ ss ct, res = .Ok (ss, ct) ∧ ss.length = 32 ∧ ct.length = 1568) ∧ Dom r' ⦄

/-- **Decapsulation.** On every secret key and ciphertext, decapsulation terminates without
panicking and returns: `BadKeyLength` if the secret key does not have 3168 bytes; otherwise
`BadCiphertext` if the ciphertext does not have 1568 bytes; otherwise a 32-byte shared secret
(`rust/protocol/src/kem/kyber1024.rs:42-54`). On a mismatched ciphertext Kyber returns a
pseudorandom secret rather than an error, so success says nothing about agreement; that is what
`KyberDeltaCorrect` measures. Termination rests on the same unbounded sampling loop as
encapsulation. -/
def KyberDecaps : Prop :=
  ∀ (sk : kem.KeyMaterial kem.Secret) (ct : Slice U8),
    kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate sk ct ⦃ res =>
      (sk.data.length ≠ 3168 → res = .Err .BadKeyLength) ∧
      (sk.data.length = 3168 → ct.length ≠ 1568 → res = .Err .BadCiphertext) ∧
      (sk.data.length = 3168 → ct.length = 1568 → ∃ ss, res = .Ok ss ∧ ss.length = 32) ⦄

end Kyber

section Std

/-- `Vec::into_boxed_slice` keeps the elements of the vector. -/
def VecIntoBoxedSlice : Prop :=
  ∀ {T : Type} (A : Type) (v : alloc.vec.Vec T),
    _root_.alloc.vec.Vec.into_boxed_slice A v = .ok (alloc.vec.Vec.deref v)

/-- `Box::<[u8]>::from(&[u8])` copies the bytes of the slice. -/
def BoxSliceFromU8 : Prop :=
  ∀ s : Slice U8, BoxSlice.Insts.CoreConvertFromShared0Slice.from core.clone.CloneU8 s = .ok s

/-- Comparing a byte slice with a byte array returns whether they have the same bytes. -/
def SliceEqArrayU8 : Prop :=
  ∀ {N : Usize} (s : Slice U8) (a : Array U8 N),
    Slice.Insts.CoreCmpPartialEqArray.eq core.cmp.PartialEqU8 s a = .ok (decide (s.val = a.val))

/-- Allocating an owned string from a string literal terminates. `pqxdh_accept` does this only
to build the message of its error for a non-canonical ephemeral key (`rust/protocol/src/pqxdh.rs:
339-344`). -/
def ToOwnedTotal : Prop :=
  ∀ s : Str, ∃ t, Str.Insts.AllocBorrowToOwnedString.to_owned s = .ok t

end Std

/-- The contracts on the opaque leaves that the two entry points and the KEM experiment call:
curve25519 agreement and checks, the Kyber1024 backend and the standard-library conversions. -/
structure CoreContracts : Prop where
  /-- Agreement on derived keys; see `AgreementDerived`. -/
  agreementDerived : AgreementDerived
  /-- Agreement terminates on every input; see `AgreementTotal`. -/
  agreementTotal : AgreementTotal
  /-- The torsion check terminates; see `TorsionFreeTotal`. -/
  torsionFreeTotal : TorsionFreeTotal
  /-- Derived public keys are canonical; see `DerivedCanonical`. -/
  derivedCanonical : DerivedCanonical
  /-- Encapsulation rejects a wrong key length; see `KyberEncapsBadLength`. -/
  kyberEncapsBadLength : KyberEncapsBadLength
  /-- The encapsulation backend contract; see `KyberEncapsBackend`. -/
  kyberEncapsBackend : KyberEncapsBackend
  /-- Decapsulation; see `KyberDecaps`. -/
  kyberDecaps : KyberDecaps
  /-- See `VecIntoBoxedSlice`. -/
  vecIntoBoxedSlice : VecIntoBoxedSlice
  /-- See `BoxSliceFromU8`. -/
  boxSliceFromU8 : BoxSliceFromU8
  /-- See `SliceEqArrayU8`. -/
  sliceEqArrayU8 : SliceEqArrayU8
  /-- See `ToOwnedTotal`. -/
  toOwnedTotal : ToOwnedTotal

/-- The contracts on the opaque signature leaves that the synthetic wrapper calls. -/
structure SignatureContracts : Prop where
  /-- Signing terminates; see `SignTotal`. -/
  signTotal : SignTotal
  /-- Completeness on derived keys; see `SignVerify`. -/
  signVerify : SignVerify
  /-- Verification terminates; see `VerifyTotal`. -/
  verifyTotal : VerifyTotal

section Partial

/-- **Agreement, fault or value.** When agreement returns, it returns 32 bytes or
`InvalidKeyAgreement`; and when both agreements between two keys with derived public halves
return, they return the same 32 bytes. -/
def AgreementPartial : Prop :=
  (∀ (sk : ECPriv) (pk : ECPub) r, curve.PrivateKey.calculate_agreement sk pk = .ok r →
    (∃ s, r = .Ok s ∧ s.length = 32) ∨ r = .Err .InvalidKeyAgreement) ∧
  ∀ (sk₁ sk₂ : ECPriv) (pk₁ pk₂ : ECPub) r₁ r₂,
    curve.PrivateKey.public_key sk₁ = .ok (.Ok pk₁) →
      curve.PrivateKey.public_key sk₂ = .ok (.Ok pk₂) →
        curve.PrivateKey.calculate_agreement sk₁ pk₂ = .ok r₁ →
          curve.PrivateKey.calculate_agreement sk₂ pk₁ = .ok r₂ →
            r₁ = r₂ ∧ ∃ s, r₁ = .Ok s ∧ s.length = 32

/-- **Canonicality of derived keys, fault or value.** When the canonicality check returns on a
derived public key, it returns `true`. -/
def DerivedCanonicalPartial : Prop :=
  ∀ (sk : ECPriv) (pk : ECPub) b, curve.PrivateKey.public_key sk = .ok (.Ok pk) →
    libsignal_core.curve.PublicKey.is_canonical pk = .ok b → b = true

/-- **Signatures, fault or value.** When signing returns, it returns a 64-byte signature; and when
verification of a signature by the private key `sk` returns under the public key derived from
`sk`, it returns `true`. -/
def SignaturePartial : Prop :=
  (∀ {R : Type} (crng : rand_core_1.CryptoRng R) (rng : rand.rng.Rng R) (sk : ECPriv)
    (msg : Slice U8) (r r' : R) res,
    curve.PrivateKey.calculate_signature crng rng sk msg r = .ok (res, r') →
      ∃ σ, res = .Ok σ ∧ σ.length = 64) ∧
  ∀ {R : Type} (crng : rand_core_1.CryptoRng R) (rng : rand.rng.Rng R) (sk : ECPriv)
    (pk : ECPub) (msg σ : Slice U8) (r r' : R) b,
    curve.PrivateKey.public_key sk = .ok (.Ok pk) →
      curve.PrivateKey.calculate_signature crng rng sk msg r = .ok (.Ok σ, r') →
        libsignal_core.curve.PublicKey.verify_signature pk msg σ = .ok b → b = true

/-- **Kyber, fault or value.** When encapsulation returns on a key that does not have 1568 bytes,
it returns `BadKEMKeyLength` and the unchanged state; when it returns on a 1568-byte key, it
returns a 32-byte secret and a 1568-byte ciphertext; and when decapsulation returns, it follows
the three branches of `KyberDecaps`. -/
def KyberPartial : Prop :=
  (∀ {R : Type} (crng : rand_core_1.CryptoRng R) (key : kem.KeyMaterial kem.Public) (r r' : R)
    res, kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate crng key r =
      .ok (res, r') →
    (key.data.length ≠ 1568 → res = .Err () ∧ r' = r) ∧
    (key.data.length = 1568 → ∃ ss ct, res = .Ok (ss, ct) ∧ ss.length = 32 ∧ ct.length = 1568)) ∧
  ∀ (sk : kem.KeyMaterial kem.Secret) (ct : Slice U8) res,
    kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate sk ct = .ok res →
      (sk.data.length ≠ 3168 → res = .Err .BadKeyLength) ∧
      (sk.data.length = 3168 → ct.length ≠ 1568 → res = .Err .BadCiphertext) ∧
      (sk.data.length = 3168 → ct.length = 1568 → ∃ ss, res = .Ok ss ∧ ss.length = 32)

/-- **Standard-library conversions, fault or value.** When they return, `Vec::into_boxed_slice`
keeps the elements, `Box::<[u8]>::from` copies the bytes, and slice equality returns whether the
bytes are equal. -/
def StdPartial : Prop :=
  (∀ {T : Type} (A : Type) (v : alloc.vec.Vec T) s,
    _root_.alloc.vec.Vec.into_boxed_slice A v = .ok s → s = alloc.vec.Vec.deref v) ∧
  (∀ (s t : Slice U8),
    BoxSlice.Insts.CoreConvertFromShared0Slice.from core.clone.CloneU8 s = .ok t → t = s) ∧
  ∀ {N : Usize} (s : Slice U8) (a : Array U8 N) b,
    Slice.Insts.CoreCmpPartialEqArray.eq core.cmp.PartialEqU8 s a = .ok b →
      b = decide (s.val = a.val)

/-- **HKDF, fault or value.** When the helper returns on a 96-byte buffer and no salt, it returns
`Ok(())` and the RFC 5869 output computed from the MAC interface `H`. This is the fault-or-value
form of `HkdfSha256Contract H`. -/
def HkdfSha256Partial (H : crypto.HmacSha256) : Prop :=
  ∀ (ikm info out : Slice U8) r out', out.length = 96 →
    crypto.hkdf_sha256 none ikm info out = .ok (r, out') →
      r = .Ok () ∧ out'.length = out.length ∧
        out'.val = crypto.hkdfSha256Okm96 H none ikm.val info.val

end Partial

/-- The fault-or-value contracts on every opaque leaf that the Full realization calls, for the
MAC interface `H`. They are the premises of the security statements, which count faults
separately. -/
structure PartialContracts (H : crypto.HmacSha256) : Prop where
  /-- See `AgreementPartial`. -/
  agreement : AgreementPartial
  /-- See `DerivedCanonicalPartial`. -/
  derivedCanonical : DerivedCanonicalPartial
  /-- See `SignaturePartial`. -/
  signature : SignaturePartial
  /-- See `KyberPartial`. -/
  kyber : KyberPartial
  /-- See `StdPartial`. -/
  std : StdPartial
  /-- See `HkdfSha256Partial`. -/
  hkdf : HkdfSha256Partial H

end Protocols.PQXDH.Realization
