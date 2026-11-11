/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin, Alessandro D'Angelo
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import Libsignal.Proofs.Protocol.Crypto.HkdfSha256
import Libsignal.Translated.Protocol.Funs
import Protocols.PQXDH.Defs

/-!
# Contracts for the opaque leaves of the PQXDH entry points

The extraction leaves opaque the primitives that `pqxdh_initiate` and `pqxdh_accept` call:
curve25519 agreement and signatures, the Kyber1024 backend, the random-number generator and the
allocation of a string. The hand-maintained external files declare them without a body, so Lean
knows only their types.

A contract states what such a leaf does on an explicit domain: which values or errors it returns,
and that it terminates without panicking. Each contract is a proposition that a theorem takes as a
named hypothesis. A `Result` type allows a panic and a loop, and a contract excludes them only
where it says so. Each contract cites the Rust code it describes. We read that code but did not
verify it, so every contract is trusted and has its own row in `Protocols/LEDGER.md`.

Each contract comes in two forms. The total form says that a leaf returns, and what it returns.
`CoreContracts` and `SignatureContracts` bundle the total forms, which the correctness statements
and `fullExp_noLostMass` take. The fault-or-value form says only what a leaf returns if it
returns, and it follows from the total form. `PartialContracts` bundles the fault-or-value forms.
The security statements take these, because they count every faulted run in the term `Pr[⊥]`.
-/

open Aeneas Aeneas.Std Result
open libsignal_protocol

namespace Protocols.PQXDH

section Rng

variable {R : Type}

/-- On every state in `Dom`, the three methods of the random-number generator terminate without
panicking and return a state in `Dom`, and `fill_bytes` keeps the length of the buffer. This is
the hypothesis that the caller's generator instance is total. The type `rand_core::CryptoRng` does
not guarantee it, because a `CryptoRng` adapter can panic (`rand_core` 0.9.3, `UnwrapErr`,
`src/lib.rs:300-317`). -/
def RngTotal (core : rand_core_1.RngCore R) (Dom : R → Prop) : Prop :=
  ∀ r, Dom r →
    (core.next_u32 r ⦃ _ r' => Dom r' ⦄) ∧ (core.next_u64 r ⦃ _ r' => Dom r' ⦄) ∧
      ∀ buf, core.fill_bytes r buf ⦃ r' buf' => buf'.length = buf.length ∧ Dom r' ⦄

end Rng

section Curve

/-- If the public keys `pk₁` and `pk₂` are those derived from the private keys `sk₁` and `sk₂`,
then agreement of `sk₁` with `pk₂` and of `sk₂` with `pk₁` both succeed with the same 32 bytes.

`PrivateKey::calculate_agreement` (`rust/core/src/curve.rs:296-309`) clamps its scalar
(`rust/core/src/curve/curve25519.rs:170-174`) and computes X25519, and `PrivateKey::public_key`
(`rust/core/src/curve.rs:259-267`) multiplies the clamped scalar into the base point. Both values
are therefore the u-coordinate of the product of the two clamped scalars with the base point. A
clamped scalar is a multiple of 8 in `[2^254, 2^255)`. It is not divisible by the prime group
order `ℓ ≈ 2^252`: a multiple `kℓ` in that range has `k < 8`, while `8 ∣ kℓ` with `ℓ` odd forces
`8 ∣ k`. So both clamped scalars are nonzero modulo `ℓ`, the product point is not the identity,
and its u-coordinate is not zero: the all-zero rejection never triggers. -/
def AgreementDerived : Prop :=
  ∀ (sk₁ sk₂ : ECPriv) (pk₁ pk₂ : ECPub),
    curve.PrivateKey.public_key sk₁ = .ok (.Ok pk₁) →
      curve.PrivateKey.public_key sk₂ = .ok (.Ok pk₂) →
        ∃ s : Slice U8, s.length = 32 ∧
          curve.PrivateKey.calculate_agreement sk₁ pk₂ = .ok (.Ok s) ∧
          curve.PrivateKey.calculate_agreement sk₂ pk₁ = .ok (.Ok s)

/-- On every private and public key, agreement terminates without panicking and returns either
32 bytes or the error `InvalidKeyAgreement`, which it returns for the all-zero shared value
(`rust/core/src/curve.rs:296-309`). -/
def AgreementTotal : Prop :=
  ∀ (sk : ECPriv) (pk : ECPub),
    curve.PrivateKey.calculate_agreement sk pk ⦃ r =>
      (∃ s, r = .Ok s ∧ s.length = 32) ∨ r = .Err .InvalidKeyAgreement ⦄

/-- On every public key, the torsion check `is_torsion_free` returns a Boolean
(`rust/core/src/curve.rs:165-174`). -/
def TorsionFreeTotal : Prop :=
  ∀ pk : ECPub, ∃ b, curve.PublicKey.is_torsion_free pk = .ok b

/-- A public key derived from a private key passes the check `is_canonical` that `pqxdh_accept`
applies to the initiator's ephemeral key (`rust/protocol/src/pqxdh.rs:339`): it is torsion-free
and its encoding is reduced (`rust/core/src/curve.rs:165-190`). A derived key is a multiple of
the base point, which lies in the prime-order subgroup, and its u-coordinate is encoded below
`2^255 - 19`. -/
def DerivedCanonical : Prop :=
  ∀ (sk : ECPriv) (pk : ECPub), curve.PrivateKey.public_key sk = .ok (.Ok pk) →
    libsignal_core.curve.PublicKey.is_canonical pk = .ok true

end Curve

section Signature

/-- When both views of the generator are total on `Dom` and the state is in `Dom`, signing
returns a 64-byte signature and a state in `Dom`. Signing first draws 64 random bytes
(`rust/core/src/curve/curve25519.rs:66-75`). Apart from that draw, its `Result` is always `Ok`
(`rust/core/src/curve.rs:283-294`). -/
def SignTotal : Prop :=
  ∀ {R : Type} (crng : rand_core_1.CryptoRng R) (rng : rand.rng.Rng R) (Dom : R → Prop),
    RngTotal crng.RngCoreInst Dom → RngTotal rng.rand_core_1RngCoreInst Dom →
      ∀ (sk : ECPriv) (msg : Slice U8) (r : R), Dom r →
        curve.PrivateKey.calculate_signature crng rng sk msg r ⦃ res r' =>
          (∃ σ, res = .Ok σ ∧ σ.length = 64) ∧ Dom r' ⦄

/-- A signature that the private key `sk` computes on `msg` verifies under the public key derived
from `sk` (XEdDSA, `rust/core/src/curve/curve25519.rs:66-158`). This is signature completeness
for the identity key used for both signing and agreement. -/
def SignVerify : Prop :=
  ∀ {R : Type} (crng : rand_core_1.CryptoRng R) (rng : rand.rng.Rng R) (sk : ECPriv)
    (pk : ECPub) (msg σ : Slice U8) (r r' : R),
    curve.PrivateKey.public_key sk = .ok (.Ok pk) →
      curve.PrivateKey.calculate_signature crng rng sk msg r = .ok (.Ok σ, r') →
        libsignal_core.curve.PublicKey.verify_signature pk msg σ = .ok true

/-- On every public key, message and signature, verification returns a Boolean, and it returns
`false` for a malformed signature or key
(`rust/core/src/curve.rs:138-151`; `rust/core/src/curve/curve25519.rs:119-139`). -/
def VerifyTotal : Prop :=
  ∀ (pk : ECPub) (parts : Slice (Slice U8)) (σ : Slice U8),
    ∃ b, curve.PublicKey.verify_signature_for_multipart_message pk parts σ = .ok b

end Signature

section Kyber

/-- On a key whose length is not 1568 bytes, encapsulation returns `BadKEMKeyLength` and leaves
the generator state unchanged, because it checks the length before it draws any randomness
(`rust/protocol/src/kem/kyber1024.rs:31-40`). -/
def KyberEncapsBadLength : Prop :=
  ∀ {R : Type} (crng : rand_core_1.CryptoRng R) (key : kem.KeyMaterial kem.Public) (r : R),
    key.data.length ≠ 1568 →
      kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate crng key r =
        .ok (.Err (), r)

/-- The backend contract for encapsulation. When the generator is total on `Dom` and the state is
in `Dom`, encapsulation on a 1568-byte key terminates without panicking, with a 32-byte shared
secret, a 1568-byte ciphertext and a state in `Dom`. libcrux 0.0.10 converts the key by length
only (`libcrux-ml-kem-0.0.10/src/types.rs:45-54`) and validates nothing else. Its rejection
sampling loop has no proved bound (`src/sampling.rs:74`, `:95-102`), so the contract trusts
termination. -/
def KyberEncapsBackend : Prop :=
  ∀ {R : Type} (crng : rand_core_1.CryptoRng R) (Dom : R → Prop), RngTotal crng.RngCoreInst Dom →
    ∀ (key : kem.KeyMaterial kem.Public) (r : R), key.data.length = 1568 → Dom r →
      kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate crng key r
        ⦃ res r' => (∃ ss ct, res = .Ok (ss, ct) ∧ ss.length = 32 ∧ ct.length = 1568) ∧ Dom r' ⦄

/-- On every secret key and ciphertext, decapsulation terminates without panicking and returns:
`BadKeyLength` if the secret key does not have 3168 bytes; otherwise `BadCiphertext` if the
ciphertext does not have 1568 bytes; otherwise a 32-byte shared secret
(`rust/protocol/src/kem/kyber1024.rs:42-54`). On a mismatched ciphertext, Kyber returns a
pseudorandom secret, not an error, so success says nothing about agreement. `KyberDeltaCorrect`
bounds how often the secrets differ. Termination rests on the same unbounded sampling loop as
encapsulation. -/
def KyberDecaps : Prop :=
  ∀ (sk : kem.KeyMaterial kem.Secret) (ct : Slice U8),
    kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate sk ct ⦃ res =>
      (sk.data.length ≠ 3168 → res = .Err .BadKeyLength) ∧
      (sk.data.length = 3168 → ct.length ≠ 1568 → res = .Err .BadCiphertext) ∧
      (sk.data.length = 3168 → ct.length = 1568 → ∃ ss, res = .Ok ss ∧ ss.length = 32) ⦄

end Kyber

section Std

/-- Allocating an owned string from a string literal terminates. `pqxdh_accept` does this only
to build the message of its error for a non-canonical ephemeral key (`rust/protocol/src/pqxdh.rs:
339-344`).

This contract stays. The Aeneas standard library models no way to build a `String` from a `str`,
and `String::from`, `to_string` and `format!` are not modelled either, so no translation patch can
route this call through a modelled one. The other standard-library conversions that the two entry
points use are modelled: the extraction calls `alloc.vec.FromBoxSliceVec.from`,
`alloc.slice.Slice.to_vec` and `core.slice.cmp.PartialEqSlice.eq` instead of axioms. The Aeneas
library states the property of `FromBoxSliceVec.from` (`from_spec`), and `Libsignal/Proofs/Std/`
proves the properties of the byte-slice conversion and of the slice comparison. -/
def ToOwnedTotal : Prop :=
  ∀ s : Str, ∃ t, Str.Insts.AllocBorrowToOwnedString.to_owned s = .ok t

end Std

/-- The contracts on the opaque leaves that the two entry points and the KEM experiment call:
curve25519 agreement and checks, the Kyber1024 backend and the allocation of a string. -/
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

/-- The fault-or-value form of `AgreementTotal` and `AgreementDerived`. When agreement returns, it
returns 32 bytes or `InvalidKeyAgreement`. When both agreements between two keys with derived
public halves return, they return the same 32 bytes. -/
def AgreementPartial : Prop :=
  (∀ (sk : ECPriv) (pk : ECPub) r, curve.PrivateKey.calculate_agreement sk pk = .ok r →
    (∃ s, r = .Ok s ∧ s.length = 32) ∨ r = .Err .InvalidKeyAgreement) ∧
  ∀ (sk₁ sk₂ : ECPriv) (pk₁ pk₂ : ECPub) r₁ r₂,
    curve.PrivateKey.public_key sk₁ = .ok (.Ok pk₁) →
      curve.PrivateKey.public_key sk₂ = .ok (.Ok pk₂) →
        curve.PrivateKey.calculate_agreement sk₁ pk₂ = .ok r₁ →
          curve.PrivateKey.calculate_agreement sk₂ pk₁ = .ok r₂ →
            r₁ = r₂ ∧ ∃ s, r₁ = .Ok s ∧ s.length = 32

/-- The fault-or-value form of `DerivedCanonical`. When the canonicality check returns on a
derived public key, it returns `true`. -/
def DerivedCanonicalPartial : Prop :=
  ∀ (sk : ECPriv) (pk : ECPub) b, curve.PrivateKey.public_key sk = .ok (.Ok pk) →
    libsignal_core.curve.PublicKey.is_canonical pk = .ok b → b = true

/-- The fault-or-value form of `SignTotal` and `SignVerify`. When signing returns, it returns a
64-byte signature. When verification of a signature by the private key `sk` returns under the
public key derived from `sk`, it returns `true`. -/
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

/-- The fault-or-value form of the Kyber contracts. When encapsulation returns on a key that does
not have 1568 bytes, it returns `BadKEMKeyLength` and the unchanged state. When it returns on a
1568-byte key, it returns a 32-byte secret and a 1568-byte ciphertext. When decapsulation returns,
it follows the three branches of `KyberDecaps`. -/
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

/-- The fault-or-value form of `HkdfSha256Contract H`. When the helper returns on a 96-byte buffer
and no salt, it returns `Ok(())` and the RFC 5869 output computed from the MAC interface `H`. -/
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
  /-- See `HkdfSha256Partial`. -/
  hkdf : HkdfSha256Partial H

end Protocols.PQXDH
