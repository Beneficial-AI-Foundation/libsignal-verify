/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Alessandro D'Angelo
-/
import Protocols.PQXDH.BranchHelpers
import Protocols.PQXDH.Contracts

/-!
# Branch equations of the extracted `pqxdh_initiate`

The extracted `pqxdh_initiate` runs these steps in order (`rust/protocol/src/pqxdh.rs:201-247`):

1. DH1, DH2 and DH3, and DH4 when Bob has a one-time prekey;
2. the encapsulation to Bob's Kyber prekey, which draws from the generator and returns its new
   state;
3. the key derivation on the assembled input.

This file states one equation for every way that the call can end, in this order:
`initiate_dh1_err_eq` to `initiate_dh4_err_eq`, `initiate_encaps_err_eq` and `initiate_ok_eq`.
`initiate_cases` is the summary: if the call returns a value, one of these branches happened.
`initiate_err_rng_eq` says that a call that returns a protocol error leaves the generator state
unchanged.

The equations use no contract. Their hypotheses name the values that the leaves return, and the
bytes assembled so far must fit in a vector, because `extend_from_slice` panics on overflow. No
hypothesis gives the length of an output of a leaf. A panic or a divergence of a leaf is not an
error: the equations say nothing about it, and `initiate_cases` excludes it, because it assumes
that the call returns a value.

`initiate_err_rng_eq` takes the fault-or-value form of the Kyber contracts, `KyberPartial`. Its
encapsulation clause says that an encapsulation that returns on a key of the wrong length returns
an error and the state it was given, and that one that returns on a key of the right length
returns a value. The clause on the wrong length alone does not rule out an error on a key of the
right length, which would advance the state.
-/

open Aeneas Aeneas.Std Result
open libsignal_protocol

namespace Protocols.PQXDH

/-- DH1 of the initiator: Alice's identity key with Bob's signed prekey. -/
noncomputable abbrev initiateDh1 (ip : pqxdh.InitiatorParameters) :=
  curve.PrivateKey.calculate_agreement ip.our_identity_key_pair.private_key
    ip.their_signed_pre_key

/-- DH2 of the initiator: Alice's ephemeral key with Bob's identity key. -/
noncomputable abbrev initiateDh2 (ip : pqxdh.InitiatorParameters) :=
  curve.PrivateKey.calculate_agreement ip.our_ephemeral_key_pair.private_key
    ip.their_identity_key.public_key

/-- DH3 of the initiator: Alice's ephemeral key with Bob's signed prekey. -/
noncomputable abbrev initiateDh3 (ip : pqxdh.InitiatorParameters) :=
  curve.PrivateKey.calculate_agreement ip.our_ephemeral_key_pair.private_key
    ip.their_signed_pre_key

/-- DH4 of the initiator, when Bob has a one-time prekey: Alice's ephemeral key with that
prekey. -/
noncomputable abbrev initiateDh4 (ip : pqxdh.InitiatorParameters)
    (opk : libsignal_core.curve.PublicKey) :=
  curve.PrivateKey.calculate_agreement ip.our_ephemeral_key_pair.private_key opk

/-- The encapsulation to Bob's Kyber prekey, on the generator state `r`. -/
noncomputable abbrev initiateEncaps {Rand : Type} (crng : rand_core_1.CryptoRng Rand)
    (ip : pqxdh.InitiatorParameters) (r : Rand) :=
  kem.KeyPublic.encapsulate crng ip.their_kyber_pre_key r

/-- The agreements of a `pqxdh_initiate` call return `d1`, `d2` and `d3`, and `d4` is the result
of DH4 when Bob has a one-time prekey and `none` otherwise. -/
def InitiateAgreements (ip : pqxdh.InitiatorParameters) (d1 d2 d3 : Slice U8)
    (d4 : Option (Slice U8)) : Prop :=
  initiateDh1 ip = .ok (.Ok d1) ∧ initiateDh2 ip = .ok (.Ok d2) ∧
    initiateDh3 ip = .ok (.Ok d3) ∧
    (match ip.their_one_time_pre_key with
      | none => d4 = none
      | some opk => ∃ d, initiateDh4 ip opk = .ok (.Ok d) ∧ d4 = some d)

variable {Rand : Type}

/-- Branch 1, DH1: when DH1 returns the error `e`, the call returns the conversion of `e` into a
protocol error and the generator state it was given. -/
theorem initiate_dh1_err_eq (crng : rand_core_1.CryptoRng Rand) (rng : rand.rng.Rng Rand)
    (ip : pqxdh.InitiatorParameters) (r : Rand) (e : libsignal_core.curve.CurveError)
    (h1 : initiateDh1 ip = .ok (.Err e)) :
    pqxdh.pqxdh_initiate rng crng ip r = (do
      let v ← error.SignalProtocolError.Insts.CoreConvertFromCurveError.from e
      .ok (.Err v, r)) := by
  sorry

/-- Branch 2, DH2: DH1 returns `d1`, the bytes so far fit in a vector, and DH2 returns the error
`e`. -/
theorem initiate_dh2_err_eq (crng : rand_core_1.CryptoRng Rand) (rng : rand.rng.Rng Rand)
    (ip : pqxdh.InitiatorParameters) (r : Rand) (d1 : Slice U8)
    (e : libsignal_core.curve.CurveError) (h1 : initiateDh1 ip = .ok (.Ok d1))
    (hl : (kdfPrefixBytes [d1]).length ≤ Usize.max) (h2 : initiateDh2 ip = .ok (.Err e)) :
    pqxdh.pqxdh_initiate rng crng ip r = (do
      let v ← error.SignalProtocolError.Insts.CoreConvertFromCurveError.from e
      .ok (.Err v, r)) := by
  sorry

/-- Branch 3, DH3: DH1 and DH2 return `d1` and `d2`, the bytes so far fit in a vector, and DH3
returns the error `e`. -/
theorem initiate_dh3_err_eq (crng : rand_core_1.CryptoRng Rand) (rng : rand.rng.Rng Rand)
    (ip : pqxdh.InitiatorParameters) (r : Rand) (d1 d2 : Slice U8)
    (e : libsignal_core.curve.CurveError) (h1 : initiateDh1 ip = .ok (.Ok d1))
    (h2 : initiateDh2 ip = .ok (.Ok d2)) (hl : (kdfPrefixBytes [d1, d2]).length ≤ Usize.max)
    (h3 : initiateDh3 ip = .ok (.Err e)) :
    pqxdh.pqxdh_initiate rng crng ip r = (do
      let v ← error.SignalProtocolError.Insts.CoreConvertFromCurveError.from e
      .ok (.Err v, r)) := by
  sorry

/-- Branch 4, DH4: Bob has the one-time prekey `opk`, DH1 to DH3 return `d1`, `d2` and `d3`, the
bytes so far fit in a vector, and DH4 returns the error `e`. -/
theorem initiate_dh4_err_eq (crng : rand_core_1.CryptoRng Rand) (rng : rand.rng.Rng Rand)
    (ip : pqxdh.InitiatorParameters) (r : Rand) (opk : libsignal_core.curve.PublicKey)
    (d1 d2 d3 : Slice U8) (e : libsignal_core.curve.CurveError)
    (hopk : ip.their_one_time_pre_key = some opk) (h1 : initiateDh1 ip = .ok (.Ok d1))
    (h2 : initiateDh2 ip = .ok (.Ok d2)) (h3 : initiateDh3 ip = .ok (.Ok d3))
    (hl : (kdfPrefixBytes [d1, d2, d3]).length ≤ Usize.max)
    (h4 : initiateDh4 ip opk = .ok (.Err e)) :
    pqxdh.pqxdh_initiate rng crng ip r = (do
      let v ← error.SignalProtocolError.Insts.CoreConvertFromCurveError.from e
      .ok (.Err v, r)) := by
  sorry

/-- Branch 5, encapsulation: the agreements return `d1`, `d2`, `d3` and `d4`, the bytes so far
fit in a vector, and the encapsulation returns the error `e` and the state `r'`. The call returns
`e` and `r'`. -/
theorem initiate_encaps_err_eq (crng : rand_core_1.CryptoRng Rand) (rng : rand.rng.Rng Rand)
    (ip : pqxdh.InitiatorParameters) (r r' : Rand) (d1 d2 d3 : Slice U8)
    (d4 : Option (Slice U8)) (e : error.SignalProtocolError)
    (hag : InitiateAgreements ip d1 d2 d3 d4)
    (hl : (kdfPrefixBytes (d1 :: d2 :: d3 :: d4.toList)).length ≤ Usize.max)
    (he : initiateEncaps crng ip r = .ok (.Err e, r')) :
    pqxdh.pqxdh_initiate rng crng ip r = .ok (.Err e, r') := by
  sorry

/-- Branch 6, success: the agreements return `d1`, `d2`, `d3` and `d4`, the encapsulation returns
the secret `ss`, the ciphertext `ct` and the state `r'`, `kdfInput` assembles `km` from the
agreements and `ss`, and the key derivation returns `hk` on `km`. The call returns `hk` with `ct`
and `r'`. -/
theorem initiate_ok_eq (crng : rand_core_1.CryptoRng Rand) (rng : rand.rng.Rng Rand)
    (ip : pqxdh.InitiatorParameters) (r r' : Rand) (d1 d2 d3 ss ct km : Slice U8)
    (d4 : Option (Slice U8)) (hk : pqxdh.HandshakeKeys)
    (hag : InitiateAgreements ip d1 d2 d3 d4)
    (he : initiateEncaps crng ip r = .ok (.Ok (ss, ct), r'))
    (hkm : kdfInput d1 d2 d3 d4 ss = .ok km) (hder : pqxdh.HandshakeKeys.derive km = .ok hk) :
    pqxdh.pqxdh_initiate rng crng ip r =
      .ok (.Ok { keys := hk, kyber_ciphertext := ct }, r') := by
  sorry

/-- The summary: if `pqxdh_initiate` returns a value and the state `r'`, one of the six branches
above happened, in the order of the code. A branch lists the values of the earlier steps and the
bytes so far, which fit in a vector. In the first four branches the state is unchanged. -/
theorem initiate_cases (crng : rand_core_1.CryptoRng Rand) (rng : rand.rng.Rng Rand)
    (ip : pqxdh.InitiatorParameters) (r r' : Rand)
    (res : core.result.Result pqxdh.InitiatorAgreement error.SignalProtocolError)
    (h : pqxdh.pqxdh_initiate rng crng ip r = .ok (res, r')) :
    (∃ e v, initiateDh1 ip = .ok (.Err e) ∧
      error.SignalProtocolError.Insts.CoreConvertFromCurveError.from e = .ok v ∧
      res = .Err v ∧ r' = r) ∨
    (∃ d1 e v, initiateDh1 ip = .ok (.Ok d1) ∧ (kdfPrefixBytes [d1]).length ≤ Usize.max ∧
      initiateDh2 ip = .ok (.Err e) ∧
      error.SignalProtocolError.Insts.CoreConvertFromCurveError.from e = .ok v ∧
      res = .Err v ∧ r' = r) ∨
    (∃ d1 d2 e v, initiateDh1 ip = .ok (.Ok d1) ∧ initiateDh2 ip = .ok (.Ok d2) ∧
      (kdfPrefixBytes [d1, d2]).length ≤ Usize.max ∧ initiateDh3 ip = .ok (.Err e) ∧
      error.SignalProtocolError.Insts.CoreConvertFromCurveError.from e = .ok v ∧
      res = .Err v ∧ r' = r) ∨
    (∃ opk d1 d2 d3 e v, ip.their_one_time_pre_key = some opk ∧
      initiateDh1 ip = .ok (.Ok d1) ∧ initiateDh2 ip = .ok (.Ok d2) ∧
      initiateDh3 ip = .ok (.Ok d3) ∧ (kdfPrefixBytes [d1, d2, d3]).length ≤ Usize.max ∧
      initiateDh4 ip opk = .ok (.Err e) ∧
      error.SignalProtocolError.Insts.CoreConvertFromCurveError.from e = .ok v ∧
      res = .Err v ∧ r' = r) ∨
    (∃ d1 d2 d3 d4 e, InitiateAgreements ip d1 d2 d3 d4 ∧
      (kdfPrefixBytes (d1 :: d2 :: d3 :: d4.toList)).length ≤ Usize.max ∧
      initiateEncaps crng ip r = .ok (.Err e, r') ∧ res = .Err e) ∨
    (∃ d1 d2 d3 d4 ss ct km hk, InitiateAgreements ip d1 d2 d3 d4 ∧
      initiateEncaps crng ip r = .ok (.Ok (ss, ct), r') ∧ kdfInput d1 d2 d3 d4 ss = .ok km ∧
      pqxdh.HandshakeKeys.derive km = .ok hk ∧
      res = .Ok { keys := hk, kyber_ciphertext := ct }) := by
  sorry

/-- A call of `pqxdh_initiate` that returns a protocol error leaves the generator state
unchanged, when the Kyber operations satisfy `KyberPartial`. -/
theorem initiate_err_rng_eq (hK : KyberPartial) (crng : rand_core_1.CryptoRng Rand)
    (rng : rand.rng.Rng Rand) (ip : pqxdh.InitiatorParameters) (r r' : Rand)
    (e : error.SignalProtocolError)
    (h : pqxdh.pqxdh_initiate rng crng ip r = .ok (.Err e, r')) : r' = r := by
  sorry

end Protocols.PQXDH
