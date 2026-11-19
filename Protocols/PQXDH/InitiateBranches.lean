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
  simp only [initiateDh1] at h1
  obtain ⟨i, s0, sec, hi, hs, hsec, -⟩ := kdf_start
  unfold pqxdh.pqxdh_initiate
  simp [hi, hs, hsec, h1, identity_key.IdentityKey.impl.public_key,
    identity_key.IdentityKeyPair.impl.private_key, Box.Insts.CoreConvertAsRef.as_ref,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  simp only [bind_tc_eq, Std.bind_assoc, bind_ok]

/-- Branch 2, DH2: DH1 returns `d1`, the bytes so far fit in a vector, and DH2 returns the error
`e`. -/
theorem initiate_dh2_err_eq (crng : rand_core_1.CryptoRng Rand) (rng : rand.rng.Rng Rand)
    (ip : pqxdh.InitiatorParameters) (r : Rand) (d1 : Slice U8)
    (e : libsignal_core.curve.CurveError) (h1 : initiateDh1 ip = .ok (.Ok d1))
    (hl : (kdfPrefixBytes [d1]).length ≤ Usize.max) (h2 : initiateDh2 ip = .ok (.Err e)) :
    pqxdh.pqxdh_initiate rng crng ip r = (do
      let v ← error.SignalProtocolError.Insts.CoreConvertFromCurveError.from e
      .ok (.Err v, r)) := by
  simp only [initiateDh1] at h1
  simp only [initiateDh2] at h2
  obtain ⟨i, s0, sec, hi, hs, hsec, hval⟩ := kdf_start
  obtain ⟨sec2, hsec2, -⟩ := extend_prefix d1 hval hl
  unfold pqxdh.pqxdh_initiate
  simp [hi, hs, hsec, h1, hsec2, h2, identity_key.IdentityKey.impl.public_key,
    identity_key.IdentityKeyPair.impl.private_key, Box.Insts.CoreConvertAsRef.as_ref,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  simp only [bind_tc_eq, Std.bind_assoc, bind_ok]

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
  simp only [initiateDh1] at h1
  simp only [initiateDh2] at h2
  simp only [initiateDh3] at h3
  obtain ⟨i, s0, sec, hi, hs, hsec, hval⟩ := kdf_start
  obtain ⟨sec2, sec3, hsec2, hsec3, -⟩ := extend_prefix_two d1 d2 hval hl
  unfold pqxdh.pqxdh_initiate
  simp [hi, hs, hsec, h1, hsec2, h2, hsec3, h3, identity_key.IdentityKey.impl.public_key,
    identity_key.IdentityKeyPair.impl.private_key, Box.Insts.CoreConvertAsRef.as_ref,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  simp only [bind_tc_eq, Std.bind_assoc, bind_ok]

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
  simp only [initiateDh1] at h1
  simp only [initiateDh2] at h2
  simp only [initiateDh3] at h3
  simp only [initiateDh4] at h4
  obtain ⟨i, s0, sec, hi, hs, hsec, hval⟩ := kdf_start
  obtain ⟨sec2, sec3, sec4, hsec2, hsec3, hsec4, -⟩ := extend_prefix_three d1 d2 d3 hval hl
  unfold pqxdh.pqxdh_initiate
  simp [hi, hs, hsec, h1, hsec2, h2, hsec3, h3, hsec4, hopk, h4,
    identity_key.IdentityKey.impl.public_key,
    identity_key.IdentityKeyPair.impl.private_key, Box.Insts.CoreConvertAsRef.as_ref,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  simp only [bind_tc_eq, Std.bind_assoc, bind_ok]

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
  obtain ⟨hd1, hd2, hd3, hd4⟩ := hag
  simp only [initiateDh1] at hd1
  simp only [initiateDh2] at hd2
  simp only [initiateDh3] at hd3
  simp only [initiateEncaps] at he
  obtain ⟨i, s0, sec, hi, hs, hsec, hval⟩ := kdf_start
  unfold pqxdh.pqxdh_initiate
  rcases hopk : ip.their_one_time_pre_key with _ | opk
  · simp only [hopk] at hd4
    subst hd4
    obtain ⟨sec2, sec3, sec4, hsec2, hsec3, hsec4, -⟩ := extend_prefix_three d1 d2 d3 hval hl
    simp [hi, hs, hsec, hd1, hsec2, hd2, hsec3, hd3, hsec4, he,
    identity_key.IdentityKey.impl.public_key,
    identity_key.IdentityKeyPair.impl.private_key, Box.Insts.CoreConvertAsRef.as_ref,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · simp only [hopk] at hd4
    obtain ⟨d, hd4', rfl⟩ := hd4
    simp only [initiateDh4] at hd4'
    obtain ⟨sec2, sec3, sec4, hsec2, hsec3, hsec4, hval4⟩ := extend_prefix_three d1 d2 d3 hval
      (le_trans (kdfPrefixBytes_length_le_append [d1, d2, d3] d) hl)
    obtain ⟨sec5, hsec5, -⟩ := extend_prefix d hval4 hl
    simp [hi, hs, hsec, hd1, hsec2, hd2, hsec3, hd3, hsec4, hd4', hsec5, he,
    identity_key.IdentityKey.impl.public_key,
    identity_key.IdentityKeyPair.impl.private_key, Box.Insts.CoreConvertAsRef.as_ref,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

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
  obtain ⟨hd1, hd2, hd3, hd4⟩ := hag
  simp only [initiateDh1] at hd1
  simp only [initiateDh2] at hd2
  simp only [initiateDh3] at hd3
  simp only [initiateEncaps] at he
  obtain ⟨i, s, sec1, sec2, sec3, sec4, sec5, sec6, hi, hs, h1, h2, h3, h4, h5, h6, rfl⟩ :=
    kdfInput_inv hkm
  unfold pqxdh.pqxdh_initiate
  rcases hopk : ip.their_one_time_pre_key with _ | opk
  · simp only [hopk] at hd4
    subst hd4
    simp only at h5
    subst h5
    simp [hi, hs, h1, hd1, h2, hd2, h3, hd3, h4, he, h6, hder,
    identity_key.IdentityKey.impl.public_key,
    identity_key.IdentityKeyPair.impl.private_key, Box.Insts.CoreConvertAsRef.as_ref,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · simp only [hopk] at hd4
    obtain ⟨d, hd4', rfl⟩ := hd4
    simp only [initiateDh4] at hd4'
    simp only at h5
    simp [hi, hs, h1, hd1, h2, hd2, h3, hd3, h4, hd4', h5, he, h6, hder,
    identity_key.IdentityKey.impl.public_key,
    identity_key.IdentityKeyPair.impl.private_key, Box.Insts.CoreConvertAsRef.as_ref,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

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
  unfold pqxdh.pqxdh_initiate at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨i, hi, s, hs, sec1, hsec1, pk, hpk, r1, hr1, cf, hcf, h⟩ := h
  have hv1 := kdf_start_of_ok hi hs hsec1
  simp only [identity_key.IdentityKeyPair.impl.private_key, Result.ok.injEq] at hpk
  subst hpk
  rcases r1 with d1 | e1
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, Result.ok.injEq] at hcf
    subst hcf
    simp only [bind_eq_ok_iff] at h
    obtain ⟨sec2, hsec2, pk1, hpk1, r2, hr2, cf1, hcf1, h⟩ := h
    obtain ⟨hf1, hv2⟩ := extend_prefix_of_ok hv1 hsec2
    simp only [identity_key.IdentityKey.impl.public_key, Result.ok.injEq] at hpk1
    subst hpk1
    rcases r2 with d2 | e2
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, Result.ok.injEq] at hcf1
      subst hcf1
      simp only [bind_eq_ok_iff] at h
      obtain ⟨sec3, hsec3, r3, hr3, cf2, hcf2, h⟩ := h
      obtain ⟨hf2, hv3⟩ := extend_prefix_of_ok hv2 hsec3
      rcases r3 with d3 | e3
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, Result.ok.injEq] at hcf2
        subst hcf2
        simp only [bind_eq_ok_iff] at h
        obtain ⟨sec4, hsec4, h⟩ := h
        obtain ⟨hf3, hv4⟩ := extend_prefix_of_ok hv3 hsec4
        rcases hopk : ip.their_one_time_pre_key with _ | opk
        · simp only [hopk] at h
          simp only [bind_eq_ok_iff] at h
          obtain ⟨⟨r4, cs1⟩, hr4, h⟩ := h
          change Std.bind (core.result.Result.Insts.CoreOpsTry.branch r4) _ = _ at h
          simp only [bind_eq_ok_iff] at h
          obtain ⟨cf3, hcf3, h⟩ := h
          rcases r4 with ⟨ss, ct⟩ | e4
          · simp only [core.result.Result.Insts.CoreOpsTry.branch, Result.ok.injEq] at hcf3
            subst hcf3
            simp only [Box.Insts.CoreConvertAsRef.as_ref, bind_ok] at h
            change Std.bind (alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sec4 ss) _ = _
              at h
            simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨sec5, hsec5, hk', hder, hres, rfl⟩ := h
            refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨d1, d2, d3, none, ss, ct,
              alloc.vec.Vec.deref sec5, hk', ⟨hr1, hr2, hr3, by simp [hopk]⟩, hr4, ?_, hder,
              hres.symm⟩))))
            simp [kdfInput, pure_tc_eq, hi, hs, hsec1, hsec2, hsec3, hsec4, hsec5]
          · simp only [core.result.Result.Insts.CoreOpsTry.branch, Result.ok.injEq] at hcf3
            subst hcf3
            simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              bind_tc_eq, bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨_, ⟨v, hv, rfl⟩, rfl, rfl⟩ := h
            have hve : v = e4 := by simpa using hv.symm
            subst hve
            exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨d1, d2, d3, none, v,
              ⟨hr1, hr2, hr3, by simp [hopk]⟩, hf3, hr4, rfl⟩))))
        · simp only [hopk] at h
          simp only [bind_eq_ok_iff] at h
          obtain ⟨r4, hr4, cf3, hcf3, h⟩ := h
          rcases r4 with d4 | e4
          · simp only [core.result.Result.Insts.CoreOpsTry.branch, Result.ok.injEq] at hcf3
            subst hcf3
            simp only [bind_eq_ok_iff] at h
            obtain ⟨sec5, hsec5, ⟨r5, cs1⟩, hr5, h⟩ := h
            change Std.bind (core.result.Result.Insts.CoreOpsTry.branch r5) _ = _ at h
            simp only [bind_eq_ok_iff] at h
            obtain ⟨cf4, hcf4, h⟩ := h
            obtain ⟨hf4, hv5⟩ := extend_prefix_of_ok hv4 hsec5
            rcases r5 with ⟨ss, ct⟩ | e5
            · simp only [core.result.Result.Insts.CoreOpsTry.branch, Result.ok.injEq] at hcf4
              subst hcf4
              simp only [Box.Insts.CoreConvertAsRef.as_ref, bind_ok] at h
              change Std.bind (alloc.vec.Vec.extend_from_slice core.clone.CloneU8 sec5 ss) _ = _
                at h
              simp only [bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨sec6, hsec6, hk', hder, hres, rfl⟩ := h
              refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨d1, d2, d3, some d4, ss, ct,
                alloc.vec.Vec.deref sec6, hk', ⟨hr1, hr2, hr3, ?_⟩, hr5, ?_, hder,
                hres.symm⟩))))
              · simp only [hopk]
                exact ⟨d4, hr4, rfl⟩
              · simp [kdfInput, pure_tc_eq, hi, hs, hsec1, hsec2, hsec3, hsec4, hsec5, hsec6]
            · simp only [core.result.Result.Insts.CoreOpsTry.branch, Result.ok.injEq] at hcf4
              subst hcf4
              simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                bind_tc_eq, bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
              obtain ⟨_, ⟨v, hv, rfl⟩, rfl, rfl⟩ := h
              have hve : v = e5 := by simpa using hv.symm
              subst hve
              refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨d1, d2, d3, some d4, v,
                ⟨hr1, hr2, hr3, ?_⟩, hf4, hr5, rfl⟩))))
              simp only [hopk]
              exact ⟨d4, hr4, rfl⟩
          · simp only [core.result.Result.Insts.CoreOpsTry.branch, Result.ok.injEq] at hcf3
            subst hcf3
            simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
              bind_tc_eq, bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
            obtain ⟨_, ⟨v, hv, rfl⟩, rfl, rfl⟩ := h
            exact Or.inr (Or.inr (Or.inr (Or.inl ⟨opk, d1, d2, d3, e4, v, rfl, hr1, hr2, hr3,
              hf3, hr4, hv, rfl, rfl⟩)))
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, Result.ok.injEq] at hcf2
        subst hcf2
        simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          bind_tc_eq, bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
        obtain ⟨_, ⟨v, hv, rfl⟩, rfl, rfl⟩ := h
        exact Or.inr (Or.inr (Or.inl ⟨d1, d2, e3, v, hr1, hr2, hf2, hr3, hv, rfl, rfl⟩))
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, Result.ok.injEq] at hcf1
      subst hcf1
      simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        bind_tc_eq, bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
      obtain ⟨_, ⟨v, hv, rfl⟩, rfl, rfl⟩ := h
      exact Or.inr (Or.inl ⟨d1, e2, v, hr1, hf1, hr2, hv, rfl, rfl⟩)
  · simp only [core.result.Result.Insts.CoreOpsTry.branch, Result.ok.injEq] at hcf
    subst hcf
    simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
      bind_tc_eq, bind_eq_ok_iff, Result.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, ⟨v, hv, rfl⟩, rfl, rfl⟩ := h
    exact Or.inl ⟨e1, v, hr1, hv, rfl, rfl⟩

/-- If `kem.KeyPublic.encapsulate` returns a protocol error, it leaves the generator state
unchanged, when the Kyber operations satisfy `KyberPartial`. -/
theorem encaps_err_state (hK : KyberPartial) (crng : rand_core_1.CryptoRng Rand)
    (key : kem.Key kem.Public) (r r' : Rand) (e : error.SignalProtocolError)
    (h : kem.KeyPublic.encapsulate crng key r = .ok (.Err e, r')) : r' = r := by
  unfold kem.KeyPublic.encapsulate at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨⟨r0, cs1⟩, hr0, h⟩ := h
  have hp := hK.1 crng key.key_data r cs1 r0 hr0
  rcases r0 with ⟨ss, ct⟩ | u
  · simp [bind_eq_ok_iff, core.result.Result.map_err,
      core.result.Result.Insts.CoreOpsTry.branch] at h
  · by_cases hl : key.key_data.data.length = 1568
    · obtain ⟨ss, ct, hh, -⟩ := hp.2 hl
      simp at hh
    · obtain ⟨-, hcs⟩ := hp.1 hl
      simp only [core.result.Result.map_err, bind_tc_eq, core.result.Result.Insts.CoreOpsTry.branch,
        core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        core.convert.FromSame.from, bind_ok, uncurry_apply_pair, Std.bind_assoc, bind_eq_ok_iff,
        ok.injEq, Prod.mk.injEq, core.result.Result.Err.injEq, ↓existsAndEq, true_and] at h
      exact h.2.symm.trans hcs

/-- A call of `pqxdh_initiate` that returns a protocol error leaves the generator state
unchanged, when the Kyber operations satisfy `KyberPartial`. -/
theorem initiate_err_rng_eq (hK : KyberPartial) (crng : rand_core_1.CryptoRng Rand)
    (rng : rand.rng.Rng Rand) (ip : pqxdh.InitiatorParameters) (r r' : Rand)
    (e : error.SignalProtocolError)
    (h : pqxdh.pqxdh_initiate rng crng ip r = .ok (.Err e, r')) : r' = r := by
  rcases initiate_cases crng rng ip r r' _ h with
    ⟨_, _, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, _, _, hr⟩ | ⟨_, _, _, _, _, _, _, _, _, _, hr⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, hr⟩ | ⟨_, _, _, _, e', _, _, he, _⟩ |
    ⟨_, _, _, _, _, _, _, _, _, _, _, _, hres⟩
  · exact hr
  · exact hr
  · exact hr
  · exact hr
  · exact encaps_err_state hK crng ip.their_kyber_pre_key r r' e' he
  · cases hres

end Protocols.PQXDH
