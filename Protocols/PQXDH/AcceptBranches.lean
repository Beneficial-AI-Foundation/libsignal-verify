/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Alessandro D'Angelo
-/
import Protocols.PQXDH.BranchHelpers

/-!
# Branch equations of the extracted `pqxdh_accept`

The extracted `pqxdh_accept` runs these steps in order (`rust/protocol/src/pqxdh.rs:337-387`):

1. the canonicality check on the initiator's ephemeral key;
2. DH1, DH2 and DH3, and DH4 when Bob has a one-time prekey;
3. the decapsulation of the initiator's Kyber ciphertext;
4. the key derivation on the assembled input.

Each of the first three kinds of step returns a value, an error, or a panic or divergence of the
leaf. An error ends the call with that error, and a value goes into the key-derivation input. This
file states one equation for every way that the call can end, in this order:
`accept_noncanonical_eq`, `accept_dh1_err_eq` to `accept_dh4_err_eq`, `accept_decaps_err_eq` and
`accept_ok_eq`. `accept_cases` is the summary: if the call returns a value, one of these branches
happened.

The equations use no contract. Their hypotheses name the values that the leaves return, and the
bytes assembled so far must fit in a vector, because `extend_from_slice` panics on overflow. No
hypothesis gives the length of an output of a leaf. A panic or a divergence of a leaf is not an
error: the equations say nothing about it, and `accept_cases` excludes it, because it assumes that
the call returns a value.

The error of the canonicality branch is built by `to_owned`, which the extraction leaves opaque
(`ToOwnedTotal` in `Contracts.lean`). So the equation of that branch keeps the call to `to_owned`.
-/

open Aeneas Aeneas.Std Result
open libsignal_protocol

namespace Protocols.PQXDH

/-- The canonicality check on the initiator's ephemeral key, the first step of `pqxdh_accept`. -/
noncomputable abbrev acceptCanonical (rp : pqxdh.RecipientParameters) :=
  libsignal_core.curve.PublicKey.is_canonical rp.their_ephemeral_key

/-- DH1 of the responder: Bob's signed prekey with the initiator's identity key. -/
noncomputable abbrev acceptDh1 (rp : pqxdh.RecipientParameters) :=
  curve.PrivateKey.calculate_agreement rp.our_signed_pre_key_pair.private_key
    rp.their_identity_key.public_key

/-- DH2 of the responder: Bob's identity key with the initiator's ephemeral key. -/
noncomputable abbrev acceptDh2 (rp : pqxdh.RecipientParameters) :=
  curve.PrivateKey.calculate_agreement rp.our_identity_key_pair.private_key
    rp.their_ephemeral_key

/-- DH3 of the responder: Bob's signed prekey with the initiator's ephemeral key. -/
noncomputable abbrev acceptDh3 (rp : pqxdh.RecipientParameters) :=
  curve.PrivateKey.calculate_agreement rp.our_signed_pre_key_pair.private_key
    rp.their_ephemeral_key

/-- DH4 of the responder, when Bob uses a one-time prekey: that prekey with the initiator's
ephemeral key. -/
noncomputable abbrev acceptDh4 (rp : pqxdh.RecipientParameters)
    (opk : libsignal_core.curve.KeyPair) :=
  curve.PrivateKey.calculate_agreement opk.private_key rp.their_ephemeral_key

/-- The decapsulation of the initiator's Kyber ciphertext with Bob's Kyber prekey. -/
noncomputable abbrev acceptDecaps (rp : pqxdh.RecipientParameters) :=
  kem.KeySecret.decapsulate rp.our_kyber_pre_key_pair.secret_key rp.their_kyber_ciphertext

/-- The agreements of a `pqxdh_accept` call return `d1`, `d2` and `d3`, and `d4` is the result of
DH4 when Bob has a one-time prekey and `none` otherwise. -/
def AcceptAgreements (rp : pqxdh.RecipientParameters) (d1 d2 d3 : Slice U8)
    (d4 : Option (Slice U8)) : Prop :=
  acceptDh1 rp = .ok (.Ok d1) ∧ acceptDh2 rp = .ok (.Ok d2) ∧ acceptDh3 rp = .ok (.Ok d3) ∧
    (match rp.our_one_time_pre_key_pair with
      | none => d4 = none
      | some opk => ∃ d, acceptDh4 rp opk = .ok (.Ok d) ∧ d4 = some d)

/-- Branch 1, canonicality: when the check returns `false`, the call returns the error
`InvalidMessage` for a pre-key message, with the message that `to_owned` builds. -/
theorem accept_noncanonical_eq (rp : pqxdh.RecipientParameters)
    (hc : acceptCanonical rp = .ok false) :
    pqxdh.pqxdh_accept rp = (do
      let s ← Str.Insts.AllocBorrowToOwnedString.to_owned
        (toStr "incoming base key is invalid")
      .ok (.Err (.InvalidMessage protocol.CiphertextMessageType.PreKey s))) := by
  simp only [acceptCanonical] at hc
  unfold pqxdh.pqxdh_accept
  simp [hc]

/-- Branch 2, DH1: when the check passes and DH1 returns the error `e`, the call returns the
conversion of `e` into a protocol error. -/
theorem accept_dh1_err_eq (rp : pqxdh.RecipientParameters) (e : libsignal_core.curve.CurveError)
    (hc : acceptCanonical rp = .ok true) (h1 : acceptDh1 rp = .ok (.Err e)) :
    pqxdh.pqxdh_accept rp = (do
      let v ← error.SignalProtocolError.Insts.CoreConvertFromCurveError.from e
      .ok (.Err v)) := by
  simp only [acceptCanonical] at hc
  simp only [acceptDh1] at h1
  obtain ⟨i, s0, sec, hi, hs, hsec, -⟩ := kdf_start
  unfold pqxdh.pqxdh_accept
  simp [hc, hi, hs, hsec, h1, identity_key.IdentityKey.impl.public_key,
    identity_key.IdentityKeyPair.impl.private_key,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  rfl

/-- Branch 3, DH2: DH1 returns `d1`, the bytes so far fit in a vector, and DH2 returns the error
`e`. -/
theorem accept_dh2_err_eq (rp : pqxdh.RecipientParameters) (d1 : Slice U8)
    (e : libsignal_core.curve.CurveError)
    (hc : acceptCanonical rp = .ok true) (h1 : acceptDh1 rp = .ok (.Ok d1))
    (hl : (kdfPrefixBytes [d1]).length ≤ Usize.max) (h2 : acceptDh2 rp = .ok (.Err e)) :
    pqxdh.pqxdh_accept rp = (do
      let v ← error.SignalProtocolError.Insts.CoreConvertFromCurveError.from e
      .ok (.Err v)) := by
  simp only [acceptCanonical] at hc
  simp only [acceptDh1] at h1
  simp only [acceptDh2] at h2
  obtain ⟨i, s0, sec, hi, hs, hsec, hval⟩ := kdf_start
  obtain ⟨sec2, hsec2, -⟩ := extend_prefix d1 hval hl
  unfold pqxdh.pqxdh_accept
  simp [hc, hi, hs, hsec, h1, hsec2, h2, identity_key.IdentityKey.impl.public_key,
    identity_key.IdentityKeyPair.impl.private_key,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  rfl

/-- Branch 4, DH3: DH1 and DH2 return `d1` and `d2`, the bytes so far fit in a vector, and DH3
returns the error `e`. -/
theorem accept_dh3_err_eq (rp : pqxdh.RecipientParameters) (d1 d2 : Slice U8)
    (e : libsignal_core.curve.CurveError)
    (hc : acceptCanonical rp = .ok true) (h1 : acceptDh1 rp = .ok (.Ok d1))
    (h2 : acceptDh2 rp = .ok (.Ok d2)) (hl : (kdfPrefixBytes [d1, d2]).length ≤ Usize.max)
    (h3 : acceptDh3 rp = .ok (.Err e)) :
    pqxdh.pqxdh_accept rp = (do
      let v ← error.SignalProtocolError.Insts.CoreConvertFromCurveError.from e
      .ok (.Err v)) := by
  simp only [acceptCanonical] at hc
  simp only [acceptDh1] at h1
  simp only [acceptDh2] at h2
  simp only [acceptDh3] at h3
  obtain ⟨i, s0, sec, hi, hs, hsec, hval⟩ := kdf_start
  obtain ⟨sec2, sec3, hsec2, hsec3, -⟩ := extend_prefix_two d1 d2 hval hl
  unfold pqxdh.pqxdh_accept
  simp [hc, hi, hs, hsec, h1, hsec2, h2, hsec3, h3, identity_key.IdentityKey.impl.public_key,
    identity_key.IdentityKeyPair.impl.private_key,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  rfl

/-- Branch 5, DH4: Bob has the one-time prekey `opk`, DH1 to DH3 return `d1`, `d2` and `d3`, the
bytes so far fit in a vector, and DH4 returns the error `e`. -/
theorem accept_dh4_err_eq (rp : pqxdh.RecipientParameters) (opk : libsignal_core.curve.KeyPair)
    (d1 d2 d3 : Slice U8) (e : libsignal_core.curve.CurveError)
    (hc : acceptCanonical rp = .ok true) (hopk : rp.our_one_time_pre_key_pair = some opk)
    (h1 : acceptDh1 rp = .ok (.Ok d1)) (h2 : acceptDh2 rp = .ok (.Ok d2))
    (h3 : acceptDh3 rp = .ok (.Ok d3)) (hl : (kdfPrefixBytes [d1, d2, d3]).length ≤ Usize.max)
    (h4 : acceptDh4 rp opk = .ok (.Err e)) :
    pqxdh.pqxdh_accept rp = (do
      let v ← error.SignalProtocolError.Insts.CoreConvertFromCurveError.from e
      .ok (.Err v)) := by
  simp only [acceptCanonical] at hc
  simp only [acceptDh1] at h1
  simp only [acceptDh2] at h2
  simp only [acceptDh3] at h3
  simp only [acceptDh4] at h4
  obtain ⟨i, s0, sec, hi, hs, hsec, hval⟩ := kdf_start
  obtain ⟨sec2, sec3, sec4, hsec2, hsec3, hsec4, -⟩ := extend_prefix_three d1 d2 d3 hval hl
  unfold pqxdh.pqxdh_accept
  simp [hc, hi, hs, hsec, h1, hsec2, h2, hsec3, h3, hsec4, hopk, h4,
    identity_key.IdentityKey.impl.public_key,
    identity_key.IdentityKeyPair.impl.private_key,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  rfl

/-- Branch 6, decapsulation: the agreements return `d1`, `d2`, `d3` and `d4`, the bytes so far fit
in a vector, and the decapsulation returns the error `e`. The call returns `e` itself. -/
theorem accept_decaps_err_eq (rp : pqxdh.RecipientParameters) (d1 d2 d3 : Slice U8)
    (d4 : Option (Slice U8)) (e : error.SignalProtocolError)
    (hc : acceptCanonical rp = .ok true) (hag : AcceptAgreements rp d1 d2 d3 d4)
    (hl : (kdfPrefixBytes (d1 :: d2 :: d3 :: d4.toList)).length ≤ Usize.max)
    (hd : acceptDecaps rp = .ok (.Err e)) :
    pqxdh.pqxdh_accept rp = .ok (.Err e) := by
  obtain ⟨hd1, hd2, hd3, hd4⟩ := hag
  simp only [acceptCanonical] at hc
  simp only [acceptDh1] at hd1
  simp only [acceptDh2] at hd2
  simp only [acceptDh3] at hd3
  simp only [acceptDecaps] at hd
  obtain ⟨i, s0, sec, hi, hs, hsec, hval⟩ := kdf_start
  unfold pqxdh.pqxdh_accept
  rcases hopk : rp.our_one_time_pre_key_pair with _ | opk
  · simp only [hopk] at hd4
    subst hd4
    obtain ⟨sec2, sec3, sec4, hsec2, hsec3, hsec4, -⟩ := extend_prefix_three d1 d2 d3 hval hl
    simp [hc, hi, hs, hsec, hd1, hsec2, hd2, hsec3, hd3, hsec4, hd,
    identity_key.IdentityKey.impl.public_key,
    identity_key.IdentityKeyPair.impl.private_key,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]
  · simp only [hopk] at hd4
    obtain ⟨d, hd4', rfl⟩ := hd4
    simp only [acceptDh4] at hd4'
    obtain ⟨sec2, sec3, sec4, hsec2, hsec3, hsec4, hval4⟩ := extend_prefix_three d1 d2 d3 hval
      (le_trans (kdfPrefixBytes_length_le_append [d1, d2, d3] d) hl)
    obtain ⟨sec5, hsec5, -⟩ := extend_prefix d hval4 hl
    simp [hc, hi, hs, hsec, hd1, hsec2, hd2, hsec3, hd3, hsec4, hd4', hsec5, hd,
    identity_key.IdentityKey.impl.public_key,
    identity_key.IdentityKeyPair.impl.private_key,
    core.result.Result.Insts.CoreOpsTry.branch,
    core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual]

/-- Branch 7, success: the agreements return `d1`, `d2`, `d3` and `d4`, the decapsulation returns
the secret `ss`, `kdfInput` assembles `km` from them, and the key derivation returns `hk` on `km`.
The call returns `hk`. -/
theorem accept_ok_eq (rp : pqxdh.RecipientParameters) (d1 d2 d3 ss km : Slice U8)
    (d4 : Option (Slice U8)) (hk : pqxdh.HandshakeKeys)
    (hc : acceptCanonical rp = .ok true) (hag : AcceptAgreements rp d1 d2 d3 d4)
    (hd : acceptDecaps rp = .ok (.Ok ss)) (hkm : kdfInput d1 d2 d3 d4 ss = .ok km)
    (hder : pqxdh.HandshakeKeys.derive km = .ok hk) :
    pqxdh.pqxdh_accept rp = .ok (.Ok hk) := by
  obtain ⟨hd1, hd2, hd3, hd4⟩ := hag
  simp only [acceptCanonical] at hc
  simp only [acceptDh1] at hd1
  simp only [acceptDh2] at hd2
  simp only [acceptDh3] at hd3
  simp only [acceptDecaps] at hd
  obtain ⟨i, s, sec1, sec2, sec3, sec4, sec5, sec6, hi, hs, h1, h2, h3, h4, h5, h6, rfl⟩ :=
    kdfInput_inv hkm
  unfold pqxdh.pqxdh_accept
  rcases hopk : rp.our_one_time_pre_key_pair with _ | opk
  · simp only [hopk] at hd4
    subst hd4
    simp only at h5
    subst h5
    simp [hc, hi, hs, h1, hd1, h2, hd2, h3, hd3, h4, hd, h6, hder,
      identity_key.IdentityKey.impl.public_key, identity_key.IdentityKeyPair.impl.private_key,
      core.result.Result.Insts.CoreOpsTry.branch]
  · simp only [hopk] at hd4
    obtain ⟨d, hd4', rfl⟩ := hd4
    simp only [acceptDh4] at hd4'
    simp only at h5
    simp [hc, hi, hs, h1, hd1, h2, hd2, h3, hd3, h4, hd4', h5, hd, h6, hder,
      identity_key.IdentityKey.impl.public_key, identity_key.IdentityKeyPair.impl.private_key,
      core.result.Result.Insts.CoreOpsTry.branch]

/-- The summary: if `pqxdh_accept` returns a value, one of the seven branches above happened, in
the order of the code. A branch lists the values of the earlier steps and the bytes so far, which
fit in a vector. -/
theorem accept_cases (rp : pqxdh.RecipientParameters)
    (res : core.result.Result pqxdh.HandshakeKeys error.SignalProtocolError)
    (h : pqxdh.pqxdh_accept rp = .ok res) :
    (acceptCanonical rp = .ok false ∧
      ∃ s, Str.Insts.AllocBorrowToOwnedString.to_owned
          (toStr "incoming base key is invalid") = .ok s ∧
        res = .Err (.InvalidMessage protocol.CiphertextMessageType.PreKey s)) ∨
    (acceptCanonical rp = .ok true ∧
      ∃ e v, acceptDh1 rp = .ok (.Err e) ∧
        error.SignalProtocolError.Insts.CoreConvertFromCurveError.from e = .ok v ∧
        res = .Err v) ∨
    (acceptCanonical rp = .ok true ∧
      ∃ d1 e v, acceptDh1 rp = .ok (.Ok d1) ∧ (kdfPrefixBytes [d1]).length ≤ Usize.max ∧
        acceptDh2 rp = .ok (.Err e) ∧
        error.SignalProtocolError.Insts.CoreConvertFromCurveError.from e = .ok v ∧
        res = .Err v) ∨
    (acceptCanonical rp = .ok true ∧
      ∃ d1 d2 e v, acceptDh1 rp = .ok (.Ok d1) ∧ acceptDh2 rp = .ok (.Ok d2) ∧
        (kdfPrefixBytes [d1, d2]).length ≤ Usize.max ∧ acceptDh3 rp = .ok (.Err e) ∧
        error.SignalProtocolError.Insts.CoreConvertFromCurveError.from e = .ok v ∧
        res = .Err v) ∨
    (acceptCanonical rp = .ok true ∧
      ∃ opk d1 d2 d3 e v, rp.our_one_time_pre_key_pair = some opk ∧
        acceptDh1 rp = .ok (.Ok d1) ∧ acceptDh2 rp = .ok (.Ok d2) ∧
        acceptDh3 rp = .ok (.Ok d3) ∧ (kdfPrefixBytes [d1, d2, d3]).length ≤ Usize.max ∧
        acceptDh4 rp opk = .ok (.Err e) ∧
        error.SignalProtocolError.Insts.CoreConvertFromCurveError.from e = .ok v ∧
        res = .Err v) ∨
    (acceptCanonical rp = .ok true ∧
      ∃ d1 d2 d3 d4 e, AcceptAgreements rp d1 d2 d3 d4 ∧
        (kdfPrefixBytes (d1 :: d2 :: d3 :: d4.toList)).length ≤ Usize.max ∧
        acceptDecaps rp = .ok (.Err e) ∧ res = .Err e) ∨
    (acceptCanonical rp = .ok true ∧
      ∃ d1 d2 d3 d4 ss km hk, AcceptAgreements rp d1 d2 d3 d4 ∧
        acceptDecaps rp = .ok (.Ok ss) ∧ kdfInput d1 d2 d3 d4 ss = .ok km ∧
        pqxdh.HandshakeKeys.derive km = .ok hk ∧ res = .Ok hk) := by
  unfold pqxdh.pqxdh_accept at h
  simp only [bind_eq_ok_iff] at h
  obtain ⟨b, hb, h⟩ := h
  cases b
  · simp only [Bool.false_eq_true, ↓reduceIte, bind_eq_ok_iff, Result.ok.injEq] at h
    obtain ⟨s, hs, h⟩ := h
    exact Or.inl ⟨hb, s, hs, h.symm⟩
  · simp only [↓reduceIte, bind_eq_ok_iff] at h
    obtain ⟨i, hi, s, hs, sec1, hsec1, pk, hpk, r, hr, cf, hcf, h⟩ := h
    have hv1 := kdf_start_of_ok hi hs hsec1
    simp only [identity_key.IdentityKey.impl.public_key, Result.ok.injEq] at hpk
    subst hpk
    rcases r with d1 | e1
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, Result.ok.injEq] at hcf
      subst hcf
      simp only [bind_eq_ok_iff] at h
      obtain ⟨sec2, hsec2, pk1, hpk1, r1, hr1, cf1, hcf1, h⟩ := h
      obtain ⟨hf1, hv2⟩ := extend_prefix_of_ok hv1 hsec2
      simp only [identity_key.IdentityKeyPair.impl.private_key, Result.ok.injEq] at hpk1
      subst hpk1
      rcases r1 with d2 | e2
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, Result.ok.injEq] at hcf1
        subst hcf1
        simp only [bind_eq_ok_iff] at h
        obtain ⟨sec3, hsec3, r2, hr2, cf2, hcf2, h⟩ := h
        obtain ⟨hf2, hv3⟩ := extend_prefix_of_ok hv2 hsec3
        rcases r2 with d3 | e3
        · simp only [core.result.Result.Insts.CoreOpsTry.branch, Result.ok.injEq] at hcf2
          subst hcf2
          simp only [bind_eq_ok_iff] at h
          obtain ⟨sec4, hsec4, h⟩ := h
          obtain ⟨hf3, hv4⟩ := extend_prefix_of_ok hv3 hsec4
          rcases hopk : rp.our_one_time_pre_key_pair with _ | opk
          · simp only [hopk] at h
            simp only [bind_eq_ok_iff] at h
            obtain ⟨r3, hr3, cf3, hcf3, h⟩ := h
            rcases r3 with ss | e4
            · simp only [core.result.Result.Insts.CoreOpsTry.branch, Result.ok.injEq] at hcf3
              subst hcf3
              simp only [bind_eq_ok_iff, Result.ok.injEq] at h
              obtain ⟨sec5, hsec5, hk', hder, h⟩ := h
              refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hb, d1, d2, d3, none, ss,
                alloc.vec.Vec.deref sec5, hk', ⟨hr, hr1, hr2, by simp [hopk]⟩, hr3, ?_, hder,
                h.symm⟩)))))
              simp [kdfInput, pure_tc_eq, hi, hs, hsec1, hsec2, hsec3, hsec4, hsec5]
            · simp only [core.result.Result.Insts.CoreOpsTry.branch, Result.ok.injEq] at hcf3
              subst hcf3
              simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                bind_tc_eq, bind_eq_ok_iff, Result.ok.injEq] at h
              obtain ⟨v, hv, h⟩ := h
              have hve : v = e4 := by simpa using hv.symm
              subst hve
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hb, d1, d2, d3, none, v,
                ⟨hr, hr1, hr2, by simp [hopk]⟩, hf3, hr3, h.symm⟩)))))
          · simp only [hopk] at h
            simp only [bind_eq_ok_iff] at h
            obtain ⟨r3, hr3, cf3, hcf3, h⟩ := h
            rcases r3 with d4 | e4
            · simp only [core.result.Result.Insts.CoreOpsTry.branch, Result.ok.injEq] at hcf3
              subst hcf3
              simp only [bind_eq_ok_iff] at h
              obtain ⟨sec5, hsec5, r4, hr4, cf4, hcf4, h⟩ := h
              obtain ⟨hf4, hv5⟩ := extend_prefix_of_ok hv4 hsec5
              rcases r4 with ss | e5
              · simp only [core.result.Result.Insts.CoreOpsTry.branch, Result.ok.injEq] at hcf4
                subst hcf4
                simp only [bind_eq_ok_iff, Result.ok.injEq] at h
                obtain ⟨sec6, hsec6, hk', hder, h⟩ := h
                refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨hb, d1, d2, d3, some d4, ss,
                  alloc.vec.Vec.deref sec6, hk', ⟨hr, hr1, hr2, ?_⟩, hr4, ?_, hder, h.symm⟩)))))
                · simp only [hopk]
                  exact ⟨d4, hr3, rfl⟩
                · simp [kdfInput, pure_tc_eq, hi, hs, hsec1, hsec2, hsec3, hsec4, hsec5, hsec6]
              · simp only [core.result.Result.Insts.CoreOpsTry.branch, Result.ok.injEq] at hcf4
                subst hcf4
                simp only [
                  core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                  bind_tc_eq, bind_eq_ok_iff, Result.ok.injEq] at h
                obtain ⟨v, hv, h⟩ := h
                have hve : v = e5 := by simpa using hv.symm
                subst hve
                refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hb, d1, d2, d3, some d4, v,
                  ⟨hr, hr1, hr2, ?_⟩, hf4, hr4, h.symm⟩)))))
                simp only [hopk]
                exact ⟨d4, hr3, rfl⟩
            · simp only [core.result.Result.Insts.CoreOpsTry.branch, Result.ok.injEq] at hcf3
              subst hcf3
              simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
                bind_tc_eq, bind_eq_ok_iff, Result.ok.injEq] at h
              obtain ⟨v, hv, h⟩ := h
              exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨hb, opk, d1, d2, d3, e4, v, rfl, hr,
                hr1, hr2, hf3, hr3, hv, h.symm⟩))))
        · simp only [core.result.Result.Insts.CoreOpsTry.branch, Result.ok.injEq] at hcf2
          subst hcf2
          simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
            bind_tc_eq, bind_eq_ok_iff, Result.ok.injEq] at h
          obtain ⟨v, hv, h⟩ := h
          exact Or.inr (Or.inr (Or.inr (Or.inl ⟨hb, d1, d2, e3, v, hr, hr1, hf2, hr2, hv,
            h.symm⟩)))
      · simp only [core.result.Result.Insts.CoreOpsTry.branch, Result.ok.injEq] at hcf1
        subst hcf1
        simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
          bind_tc_eq, bind_eq_ok_iff, Result.ok.injEq] at h
        obtain ⟨v, hv, h⟩ := h
        exact Or.inr (Or.inr (Or.inl ⟨hb, d1, e2, v, hr, hf1, hr1, hv, h.symm⟩))
    · simp only [core.result.Result.Insts.CoreOpsTry.branch, Result.ok.injEq] at hcf
      subst hcf
      simp only [core.result.Result.Insts.CoreOpsTry_traitFromResidualResult.from_residual,
        bind_tc_eq, bind_eq_ok_iff, Result.ok.injEq] at h
      obtain ⟨v, hv, h⟩ := h
      exact Or.inr (Or.inl ⟨hb, e1, v, hr, hv, h.symm⟩)

end Protocols.PQXDH
