/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Alessandro D'Angelo
-/
import Libsignal.Proofs.Core.Curve.PublicKey
import Libsignal.Proofs.Protocol.Kem.Key
import Protocols.PQXDH.HonestRun
import Protocols.PQXDH.Scheme

/-!
# One honest run of the Full realization

In an honest run of either scheme on the extracted entry points, both parties output equal keys
at least as often as the Kyber correctness experiment succeeds, when encapsulation runs on the
state that `generate` returns (`uakeInitiator_agreement_le`, `uakeRecipient_agreement_le`). Both
lemmas need the hypotheses that the docstring of `wrapperAgreement_uakeInitiator` in
`Correctness.lean` lists: honest keys, the core, HKDF, signature and generator contracts, and
perfect correctness of the synthetic AEAD. Of the signature contracts they take only `SignTotal`
and `SignVerify`.
-/

open OracleSpec OracleComp AKE AKE.UAKE ENNReal
open Aeneas Aeneas.Std
open libsignal_protocol
open Protocols.Realization

namespace Protocols.PQXDH

noncomputable section

variable {Rand Msg C IdC IdK : Type}

/-- The extracted serialization of a curve25519 public key returns some bytes, so `encodeEC` is
pure on every key. -/
private theorem encodeEC_eq (pk : ECPub) : ∃ b, encodeEC pk = pure b := by
  open libsignal_core.curve.PublicKey in
  obtain ⟨b, hb, -⟩ := exists_ok_of_spec (serialize_spec pk)
  exact ⟨b, by simp [encodeEC, hb]⟩

/-- The extracted serialization of a Kyber public key whose material has fewer than `Usize.max`
bytes returns some bytes, so `encodeKEM` is pure on it. -/
private theorem encodeKEM_eq (pk : PQPub) (h : (pk.key_data.data).length < Usize.max) :
    ∃ b, encodeKEM pk = pure b := by
  open kem in
  obtain ⟨b, hb, -⟩ :=
    exists_ok_of_spec (Key.serialize_spec Public.Insts.Libsignal_protocolKemKeyKind pk h)
  exact ⟨b, by simp [encodeKEM, hb]⟩

/-- A Kyber1024-shaped public key has fewer than `Usize.max` bytes. -/
private theorem kyber_length_lt {kp : PQKeyPair} (h : PQKeyPairShape kp) :
    (kp.public_key).key_data.data.length < Usize.max := by
  obtain ⟨-, -, hl, -⟩ := h
  rw [hl]
  rcases Usize.bounds_eq with h | h <;> rw [h] <;> simp only [U32.max, U64.max] <;> scalar_tac

/-- A signature through `signBytes` is an `Ok` value computed by the extracted
`calculate_signature` on a state of `Dom`. If a bound `ε` holds after every such signature, it
holds after `signBytes`. -/
private theorem le_prEvent_signBytes_bind {γ : Type} (P : Params Rand Msg C IdC IdK)
    (hST : SignTotal) (Dom : Rand → Prop)
    (hRng : RngTotal P.cryptoRngInst.RngCoreInst Dom)
    (hSigRng : RngTotal P.rngInst.rand_core_1RngCoreInst Dom)
    (hCoins : ∀ r ∈ support P.coins, Dom r) (sk : ECPriv) (m : Slice U8)
    (k : core.result.Result (Slice U8) libsignal_core.curve.CurveError →
      RustOracleComp unifSpec γ)
    (q : γ → Prop) (ε : ℝ≥0∞)
    (h : ∀ σ r r', Dom r →
      curve.PrivateKey.calculate_signature P.cryptoRngInst P.rngInst sk m r = .ok (.Ok σ, r') →
        ε ≤ Pr{let y ← k (.Ok σ)}[q y]) :
    ε ≤ Pr{let y ← signBytes P sk m >>= k}[q y] := by
  unfold signBytes
  simp only [bind_assoc]
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _ fun r hr => ?_
  rw [ExceptT.support_liftM] at hr
  obtain ⟨⟨res, r'⟩, hsig, hpost⟩ := exists_ok_of_spec
    (hST P.cryptoRngInst P.rngInst Dom hRng hSigRng sk m r (hCoins r hr))
  simp only [WP.uncurry'] at hpost
  obtain ⟨⟨σ, rfl, -⟩, -⟩ := hpost
  simp only [hsig, liftResult_ok, pure_bind]
  exact h σ r r' (hCoins r hr) hsig

/-- Bob selects his own one-time prekey when the initial message carries the prekey's identifier. -/
private theorem selectOPK_publish [DecidableEq IdC] (P : Params Rand Msg C IdC IdK)
    (p : RecipientParameters) (o : Option ECKeyPair) (h : p.opkB = o) :
    selectOPK P p (o.map fun opk => P.idEC opk.public_key) = some o := by
  subst h
  unfold selectOPK
  rcases h : p.opkB with _ | opk <;> simp

open core.result in
/-- The Kyber correctness experiment with encapsulation after `generate`, from the draw of its
generator state `r` on. If `generate` on `r` returns the state `r₁`, encapsulation on `r₁` returns
the secret `ss` and decapsulation of its ciphertext returns `ss'`, the experiment returns `true`
with probability `1` when `ss' = ss` and `0` otherwise. So any `x` that is at least `1` when
`ss' = ss` bounds it. -/
private theorem correctnessTail_le (P : Params Rand Msg C IdC IdK) (kp : PQKeyPair)
    (r r₁ r' : Rand) (ekA : ECKeyPair) (ss ct ss' : Slice U8) (x : ℝ≥0∞)
    (hgen : curve.KeyPair.generate P.rngInst P.cryptoRngInst r = .ok (ekA, r₁))
    (henc : kem.KeyPublic.encapsulate P.cryptoRngInst kp.public_key r₁ = .ok (.Ok (ss, ct), r'))
    (hdec : kem.KeySecret.decapsulate kp.secret_key ct = .ok (.Ok ss')) (h : ss' = ss → 1 ≤ x) :
    Pr{let b ← (do
          let g ← liftResult (curve.KeyPair.generate P.rngInst P.cryptoRngInst r)
          let e ← liftResult (kem.KeyPublic.encapsulate P.cryptoRngInst kp.public_key g.2)
          let p ← (match e.1 with
            | Result.Ok (s, c) => pure (Result.Ok c, Result.Ok s)
            | Result.Err f => pure (Result.Err f, Result.Err f))
          let k' ← (match p.1 with
            | Result.Ok c => do
              let res ← liftResult (kem.KeySecret.decapsulate kp.secret_key c)
              pure (some res)
            | Result.Err _ => pure none)
          pure (decide (k' = some p.2)) : RustOracleComp unifSpec Bool)}[b = true] ≤ x := by
  simp only [hgen, henc, hdec, liftResult_ok, pure_bind]
  rw [prEvent_pure]
  by_cases hss : ss' = ss
  · simpa [hss] using h hss
  · simp [hss]

section Cases

variable [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
  (P : Params Rand Msg C IdC IdK) (msg : Msg) (hasOPK : Bool) (kind : KyberPrekeyKind)
  (hC : CoreContracts) (hST : SignTotal) (hSV : SignVerify) (hG : GenerateTotal)
  (H : crypto.HmacSha256) (hH : crypto.HkdfSha256Contract H)
  (hEC : ∀ kp ∈ support P.ecKeygen, ECKeyPairValid kp)
  (hPQ : ∀ kp ∈ support P.pqKeygen, PQKeyPairShape kp)
  (Dom : Rand → Prop) (hRng : RngTotal P.cryptoRngInst.RngCoreInst Dom)
  (hSigRng : RngTotal P.rngInst.rand_core_1RngCoreInst Dom)
  (hCoins : ∀ r ∈ support P.coins, Dom r) (hAead : AEAD.PerfectlyCorrect P.aead)

include hC hST hSV hG H hH hEC hPQ Dom hRng hSigRng hCoins hAead

/-- The case of `uakeRecipient_agreement_le` for the last-resort Kyber prekey. -/
private theorem uakeRecipient_lastResort_le :
    rustRuntime.evalDist (kyberKemAfterGenerate P).correctnessExperiment {true} ≤
      rustRuntime.evalDist
        (UAKE.agreementExp (uakeRecipient P EntryPoints.extracted msg hasOPK .lastResort))
        {true} := by
  rw [rustRuntime_evalDist_true, rustRuntime_evalDist_true]
  simp only [UAKE.agreementExp, uakeRecipient, setup, recipientNoConfirm, initiatorNoConfirm,
    recipientInit, sessionKyberPrekey, KEMScheme.correctnessExperiment, kyberKemAfterGenerate,
    kyberKem, Party.runHonest,bind_assoc, pure_bind, bind_map_left, Prod.swap_prod_mk]
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _ fun ikA hikA => ?_
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _ fun ikB hikB => ?_
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _ fun spkB hspkB => ?_
  rw [ExceptT.support_liftM] at hikA hikB hspkB
  obtain ⟨b1, he1⟩ := encodeEC_eq spkB.public_key
  rw [he1, pure_bind]
  refine le_prEvent_signBytes_bind P hST Dom hRng hSigRng hCoins _ _ _ _ _
    fun σ1 r1 r1' hr1 hsig1 => ?_
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun kp hkp => ?_
  rw [ExceptT.support_liftM] at hkp
  obtain ⟨b2, he2⟩ := encodeKEM_eq kp.public_key (kyber_length_lt (hPQ _ hkp))
  rw [he2, pure_bind]
  refine le_prEvent_signBytes_bind P hST Dom hRng hSigRng hCoins _ _ _ _ _
    fun σ2 r2 r2' hr2 hsig2 => ?_
  simp only [bind_assoc, pure_bind]
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _ fun opkB hopkB => ?_
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun r hr => ?_
  rw [ExceptT.support_liftM] at hopkB hr
  obtain ⟨⟨ekA, r₁⟩, hgen, hgpost⟩ := exists_ok_of_spec
    (hG P.rngInst P.cryptoRngInst Dom hRng hSigRng r (hCoins r hr))
  simp only [WP.uncurry'] at hgpost
  obtain ⟨hekA, hr₁⟩ := hgpost
  obtain ⟨ss, ct, ss', r', hkA, hkB, henc, hdec, hinit, hacc, hidx, hagree⟩ :=
    honest_run_ok hC H hH P.rngInst P.cryptoRngInst Dom hRng ikA ikB spkB ekA opkB kp r₁
      (hEC _ hikA) (hEC _ hikB) (hEC _ hspkB) hekA (genOPK_valid P hasOPK hEC _ hopkB)
      (hPQ _ hkp) hr₁
  have hv1 :=
    hSV P.cryptoRngInst P.rngInst ikB.private_key ikB.public_key b1 σ1 r1 r1'
      (hEC _ hikB) hsig1
  have hv2 :=
    hSV P.cryptoRngInst P.rngInst ikB.private_key ikB.public_key b2 σ2 r2 r2'
      (hEC _ hikB) hsig2
  refine correctnessTail_le P kp r r₁ r' ekA ss ct ss' _ hgen henc hdec fun hss => ?_
  obtain rfl := hagree hss
  simp only [Party.runHonestStart, Party.InitResult.opening, Party.InitResult.state,
    Party.runHonestLoop]
  simp only [identityKeyOf, identityKeyPairOf] at hinit hacc
  simp only [initiate, publish, identityKeyOf, identityKeyPairOf, he1, he2, verifyBytes, hv1, hv2,
    hgen, EntryPoints.extracted, Option.map_map, Function.comp_def, liftResult_ok, pure_bind,
    bind_assoc, ne_eq, not_true_eq_false, ↓reduceIte, Bool.not_true, Bool.false_eq_true, hinit]
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _ fun ctxt hctxt => ?_
  rw [ExceptT.support_liftM] at hctxt
  have hd := AEAD.decrypt_eq_of_mem_support_encrypt hAead _ _ _ hctxt
  simp only [accept, selectOPK_publish, hacc, hd, liftResult_ok, pure_bind, ne_eq,
    not_true_eq_false, or_self, ↓reduceIte]
  rw [prEvent_pure]
  simp [RecipientState.jointKeys, InitiatorState.jointKeys]

/-- The case of `uakeRecipient_agreement_le` for a one-time Kyber prekey. -/
private theorem uakeRecipient_oneTime_le :
    rustRuntime.evalDist (kyberKemAfterGenerate P).correctnessExperiment {true} ≤
      rustRuntime.evalDist
        (UAKE.agreementExp (uakeRecipient P EntryPoints.extracted msg hasOPK .oneTime)) {true} := by
  rw [rustRuntime_evalDist_true, rustRuntime_evalDist_true]
  simp only [UAKE.agreementExp, uakeRecipient, setup, recipientNoConfirm, initiatorNoConfirm,
    recipientInit, sessionKyberPrekey, KEMScheme.correctnessExperiment, kyberKemAfterGenerate,
    kyberKem, Party.runHonest,bind_assoc, pure_bind, bind_map_left, Prod.swap_prod_mk]
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _ fun ikA hikA => ?_
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _ fun ikB hikB => ?_
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _ fun spkB hspkB => ?_
  rw [ExceptT.support_liftM] at hikA hikB hspkB
  obtain ⟨b1, he1⟩ := encodeEC_eq spkB.public_key
  rw [he1, pure_bind]
  refine le_prEvent_signBytes_bind P hST Dom hRng hSigRng hCoins _ _ _ _ _
    fun σ1 r1 r1' hr1 hsig1 => ?_
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _ fun lr hlr => ?_
  rw [ExceptT.support_liftM] at hlr
  obtain ⟨bl, hel⟩ := encodeKEM_eq lr.public_key (kyber_length_lt (hPQ _ hlr))
  rw [hel, pure_bind]
  refine le_prEvent_signBytes_bind P hST Dom hRng hSigRng hCoins _ _ _ _ _
    fun σl rl rl' hrl hsigl => ?_
  simp only [bind_assoc]
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _ fun opkB hopkB => ?_
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun kp hkp => ?_
  rw [ExceptT.support_liftM] at hkp
  obtain ⟨b2, he2⟩ := encodeKEM_eq kp.public_key (kyber_length_lt (hPQ _ hkp))
  rw [he2, pure_bind]
  refine le_prEvent_signBytes_bind P hST Dom hRng hSigRng hCoins _ _ _ _ _
    fun σ2 r2 r2' hr2 hsig2 => ?_
  simp only [pure_bind]
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun r hr => ?_
  rw [ExceptT.support_liftM] at hopkB hr
  obtain ⟨⟨ekA, r₁⟩, hgen, hgpost⟩ := exists_ok_of_spec
    (hG P.rngInst P.cryptoRngInst Dom hRng hSigRng r (hCoins r hr))
  simp only [WP.uncurry'] at hgpost
  obtain ⟨hekA, hr₁⟩ := hgpost
  obtain ⟨ss, ct, ss', r', hkA, hkB, henc, hdec, hinit, hacc, -, hagree⟩ :=
    honest_run_ok hC H hH P.rngInst P.cryptoRngInst Dom hRng ikA ikB spkB ekA opkB kp r₁
      (hEC _ hikA) (hEC _ hikB) (hEC _ hspkB) hekA (genOPK_valid P hasOPK hEC _ hopkB)
      (hPQ _ hkp) hr₁
  have hv1 :=
    hSV P.cryptoRngInst P.rngInst ikB.private_key ikB.public_key b1 σ1 r1 r1'
      (hEC _ hikB) hsig1
  have hv2 :=
    hSV P.cryptoRngInst P.rngInst ikB.private_key ikB.public_key b2 σ2 r2 r2'
      (hEC _ hikB) hsig2
  refine correctnessTail_le P kp r r₁ r' ekA ss ct ss' _ hgen henc hdec fun hss => ?_
  obtain rfl := hagree hss
  simp only [Party.runHonestStart, Party.InitResult.opening, Party.InitResult.state,
    Party.runHonestLoop]
  simp only [identityKeyOf, identityKeyPairOf] at hinit hacc
  simp only [initiate, publish, identityKeyOf, identityKeyPairOf, he1, he2, verifyBytes, hv1, hv2,
    hgen, EntryPoints.extracted, Option.map_map, Function.comp_def, liftResult_ok, pure_bind,
    bind_assoc, ne_eq, not_true_eq_false, ↓reduceIte, Bool.not_true, Bool.false_eq_true, hinit]
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _ fun ctxt hctxt => ?_
  rw [ExceptT.support_liftM] at hctxt
  have hd := AEAD.decrypt_eq_of_mem_support_encrypt hAead _ _ _ hctxt
  simp only [accept, selectOPK_publish, hacc, hd, liftResult_ok, pure_bind, ne_eq,
    not_true_eq_false, or_self, ↓reduceIte]
  rw [prEvent_pure]
  simp [RecipientState.jointKeys, InitiatorState.jointKeys]

/-- The case of `uakeInitiator_agreement_le` for the last-resort Kyber prekey. -/
private theorem uakeInitiator_lastResort_le :
    rustRuntime.evalDist (kyberKemAfterGenerate P).correctnessExperiment {true} ≤
      rustRuntime.evalDist
        (UAKE.agreementExp (uakeInitiator P EntryPoints.extracted msg hasOPK .lastResort))
        {true} := by
  rw [rustRuntime_evalDist_true, rustRuntime_evalDist_true]
  simp only [UAKE.agreementExp, uakeInitiator, setup, recipient, initiator,
    recipientInit, sessionKyberPrekey, KEMScheme.correctnessExperiment, kyberKemAfterGenerate,
    kyberKem, Party.runHonest,bind_assoc, pure_bind]
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _ fun ikA hikA => ?_
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _ fun ikB hikB => ?_
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _ fun spkB hspkB => ?_
  rw [ExceptT.support_liftM] at hikA hikB hspkB
  obtain ⟨b1, he1⟩ := encodeEC_eq spkB.public_key
  rw [he1, pure_bind]
  refine le_prEvent_signBytes_bind P hST Dom hRng hSigRng hCoins _ _ _ _ _
    fun σ1 r1 r1' hr1 hsig1 => ?_
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun kp hkp => ?_
  rw [ExceptT.support_liftM] at hkp
  obtain ⟨b2, he2⟩ := encodeKEM_eq kp.public_key (kyber_length_lt (hPQ _ hkp))
  rw [he2, pure_bind]
  refine le_prEvent_signBytes_bind P hST Dom hRng hSigRng hCoins _ _ _ _ _
    fun σ2 r2 r2' hr2 hsig2 => ?_
  simp only [bind_assoc, pure_bind]
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun r hr => ?_
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _ fun opkB hopkB => ?_
  rw [ExceptT.support_liftM] at hopkB hr
  obtain ⟨⟨ekA, r₁⟩, hgen, hgpost⟩ := exists_ok_of_spec
    (hG P.rngInst P.cryptoRngInst Dom hRng hSigRng r (hCoins r hr))
  simp only [WP.uncurry'] at hgpost
  obtain ⟨hekA, hr₁⟩ := hgpost
  obtain ⟨ss, ct, ss', r', hkA, hkB, henc, hdec, hinit, hacc, -, hagree⟩ :=
    honest_run_ok hC H hH P.rngInst P.cryptoRngInst Dom hRng ikA ikB spkB ekA opkB kp r₁
      (hEC _ hikA) (hEC _ hikB) (hEC _ hspkB) hekA (genOPK_valid P hasOPK hEC _ hopkB)
      (hPQ _ hkp) hr₁
  have hv1 :=
    hSV P.cryptoRngInst P.rngInst ikB.private_key ikB.public_key b1 σ1 r1 r1'
      (hEC _ hikB) hsig1
  have hv2 :=
    hSV P.cryptoRngInst P.rngInst ikB.private_key ikB.public_key b2 σ2 r2 r2'
      (hEC _ hikB) hsig2
  refine correctnessTail_le P kp r r₁ r' ekA ss ct ss' _ hgen henc hdec fun hss => ?_
  obtain rfl := hagree hss
  simp only [Party.runHonestStart, Party.InitResult.opening, Party.InitResult.state,
    Party.runHonestLoop]
  simp only [identityKeyOf, identityKeyPairOf] at hinit hacc
  simp only [initiate, publish, identityKeyOf, identityKeyPairOf, he1, he2, verifyBytes, hv1, hv2,
    hgen, EntryPoints.extracted, Option.map_map, Function.comp_def, liftResult_ok, pure_bind,
    bind_assoc, ne_eq, not_true_eq_false, ↓reduceIte, Bool.not_true, Bool.false_eq_true, hinit]
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _ fun ctxt hctxt => ?_
  rw [ExceptT.support_liftM] at hctxt
  have hd := AEAD.decrypt_eq_of_mem_support_encrypt hAead _ _ _ hctxt
  simp only [accept, selectOPK_publish, hacc, hd, liftResult_ok, pure_bind, bind_assoc, ne_eq,
    not_true_eq_false, or_self, ↓reduceIte]
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _ fun conf hconf => ?_
  rw [ExceptT.support_liftM] at hconf
  have hd' := AEAD.decrypt_eq_of_mem_support_encrypt hAead _ _ _ hconf
  simp only [confirmOk, hd', decide_true, ↓reduceIte, pure_bind]
  rw [prEvent_pure]
  simp [RecipientState.jointKeys, InitiatorState.jointKeys]

/-- The case of `uakeInitiator_agreement_le` for a one-time Kyber prekey. Alice's draw of her
generator state comes before Bob's draw of the one-time Kyber prekey in the scheme, and after it
in the Kyber experiment, so the proof swaps the two draws in the experiment. -/
private theorem uakeInitiator_oneTime_le :
    rustRuntime.evalDist (kyberKemAfterGenerate P).correctnessExperiment {true} ≤
      rustRuntime.evalDist
        (UAKE.agreementExp (uakeInitiator P EntryPoints.extracted msg hasOPK .oneTime)) {true} := by
  rw [rustRuntime_evalDist_true, rustRuntime_evalDist_true]
  simp only [UAKE.agreementExp, uakeInitiator, setup, recipient, initiator,
    recipientInit, sessionKyberPrekey, KEMScheme.correctnessExperiment, kyberKemAfterGenerate,
    kyberKem, Party.runHonest,bind_assoc, pure_bind]
  rw [prEvent_liftM_bind_liftM_swap]
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _ fun ikA hikA => ?_
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _ fun ikB hikB => ?_
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _ fun spkB hspkB => ?_
  rw [ExceptT.support_liftM] at hikA hikB hspkB
  obtain ⟨b1, he1⟩ := encodeEC_eq spkB.public_key
  rw [he1, pure_bind]
  refine le_prEvent_signBytes_bind P hST Dom hRng hSigRng hCoins _ _ _ _ _
    fun σ1 r1 r1' hr1 hsig1 => ?_
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _ fun lr hlr => ?_
  rw [ExceptT.support_liftM] at hlr
  obtain ⟨bl, hel⟩ := encodeKEM_eq lr.public_key (kyber_length_lt (hPQ _ hlr))
  rw [hel, pure_bind]
  refine le_prEvent_signBytes_bind P hST Dom hRng hSigRng hCoins _ _ _ _ _
    fun σl rl rl' hrl hsigl => ?_
  simp only [bind_assoc]
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun r hr => ?_
  rw [ExceptT.support_liftM] at hr
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _ fun opkB hopkB => ?_
  rw [ExceptT.support_liftM] at hopkB
  refine prEvent_bind_mono_of_forall_le_of_support _ _ _ _ _ fun kp hkp => ?_
  rw [ExceptT.support_liftM] at hkp
  obtain ⟨b2, he2⟩ := encodeKEM_eq kp.public_key (kyber_length_lt (hPQ _ hkp))
  rw [he2, pure_bind]
  refine le_prEvent_signBytes_bind P hST Dom hRng hSigRng hCoins _ _ _ _ _
    fun σ2 r2 r2' hr2 hsig2 => ?_
  simp only [pure_bind]
  obtain ⟨⟨ekA, r₁⟩, hgen, hgpost⟩ := exists_ok_of_spec
    (hG P.rngInst P.cryptoRngInst Dom hRng hSigRng r (hCoins r hr))
  simp only [WP.uncurry'] at hgpost
  obtain ⟨hekA, hr₁⟩ := hgpost
  obtain ⟨ss, ct, ss', r', hkA, hkB, henc, hdec, hinit, hacc, -, hagree⟩ :=
    honest_run_ok hC H hH P.rngInst P.cryptoRngInst Dom hRng ikA ikB spkB ekA opkB kp r₁
      (hEC _ hikA) (hEC _ hikB) (hEC _ hspkB) hekA (genOPK_valid P hasOPK hEC _ hopkB)
      (hPQ _ hkp) hr₁
  have hv1 :=
    hSV P.cryptoRngInst P.rngInst ikB.private_key ikB.public_key b1 σ1 r1 r1'
      (hEC _ hikB) hsig1
  have hv2 :=
    hSV P.cryptoRngInst P.rngInst ikB.private_key ikB.public_key b2 σ2 r2 r2'
      (hEC _ hikB) hsig2
  refine correctnessTail_le P kp r r₁ r' ekA ss ct ss' _ hgen henc hdec fun hss => ?_
  obtain rfl := hagree hss
  simp only [Party.runHonestStart, Party.InitResult.opening, Party.InitResult.state,
    Party.runHonestLoop]
  simp only [identityKeyOf, identityKeyPairOf] at hinit hacc
  simp only [initiate, publish, identityKeyOf, identityKeyPairOf, he1, he2, verifyBytes, hv1, hv2,
    hgen, EntryPoints.extracted, Option.map_map, Function.comp_def, liftResult_ok, pure_bind,
    bind_assoc, ne_eq, not_true_eq_false, ↓reduceIte, Bool.not_true, Bool.false_eq_true, hinit]
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _ fun ctxt hctxt => ?_
  rw [ExceptT.support_liftM] at hctxt
  have hd := AEAD.decrypt_eq_of_mem_support_encrypt hAead _ _ _ hctxt
  simp only [accept, selectOPK_publish, hacc, hd, liftResult_ok, pure_bind, bind_assoc, ne_eq,
    not_true_eq_false, or_self, ↓reduceIte]
  refine le_prEvent_bind_of_forall_le_of_support _ (prEvent_true_liftM _) _ _ fun conf hconf => ?_
  rw [ExceptT.support_liftM] at hconf
  have hd' := AEAD.decrypt_eq_of_mem_support_encrypt hAead _ _ _ hconf
  simp only [confirmOk, hd', decide_true, ↓reduceIte, pure_bind]
  rw [prEvent_pure]
  simp [RecipientState.jointKeys, InitiatorState.jointKeys]

/-- In an honest run of `uakeInitiator` on the extracted entry points, with Bob's sessions using
Kyber prekeys of the kind `kind`, both parties output equal keys at least as often as the Kyber
correctness experiment with encapsulation after `generate` succeeds. -/
theorem uakeInitiator_agreement_le :
    rustRuntime.evalDist (kyberKemAfterGenerate P).correctnessExperiment {true} ≤
      rustRuntime.evalDist
        (UAKE.agreementExp (uakeInitiator P EntryPoints.extracted msg hasOPK kind)) {true} := by
  cases kind
  · apply uakeInitiator_oneTime_le <;> assumption
  · apply uakeInitiator_lastResort_le <;> assumption

/-- In an honest run of `uakeRecipient` on the extracted entry points, with Bob's sessions using
Kyber prekeys of the kind `kind`, both parties output equal keys at least as often as the Kyber
correctness experiment with encapsulation after `generate` succeeds. -/
theorem uakeRecipient_agreement_le :
    rustRuntime.evalDist (kyberKemAfterGenerate P).correctnessExperiment {true} ≤
      rustRuntime.evalDist
        (UAKE.agreementExp (uakeRecipient P EntryPoints.extracted msg hasOPK kind)) {true} := by
  cases kind
  · apply uakeRecipient_oneTime_le <;> assumption
  · apply uakeRecipient_lastResort_le <;> assumption

end Cases

end

end Protocols.PQXDH
