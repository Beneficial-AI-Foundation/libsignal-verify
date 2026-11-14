/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import Protocols.Models.PQXDH.UAKE.SecurityLemmas.Games
import Protocols.Models.PQXDH.UAKE.SecurityLemmas.KeyGuessing
import Protocols.Models.PQXDH.UAKE.SecurityLemmas.SigReduction

/-!
# Shared Security Hops

Hops 1 through 4 of the security proofs, used by both the DH and the PQ
security theorems in `Security.lean`: the forgery/indistinguishability
split, the union bound over forgery causes, the joint unforgeability
reduction, and the KEM public-key guessing bound. See `SecurityLemmas.lean`
for the overall map.

The lemma statements and proofs in this file are AI-written.
-/

open OracleSpec OracleComp AKE AKE.UAKE
open scoped ENNReal

namespace Protocols.Models.PQXDH

variable {F G SS PQPK PQSK CT S C Msg K IdC IdK : Type}
  [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
  [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
  [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
  [SampleableType K]
  (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)

/-- One-point union bound: if the Boolean `a` implies `b || (c || d)`, the
  probability that a deterministic run returns `a = true` is at most the sum
  of the probabilities for `b`, `c`, and `d`. -/
private lemma probOutput_pure_le_add3 {a b c d : Bool}
    (h : a = true → (b || (c || d)) = true) :
    Pr{let y ← (pure a : ProbComp Bool)}[y = true] ≤
      Pr{let y ← (pure b : ProbComp Bool)}[y = true] +
        Pr{let y ← (pure c : ProbComp Bool)}[y = true] +
        Pr{let y ← (pure d : ProbComp Bool)}[y = true] := by
  cases a with
  | false => simp
  | true =>
    rcases (by simpa using h rfl : b = true ∨ c = true ∨ d = true) with hb | hc | hd
    · rw [hb]; exact le_add_right (le_add_right le_rfl)
    · rw [hc]; exact le_add_right (le_add_left le_rfl)
    · rw [hd]; exact le_add_left le_rfl

omit [SampleableType K] in
/-- Case split behind the Hop 2 union bound: on a forgery run, either the
  accepted bundle carries a signed pair the challenger never produced, or
  the KEM-key bad event occurred, or the run is a residual forgery with an
  honest bundle and separated KEM keys. -/
private lemma forge_or_cases (tk : RecipientIdentity F G S)
    (env : Env (uakeInitiator P msg hasOPK))
    (cr : ChallengeResult (uakeInitiator P msg hasOPK))
    (h : (cr.K0.isSome && !challengePartnered P msg hasOPK cr env) = true) :
    ((cr.K0.isSome && (challengeBundle P msg hasOPK cr).any fun b =>
        !honestBundle P msg hasOPK tk cr b) ||
      (pqpkGuessed P msg hasOPK cr ||
        (cr.K0.isSome && !challengePartnered P msg hasOPK cr env &&
          ((challengeBundle P msg hasOPK cr).all fun b =>
            honestBundle P msg hasOPK tk cr b) &&
          !pqpkGuessed P msg hasOPK cr))) = true := by
  cases hg : pqpkGuessed P msg hasOPK cr
  · rcases hb : challengeBundle P msg hasOPK cr with _ | b
    · simp_all
    · cases hh : honestBundle P msg hasOPK tk cr b <;> simp_all
  · simp

/-- Hop 1: the partnered experiment `PartneredExp` over `originalKeyPartnering` and `indistExp`
  agree except on the forgery branch, where Alice accepts with no original-key partner: the
  former returns `true` and the latter flips a fair coin. After commuting the challenge bit ahead
  of the challenge phase, the two experiments share their sampling prefix, so `PartneredExp`'s
  success probability lies between `indistExp`'s and `indistExp`'s plus the forgery probability,
  and the triangle inequality bounds the partnered advantage by `forgeProb` plus
  `indistAdvantage`. Purely probabilistic; uses no cryptographic hypotheses. -/
lemma advantage_le_forgeProb_add_indistAdvantage
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    partneredAdvantage ProbCompRuntime.probComp (originalKeyPartnering P msg hasOPK) A ≤
      forgeProb P msg hasOPK A + indistAdvantage P msg hasOPK A := by
  have hswapE : Pr{let y ← (PartneredExp ProbCompRuntime.probComp.toProbCompLift
        (originalKeyPartnering P msg hasOPK) A)}[y = true] =
      Pr{let y ← (do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let (cr, st) ← challengePhase P msg hasOPK A
        if cr.K0.isNone then
          finalizePartnered ProbCompRuntime.probComp.toProbCompLift
            (originalKeyPartnering P msg hasOPK) A st cr b none
        else if !challengePartnered P msg hasOPK cr st.2.1 then
          return true
        else do
          let K1 ← some <$> ($ᵗ K)
          finalizePartnered ProbCompRuntime.probComp.toProbCompLift
            (originalKeyPartnering P msg hasOPK) A st cr b K1 :
        ProbComp Bool)}[y = true] := by
    rw [PartneredExp, challengePhase]
    simp only [bind_assoc, map_bind]
    exact prEvent_bind_bind_swap_of_uniform _ _ _
  have hswapI : Pr{let y ← (indistExp P msg hasOPK A)}[y = true] =
      Pr{let y ← (do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let (cr, st) ← challengePhase P msg hasOPK A
        if cr.K0.isNone then
          finalizePartnered ProbCompRuntime.probComp.toProbCompLift
            (originalKeyPartnering P msg hasOPK) A st cr b none
        else if !challengePartnered P msg hasOPK cr st.2.1 then
          $ᵗ Bool
        else do
          let K1 ← some <$> ($ᵗ K)
          finalizePartnered ProbCompRuntime.probComp.toProbCompLift
            (originalKeyPartnering P msg hasOPK) A st cr b K1 :
        ProbComp Bool)}[y = true] := by
    rw [indistExp, challengePhase]
    simp only [bind_assoc, map_bind]
    exact prEvent_bind_bind_swap_of_uniform _ _ _
  have hEI : Pr{let y ← (indistExp P msg hasOPK A)}[y = true] ≤
      Pr{let y ← (PartneredExp ProbCompRuntime.probComp.toProbCompLift
        (originalKeyPartnering P msg hasOPK) A)}[y = true] := by
    rw [hswapI, hswapE]
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun b => ?_
    refine prEvent_bind_mono_of_forall_le _ _ _ _ _ fun x => ?_
    obtain ⟨cr, st⟩ := x
    rcases hk : cr.K0 with _ | k
    · simp [hk]
    · cases hp : challengePartnered P msg hasOPK cr st.2.1 <;>
        simp [hk, hp, Finset.filter_insert, Finset.filter_singleton]
  have hIE : Pr{let y ← (PartneredExp ProbCompRuntime.probComp.toProbCompLift
        (originalKeyPartnering P msg hasOPK) A)}[y = true] ≤
      Pr{let y ← (indistExp P msg hasOPK A)}[y = true] +
        Pr{let y ← (forgeExp P msg hasOPK A)}[y = true] := by
    have hcoin : Pr{let y ← (forgeExp P msg hasOPK A)}[y = true] =
        Pr{let y ← (($ᵗ Bool : ProbComp Bool) >>= fun _ => forgeExp P msg hasOPK A)}[y = true] := by
      simp only [map_bind]
      exact (OracleComp.prEvent_bind_const _ _).symm
    rw [hswapE, hswapI, hcoin]
    refine prEvent_bind_le_add_of_forall_le _ _ _ _ _ _ _ fun b => ?_
    simp only [forgeExp]
    refine prEvent_bind_le_add_of_forall_le _ _ _ _ _ _ _ fun x => ?_
    obtain ⟨cr, st⟩ := x
    rcases _hk : cr.K0 with _ | k
    · simp
    · cases _hp : challengePartnered P msg hasOPK cr st.2.1 <;> simp
  have h1 : (Pr{let y ← (indistExp P msg hasOPK A)}[y = true]).toReal ≤
      (Pr{let y ← (PartneredExp ProbCompRuntime.probComp.toProbCompLift
        (originalKeyPartnering P msg hasOPK) A)}[y = true]).toReal :=
    ENNReal.toReal_mono (prEvent_ne_top _) hEI
  have h2 : (Pr{let y ← (PartneredExp ProbCompRuntime.probComp.toProbCompLift
        (originalKeyPartnering P msg hasOPK) A)}[y = true]).toReal ≤
      (Pr{let y ← (indistExp P msg hasOPK A)}[y = true]).toReal +
        (Pr{let y ← (forgeExp P msg hasOPK A)}[y = true]).toReal := by
    have h := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨prEvent_ne_top _, prEvent_ne_top _⟩) hIE
    rwa [ENNReal.toReal_add (prEvent_ne_top _) (prEvent_ne_top _)] at h
  rw [partneredAdvantage, probOutput_probComp_evalDist, forgeProb, indistAdvantage,
    ← prEvent_eq_evalDist_singleton]
  calc |(Pr{let y ← (PartneredExp ProbCompRuntime.probComp.toProbCompLift
          (originalKeyPartnering P msg hasOPK) A)}[y = true]).toReal - 1 / 2|
      ≤ |(Pr{let y ← (PartneredExp ProbCompRuntime.probComp.toProbCompLift
            (originalKeyPartnering P msg hasOPK) A)}[y = true]).toReal -
          (Pr{let y ← (indistExp P msg hasOPK A)}[y = true]).toReal| +
        |(Pr{let y ← (indistExp P msg hasOPK A)}[y = true]).toReal - 1 / 2| := abs_sub_le _ _ _
    _ ≤ (Pr{let y ← (forgeExp P msg hasOPK A)}[y = true]).toReal +
        |(Pr{let y ← (indistExp P msg hasOPK A)}[y = true]).toReal - 1 / 2| := by
      have habs := abs_of_nonneg (sub_nonneg.mpr h1)
      linarith

omit [SampleableType K] in
/-- Hop 2 (union bound): on any completed challenge run without an original-key partner,
  either some signed key of the accepted bundle was never signed by the challenger
  (`sigForgeExp`), or the KEM-key bad event occurred (`pqpkGuessedExp`), or
  the forgery happened with an honest bundle and separated KEM keys
  (`forgeHonestGoodExp`). Purely probabilistic; uses no cryptographic
  hypotheses. -/
lemma forgeProb_le_sigForge_add_pqpkGuessed_add_forgeHonestGood
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    forgeProb P msg hasOPK A ≤ sigForgeProb P msg hasOPK A +
      pqpkGuessedProb P msg hasOPK A + forgeHonestGoodProb P msg hasOPK A := by
  have key : Pr{let y ← (forgeExp P msg hasOPK A)}[y = true] ≤
      Pr{let y ← (sigForgeExp P msg hasOPK A)}[y = true] + Pr{let y ← (pqpkGuessedExp P msg hasOPK A)}[y = true] +
        Pr{let y ← (forgeHonestGoodExp P msg hasOPK A)}[y = true] := by
    simp only [forgeExp, sigForgeExp, pqpkGuessedExp, forgeHonestGoodExp]
    let : MeasurableSpace (ChallengeResult (uakeInitiator P msg hasOPK) ×
      (A.State × Env (uakeInitiator P msg hasOPK) × RecipientIdentity F G S)) := ⊤
    rw [prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete,
      prEvent_bind_eq_lintegral_of_discrete, prEvent_bind_eq_lintegral_of_discrete,
      ← MeasureTheory.lintegral_add_left Measurable.of_discrete,
      ← MeasureTheory.lintegral_add_left Measurable.of_discrete]
    refine MeasureTheory.lintegral_mono fun x => ?_
    obtain ⟨cr, st⟩ := x
    exact probOutput_pure_le_add3 (forge_or_cases P msg hasOPK st.2.2 st.2.1 cr)
  have h2 : Pr{let y ← (sigForgeExp P msg hasOPK A)}[y = true] +
      Pr{let y ← (pqpkGuessedExp P msg hasOPK A)}[y = true] ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨prEvent_ne_top _, prEvent_ne_top _⟩
  have h3 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨h2, prEvent_ne_top _⟩) key
  rwa [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨prEvent_ne_top _, prEvent_ne_top _⟩)
    (prEvent_ne_top _), ENNReal.toReal_add (prEvent_ne_top _) (prEvent_ne_top _)] at h3

omit [DecidableEq CT] [DecidableEq S] [DecidableEq C] [SampleableType K] in
/-- Hop 3 (joint EUF-CMA): a signature forgery in the challenge phase yields a forgery
against `P.sig` in the joint EUF-CMA game of the identity key.

The joint game gives the adversary signing and agreement queries `Y ↦ DH x Y` on one identity
key pair. It wins with a valid signature on a message that it never had signed. With deterministic
verification (`hverifyDet`), the advantage of `SigReduction.sigAdversary` is at least
`sigForgeProb`, the probability of the signature forgery event. That event compares signed keys,
so a different valid signature on a signed key is not a forgery.

The premise `hsig` states joint EUF-CMA of the identity key. It bounds adversaries without a
resource limit (#41), so the statement does not yet say anything about efficient adversaries. The
reduction makes one signing query for `setup` and one for each `openT` query, and one agreement
query for each `stepT` query that reaches `DH2`. A rejected `stepT` query leaves the session open
for another try, so the number of agreement queries is not bounded by the number of sessions.

Used by `uakeInitiator_secure_dh` and `uakeInitiator_secure_pq` as hop 3. -/
lemma sigForgeProb_le_sig [Inhabited F]
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (εsig : ℝ)
    (hverifyDet : ∀ (pk : G) (m : G ⊕ PQPK) (σ : S), ∃ b, P.sig.verify pk m σ = pure b)
    (hsig : ∀ B : P.sig.JointAdversary (DH : F → G → G), B.advantage.toReal ≤ εsig) :
    sigForgeProb P msg hasOPK A ≤ εsig :=
  (SigReduction.sigForgeProb_le_advantage_sigAdversary P msg hasOPK A hverifyDet).trans
    (hsig _)

omit [DecidableEq CT] [DecidableEq S] [DecidableEq C] [SampleableType K] in
/-- Hop 4 (KEM-key guessing): if `A.OpensAtMost q` and every public-key output of
  `P.pqkem.keygen` has probability at most `εpk`, then
  `pqpkGuessedProb P msg hasOPK A ≤ (q : ℝ) ^ 2 * εpk`. The statement needs no
  `SampleableType K` instance.

  Used by `uakeInitiator_secure_dh` and `uakeInitiator_secure_pq` as hop 4. -/
lemma pqpkGuessedProb_le
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εpk : ℝ)
    (hpk : ∀ pk : PQPK, (Pr{let y ← (Prod.fst <$> P.pqkem.keygen)}[y = pk]).toReal ≤ εpk) :
    pqpkGuessedProb P msg hasOPK A ≤ (q : ℝ) ^ 2 * εpk := by
  -- Each T session draws its KEM public key afresh from `P.pqkem.keygen`, after the keys of the
  -- earlier sessions and the key of any bundle the challenge has accepted are fixed. So the draw
  -- of the `j`-th session hits one of at most `j` known keys with probability at most `j * εpk`.
  -- `KeyGuessing.probEvent_badEnv_le` bounds the simulated challenge stage by the potential
  -- `εpk * b * (n + b)` for `n` open sessions and `b` remaining openings. That is `εpk * q ^ 2`
  -- at the start. Only the challenge-stage half of `hq` is used.
  have hε0 : 0 ≤ εpk := nonneg_of_probOutput_le _ hpk
  have hpk' : ∀ pk, Pr{let y ← (Prod.fst <$> P.pqkem.keygen)}[y = pk] ≤
      ENNReal.ofReal εpk := fun pk =>
    (ENNReal.le_ofReal_iff_toReal_le (by finiteness) hε0).2 (hpk pk)
  have key : Pr{let y ← (pqpkGuessedExp P msg hasOPK A)}[y = true] ≤
      ENNReal.ofReal εpk * ((q * q : ℕ) : ℝ≥0∞) := by
    simp only [pqpkGuessedExp, challengePhase, bind_assoc]
    refine prEvent_bind_le_of_forall_le _ _ _ fun ukt => ?_
    have hinit : (uakeInitiator P msg hasOPK).U.init ukt.1 = pure (.waitForMsg (.inl ukt.1)) :=
      rfl
    simp only [challengeSession, bind_assoc, hinit, pure_bind, Party.InitResult.opening,
      Party.InitResult.state, recordOpt]
    refine (prEvent_bind_le_prEvent_of_forall_eq_zero _ _
      (fun z => KeyGuessing.badEnv P msg hasOPK z.2 = true) _
      fun z hz => le_antisymm (prEvent_bind_le_of_forall_le _ _ _ fun k0 => ?_) zero_le).trans ?_
    · have hk : pqpkGuessed P msg hasOPK
          ⟨k0.join, z.2.challenge.transcript, z.2.tSessions.map (·.transcript)⟩ =
            KeyGuessing.badEnv P msg hasOPK z.2 := rfl
      simp [hk, hz]
    · refine (KeyGuessing.probEvent_badEnv_le P msg hasOPK ukt.2 _ hpk' ?_ _ q (hq.1 _ _) _
        ?_).trans ?_
      · intro t
        rcases t with n | op
        · simp
        · cases op <;> simp
      · intro s hs
        simp at hs
      · simp [KeyGuessing.badEnv, KeyGuessing.envResult, pqpkGuessed, oracleBundles,
          challengeBundle, transcriptBundle]
  have hfin : ENNReal.ofReal εpk * ((q * q : ℕ) : ℝ≥0∞) ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.natCast_ne_top _)
  calc pqpkGuessedProb P msg hasOPK A
      ≤ (ENNReal.ofReal εpk * ((q * q : ℕ) : ℝ≥0∞)).toReal := ENNReal.toReal_mono hfin key
    _ = (q : ℝ) ^ 2 * εpk := by
      rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hε0, ENNReal.toReal_natCast]
      push_cast
      ring

end Protocols.Models.PQXDH
