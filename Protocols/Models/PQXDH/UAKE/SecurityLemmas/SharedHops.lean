/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import Protocols.Models.PQXDH.UAKE.SecurityLemmas.Games
import Protocols.Models.PQXDH.UAKE.SecurityLemmas.KeyGuessing

/-!
# Shared Security Hops

Hops 1 through 4 of the security proofs, used by both the DH and the PQ
security theorems in `Security.lean`: the forgery/indistinguishability
split, the union bound over forgery causes, the SUF-CMA reduction, and the
KEM public-key guessing bound. See `SecurityLemmas.lean` for the overall
map.

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
    Pr[= true | (pure a : ProbComp Bool)] ≤
      Pr[= true | (pure b : ProbComp Bool)] + Pr[= true | (pure c : ProbComp Bool)] +
        Pr[= true | (pure d : ProbComp Bool)] := by
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
    (cr : ChallengeResult (uakeInitiator P msg hasOPK))
    (h : (cr.K0.isSome && !isPingPong cr) = true) :
    ((cr.K0.isSome && (challengeBundle P msg hasOPK cr).any fun b =>
        !honestBundle P msg hasOPK tk cr b) ||
      (pqpkGuessed P msg hasOPK cr ||
        (cr.K0.isSome && !isPingPong cr &&
          ((challengeBundle P msg hasOPK cr).all fun b =>
            honestBundle P msg hasOPK tk cr b) &&
          !pqpkGuessed P msg hasOPK cr))) = true := by
  cases hg : pqpkGuessed P msg hasOPK cr
  · rcases hb : challengeBundle P msg hasOPK cr with _ | b
    · simp_all
    · cases hh : honestBundle P msg hasOPK tk cr b <;> simp_all
  · simp

/-- Hop 1: `UAKE.Exp` and `indistExp` agree except on the forgery branch,
  where the former returns `true` and the latter flips a fair coin. After
  commuting the challenge bit ahead of the challenge phase, the two
  experiments share their sampling prefix, so `UAKE.Exp`'s success
  probability lies between `indistExp`'s and `indistExp`'s plus the forgery
  probability, and the triangle inequality bounds the UAKE advantage by
  `forgeProb` plus `indistAdvantage`. Purely probabilistic; uses no
  cryptographic hypotheses. -/
lemma advantage_le_forgeProb_add_indistAdvantage
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    UAKE.advantage ProbCompRuntime.probComp A ≤
      forgeProb P msg hasOPK A + indistAdvantage P msg hasOPK A := by
  have hswapE : Pr[= true | UAKE.Exp ProbCompRuntime.probComp.toProbCompLift A] =
      Pr[= true | (do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let (cr, st) ← challengePhase P msg hasOPK A
        if cr.K0.isNone then
          finalize ProbCompRuntime.probComp.toProbCompLift A st cr b none
        else if !isPingPong cr then
          return true
        else do
          let K1 ← some <$> ($ᵗ K)
          finalize ProbCompRuntime.probComp.toProbCompLift A st cr b K1 :
        ProbComp Bool)] := by
    rw [UAKE.Exp, challengePhase]
    simp only [bind_assoc]
    exact probOutput_bind_bind_swap _ _ _ _
  have hswapI : Pr[= true | indistExp P msg hasOPK A] =
      Pr[= true | (do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let (cr, st) ← challengePhase P msg hasOPK A
        if cr.K0.isNone then
          finalize ProbCompRuntime.probComp.toProbCompLift A st cr b none
        else if !isPingPong cr then
          $ᵗ Bool
        else do
          let K1 ← some <$> ($ᵗ K)
          finalize ProbCompRuntime.probComp.toProbCompLift A st cr b K1 :
        ProbComp Bool)] := by
    rw [indistExp, challengePhase]
    simp only [bind_assoc]
    exact probOutput_bind_bind_swap _ _ _ _
  have hEI : Pr[= true | indistExp P msg hasOPK A] ≤
      Pr[= true | UAKE.Exp ProbCompRuntime.probComp.toProbCompLift A] := by
    rw [hswapI, hswapE]
    refine probOutput_bind_mono fun b _ => ?_
    refine probOutput_bind_mono fun x _ => ?_
    obtain ⟨cr, st⟩ := x
    rcases hk : cr.K0 with _ | k
    · simp [hk]
    · cases hp : isPingPong cr <;> simp [hk, hp]
  have hIE : Pr[= true | UAKE.Exp ProbCompRuntime.probComp.toProbCompLift A] ≤
      Pr[= true | indistExp P msg hasOPK A] + Pr[= true | forgeExp P msg hasOPK A] := by
    have hcoin : Pr[= true | forgeExp P msg hasOPK A] =
        Pr[= true | ($ᵗ Bool : ProbComp Bool) >>= fun _ => forgeExp P msg hasOPK A] := by
      rw [probOutput_bind_const, probFailure_uniformSample, tsub_zero, one_mul]
    rw [hswapE, hswapI, hcoin]
    refine probOutput_bind_congr_le_add fun b _ => ?_
    simp only [forgeExp]
    refine probOutput_bind_congr_le_add fun x _ => ?_
    obtain ⟨cr, st⟩ := x
    rcases _hk : cr.K0 with _ | k
    · simp
    · cases _hp : isPingPong cr <;> simp
  have h1 : (Pr[= true | indistExp P msg hasOPK A]).toReal ≤
      (Pr[= true | UAKE.Exp ProbCompRuntime.probComp.toProbCompLift A]).toReal :=
    ENNReal.toReal_mono probOutput_ne_top hEI
  have h2 : (Pr[= true | UAKE.Exp ProbCompRuntime.probComp.toProbCompLift A]).toReal ≤
      (Pr[= true | indistExp P msg hasOPK A]).toReal +
        (Pr[= true | forgeExp P msg hasOPK A]).toReal := by
    have h := ENNReal.toReal_mono
      (ENNReal.add_ne_top.mpr ⟨probOutput_ne_top, probOutput_ne_top⟩) hIE
    rwa [ENNReal.toReal_add probOutput_ne_top probOutput_ne_top] at h
  rw [UAKE.advantage, probOutput_probComp_evalDist, forgeProb, indistAdvantage]
  calc |(Pr[= true | UAKE.Exp ProbCompRuntime.probComp.toProbCompLift A]).toReal - 1 / 2|
      ≤ |(Pr[= true | UAKE.Exp ProbCompRuntime.probComp.toProbCompLift A]).toReal -
          (Pr[= true | indistExp P msg hasOPK A]).toReal| +
        |(Pr[= true | indistExp P msg hasOPK A]).toReal - 1 / 2| := abs_sub_le _ _ _
    _ ≤ (Pr[= true | forgeExp P msg hasOPK A]).toReal +
        |(Pr[= true | indistExp P msg hasOPK A]).toReal - 1 / 2| := by
      have habs := abs_of_nonneg (sub_nonneg.mpr h1)
      linarith

omit [SampleableType K] in
/-- Hop 2 (union bound): on any completed challenge run, either some signed
  pair of the accepted bundle was never produced by the challenger
  (`sigForgeExp`), or the KEM-key bad event occurred (`pqpkGuessedExp`), or
  the forgery happened with an honest bundle and separated KEM keys
  (`forgeHonestGoodExp`). Purely probabilistic; uses no cryptographic
  hypotheses. -/
lemma forgeProb_le_sigForge_add_pqpkGuessed_add_forgeHonestGood
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) :
    forgeProb P msg hasOPK A ≤ sigForgeProb P msg hasOPK A +
      pqpkGuessedProb P msg hasOPK A + forgeHonestGoodProb P msg hasOPK A := by
  have key : Pr[= true | forgeExp P msg hasOPK A] ≤
      Pr[= true | sigForgeExp P msg hasOPK A] + Pr[= true | pqpkGuessedExp P msg hasOPK A] +
        Pr[= true | forgeHonestGoodExp P msg hasOPK A] := by
    simp only [forgeExp, sigForgeExp, pqpkGuessedExp, forgeHonestGoodExp,
      probOutput_bind_eq_tsum]
    rw [← ENNReal.tsum_add, ← ENNReal.tsum_add]
    refine ENNReal.tsum_le_tsum fun x => ?_
    rw [← left_distrib, ← left_distrib]
    refine mul_le_mul' le_rfl ?_
    obtain ⟨cr, st⟩ := x
    exact probOutput_pure_le_add3 (forge_or_cases P msg hasOPK st.2.2 cr)
  have h2 : Pr[= true | sigForgeExp P msg hasOPK A] +
      Pr[= true | pqpkGuessedExp P msg hasOPK A] ≠ ⊤ :=
    ENNReal.add_ne_top.mpr ⟨probOutput_ne_top, probOutput_ne_top⟩
  have h3 := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨h2, probOutput_ne_top⟩) key
  rwa [ENNReal.toReal_add (ENNReal.add_ne_top.mpr ⟨probOutput_ne_top, probOutput_ne_top⟩)
    probOutput_ne_top, ENNReal.toReal_add probOutput_ne_top probOutput_ne_top] at h3

omit [DecidableEq CT] [DecidableEq C] in
/-- Hop 3 (SUF-CMA): a signature forgery in the challenge phase yields a
  strong existential forgery against `P.sig`.

  Ported reduction outline: the SUF-CMA adversary simulates the challenge phase,
  substituting its challenge public key for `ikB.1` and its signing oracle
  for the two uses of `P.sig.sign` (setup's pre-key signature and each
  session's KEM-key signature). When the challenge session completes, it stops
  and outputs the accepted bundle's signed pair that `honestBundle` fails,
  so the pair was not returned by any signing query. Determinism of
  verification (`hverifyDet`) transfers the initiator's successful
  verification of that pair to the SUF-CMA experiment's final check.
  Strong unforgeability (rather than EUF-CMA) is needed because `setup` and
  `publish` sign only two message forms, so a dishonest bundle may reuse an
  honestly signed message with a fresh signature.

  With the single identity key this outline is incomplete. Each T-session's
  `accept` also computes `DH p.ikB.2 msg.ekA` on the adversary's ephemeral key,
  and the SUF-CMA game has no query that answers this. The statement still
  holds, because `hsig` bounds adversaries without a resource limit (#41): an
  adversary that makes no query and outputs some valid pair for its public key
  wins with at least the probability of `sigForgeExp`. So the statement says
  nothing about efficient adversaries. Its intended replacement premise is
  joint unforgeability of the identity key: signing queries and agreement
  queries `Y ↦ DH x Y` on the one key pair, with a win on a valid signature of a
  message that was never signed. With that premise the forgery event compares
  signed keys, not signature bytes, because XEdDSA signatures are malleable.

  Used by `uakeInitiator_secure_dh` and `uakeInitiator_secure_pq` as hop 3. -/
lemma sigForgeProb_le_sig [Inhabited S] [Inhabited F]
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (εsig : ℝ)
    (hverifyDet : ∀ (pk : G) (m : G ⊕ PQPK) (σ : S), ∃ b, P.sig.verify pk m σ = pure b)
    (hsig : ∀ B : P.sig.unforgeableAdv,
      (B.strongAdvantage ProbCompRuntime.probComp).toReal ≤ εsig) :
    sigForgeProb P msg hasOPK A ≤ εsig := by
  sorry

omit [DecidableEq CT] [DecidableEq S] [DecidableEq C] [SampleableType K] in
/-- Hop 4 (KEM-key guessing): if `A.OpensAtMost q` and every public-key output of
  `P.pqkem.keygen` has probability at most `εpk`, then
  `pqpkGuessedProb P msg hasOPK A ≤ (q : ℝ) ^ 2 * εpk`. The statement needs no
  `SampleableType K` instance.

  Used by `uakeInitiator_secure_dh` and `uakeInitiator_secure_pq` as hop 4. -/
lemma pqpkGuessedProb_le
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εpk : ℝ)
    (hpk : ∀ pk : PQPK, (Pr[= pk | Prod.fst <$> P.pqkem.keygen]).toReal ≤ εpk) :
    pqpkGuessedProb P msg hasOPK A ≤ (q : ℝ) ^ 2 * εpk := by
  -- Each T session draws its KEM public key afresh from `P.pqkem.keygen`, after the keys of the
  -- earlier sessions and the key of any bundle the challenge has accepted are fixed. So the draw
  -- of the `j`-th session hits one of at most `j` known keys with probability at most `j * εpk`.
  -- `KeyGuessing.probEvent_badEnv_le` bounds the simulated challenge stage by the potential
  -- `εpk * b * (n + b)` for `n` open sessions and `b` remaining openings. That is `εpk * q ^ 2`
  -- at the start. Only the challenge-stage half of `hq` is used.
  have hε0 : 0 ≤ εpk := nonneg_of_probOutput_le _ hpk
  have hpk' : ∀ pk, Pr[= pk | Prod.fst <$> P.pqkem.keygen] ≤ ENNReal.ofReal εpk := fun pk =>
    (ENNReal.le_ofReal_iff_toReal_le probOutput_ne_top hε0).2 (hpk pk)
  have key : Pr[= true | pqpkGuessedExp P msg hasOPK A] ≤
      ENNReal.ofReal εpk * ((q * q : ℕ) : ℝ≥0∞) := by
    rw [← probEvent_eq_eq_probOutput]
    simp only [pqpkGuessedExp, challengePhase, bind_assoc]
    refine probEvent_bind_le_of_forall_le fun ukt _ => ?_
    have hinit : (uakeInitiator P msg hasOPK).U.init ukt.1 = pure (.waitForMsg (.inl ukt.1)) :=
      rfl
    simp only [challengeSession, bind_assoc, hinit, pure_bind, Party.InitResult.opening,
      Party.InitResult.state, recordOpt]
    refine (probEvent_bind_le_probEvent
      (p := fun z => KeyGuessing.badEnv P msg hasOPK z.2 = true)
      fun z _ hz => le_antisymm (probEvent_bind_le_of_forall_le fun k0 _ => ?_) zero_le).trans ?_
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
