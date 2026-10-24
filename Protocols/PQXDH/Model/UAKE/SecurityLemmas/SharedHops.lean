/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import Protocols.PQXDH.Model.UAKE.SecurityLemmas.Games

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

namespace Protocols.PQXDH

variable {F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK : Type}
  [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
  [DecidableEq G] [DecidableEq PQPK] [DecidableEq CT] [DecidableEq S] [DecidableEq C]
  [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
  [SampleableType K]
  (P : Parameters F G SS PQPK PQSK CT SPK SSK S C Msg K IdC IdK) (msg : Msg) (hasOPK : Bool)

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
private lemma forge_or_cases (tk : RecipientIdentity F G SPK SSK S)
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

  Intended reduction: the SUF-CMA adversary simulates the challenge phase,
  substituting its challenge public key for `sigkB.1` and its signing oracle
  for the two uses of `P.sig.sign` (setup's pre-key signature and each
  session's KEM-key signature; the signing key is used nowhere else, and the
  adversary never sees it). When the challenge session completes, it stops
  and outputs the accepted bundle's signed pair that `honestBundle` fails,
  so the pair was not returned by any signing query. Determinism of
  verification (`hverifyDet`) transfers the initiator's successful
  verification of that pair to the SUF-CMA experiment's final check.
  Strong unforgeability (rather than EUF-CMA) is needed because `setup` and
  `publish` sign only two message forms, so a dishonest bundle may reuse an
  honestly signed message with a fresh signature.

  Used by `uakeInitiator_secure_dh` and `uakeInitiator_secure_pq` as hop 3. A proof would build the
  SUF-CMA adversary described above and relate its winning event to `sigForgeExp`. -/
lemma sigForgeProb_le_sig [Inhabited S] [Inhabited SSK]
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (εsig : ℝ)
    (hverifyDet : ∀ (pk : SPK) (m : G ⊕ PQPK) (σ : S), ∃ b, P.sig.verify pk m σ = pure b)
    (hsig : ∀ B : P.sig.unforgeableAdv,
      (B.strongAdvantage ProbCompRuntime.probComp).toReal ≤ εsig) :
    sigForgeProb P msg hasOPK A ≤ εsig := by
  sorry

omit [DecidableEq CT] [DecidableEq S] [DecidableEq C] in
/-- Hop 4 (KEM-key guessing): the bad event `pqpkGuessed` is a union of
  pairwise guessing events on `P.pqkem.keygen`, so its probability is
  bounded by the number of pairs times the per-pair guessing bound `εpk`.

  Intended proof: with at most `q` sessions, the collision part is a union
  over at most `q * (q - 1) / 2` unordered session pairs; conditioning on
  the earlier key generation, the later one hits it with probability at most
  `εpk` by `hpk`. The prediction part is a union over at most `q` pairs of
  the accepted bundle and a later-opened session; the accepted bundle's key
  is determined strictly before that session's key generation, so `hpk`
  applies again. In total `q * (q + 1) / 2 ≤ q ^ 2` pairs (for `q = 0` both
  sides vanish).

  Used by `uakeInitiator_secure_dh` and `uakeInitiator_secure_pq` as hop 4. A proof would be the
  union bound described above over at most `q ^ 2` session pairs, each bounded by `hpk`. -/
lemma pqpkGuessedProb_le
    (A : UAKE.Adversary (uakeInitiator P msg hasOPK)) (q : ℕ) (hq : A.OpensAtMost q)
    (εpk : ℝ)
    (hpk : ∀ pk : PQPK, (Pr[= pk | Prod.fst <$> P.pqkem.keygen]).toReal ≤ εpk) :
    pqpkGuessedProb P msg hasOPK A ≤ (q : ℝ) ^ 2 * εpk := by
  sorry

end Protocols.PQXDH
