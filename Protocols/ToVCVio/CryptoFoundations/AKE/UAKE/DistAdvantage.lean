/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin, Alessandro D'Angelo
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models and
https://github.com/Beneficial-AI-Foundation/secure-messaging, see Protocols/ATTRIBUTION.md.
-/
import Protocols.ToVCVio.CryptoFoundations.AKE.UAKE.Defs

/-!
# The real-versus-random advantage of the UAKE experiment

`AKE.UAKE.advantage` is the distance of the adversary's winning probability in `Exp` from one
half (the guess form). This file defines the real-versus-random form that secure-messaging uses.
`FixedBitExp` fixes the challenge bit `b` and returns a guess: `b = false` selects the challenge
session's key (the real game), and `b = true` selects a uniform key (the random game).
`distAdvantage` is the distance between the probabilities that the two games return `true`.
`FixedBitExp` keeps the three cases of `Exp`:
* If the challenge session outputs no key, the adversary guesses with no key in both games.
* If it accepts with no matching session of T (a forgery), `Exp` declares a win and asks for
  no guess. `FixedBitExp` returns `b`, a correct guess in either game.
* Otherwise the adversary guesses with the selected key.

In the first and third cases, a fair coin replaces the guess when a revealed session of T
matches the challenge transcript, as in `finalize`.

`advantage_eq_distAdvantage_div_two` proves `advantage = distAdvantage / 2` for the `ProbComp`
runtime. The identity needs an experiment that loses no probability mass, and `ProbComp` loses
none. Under a runtime that can lose mass, the two forms can differ: if every run fails,
`advantage` is 1/2 and `distAdvantage` is 0. Issues #29 (lost mass in `advantage`) and #30 (the
factor of two against VCVio's `boolBiasAdvantage`) remain open.

`finalizeGuess` and `FixedBitExp` follow `finalize` and `Exp`. `distAdvantage` and the proof
follow secure-messaging's one-time AEAD game. See `Protocols/ATTRIBUTION.md`. The proofs in this
file are AI-written.
-/

open OracleSpec OracleComp

namespace AKE.UAKE

variable {K UK TK W : Type} {m : Type → Type}

/-- The key-distinguishing stage `finalize` with the challenge bit `b` given, returning the
  adversary's guess `b'` instead of the test `b' == b`. The adversary receives `K1` if
  `b = true` and the challenge key otherwise. If a revealed session of T matches the challenge
  transcript, the result is a fair coin, as in `finalize`. -/
def finalizeGuess [DecidableEq W] [Monad m] (lift : ProbCompLift m)
    {proto : Scheme m K UK TK W} (A : Adversary proto)
    (st : A.State × Env proto × TK) (cr : ChallengeResult proto) (b : Bool) (K1 : Option K) :
    m Bool := do
  let (aSt, env, tk) := st
  let Kb := if b then K1 else cr.K0
  let env := { env with challengeDone := true }
  let (b', env') ← (simulateQ (oracleImpl lift proto tk) (A.post aSt Kb)).run env
  if fullPingPong env'.tSessions cr then lift.liftProbComp ($ᵗ Bool) else pure b'

/-- The UAKE experiment `Exp` with the challenge bit `b` fixed, returning a guess instead of a
  win. `FixedBitExp lift A false` is the real game and `FixedBitExp lift A true` the random
  game. In the forgery case, which `Exp` scores as a win, the result is `b`. -/
def FixedBitExp [SampleableType K] [DecidableEq W] [Monad m] (lift : ProbCompLift m)
    {proto : Scheme m K UK TK W} (A : Adversary proto) (b : Bool) : m Bool := do
  let (uk, tk) ← proto.setup
  let (cr, st) ← challengeSession lift A uk tk
  if cr.K0.isNone then
    finalizeGuess lift A st cr b none
  else if !isPingPong cr then
    return b
  else
    let K1 ← some <$> lift.liftProbComp ($ᵗ K)
    finalizeGuess lift A st cr b K1

/-- The real-versus-random advantage of the adversary: the distance between the probabilities
  that the random game `FixedBitExp … true` and the real game `FixedBitExp … false` return
  `true`. It is VCVio's `SPMF.boolDistAdvantage` of the two games. A run that loses mass returns
  neither output, so under a runtime that can lose mass this value also mixes lost mass into the
  score (#29). -/
noncomputable def distAdvantage [SampleableType K] [DecidableEq W] [Monad m]
    {proto : Scheme m K UK TK W} (runtime : ProbCompRuntime m) (A : Adversary proto) : ℝ :=
  SPMF.boolDistAdvantage (runtime.evalDist (FixedBitExp runtime.toProbCompLift A true))
    (runtime.evalDist (FixedBitExp runtime.toProbCompLift A false))

section ProbComp

/-- The lift of the `ProbComp` runtime. -/
local notation "probLift" => ProbCompRuntime.probComp.toProbCompLift

variable [SampleableType K] [DecidableEq W] {proto : Scheme ProbComp K UK TK W}

omit [SampleableType K] in
/-- `finalize` is `finalizeGuess` followed by the test against the challenge bit. -/
private theorem probOutput_finalize_eq (A : Adversary proto) (st : A.State × Env proto × TK)
    (cr : ChallengeResult proto) (b : Bool) (K1 : Option K) (x : Bool) :
    Pr[= x | finalize probLift A st cr b K1] =
      Pr[= x | finalizeGuess probLift A st cr b K1 >>=
        fun z => pure (b == z)] := by
  obtain ⟨aSt, env, tk⟩ := st
  simp only [finalize, finalizeGuess, bind_assoc]
  refine probOutput_bind_congr' _ x fun r => ?_
  obtain ⟨b', env'⟩ := r
  by_cases h : fullPingPong env'.tSessions cr
  · have hb : Function.Bijective (fun z : Bool => b == z) :=
      Function.Involutive.bijective fun z => by cases b <;> cases z <;> rfl
    simp only [h, if_true]
    change Pr[= x | ($ᵗ Bool : ProbComp Bool)] =
      Pr[= x | ($ᵗ Bool : ProbComp Bool) >>= fun z => pure (b == z)]
    rw [bind_pure_comp]
    exact (probOutput_map_bijective_uniformSample Bool hb x).symm
  · simp [h, Bool.beq_comm]

/-- The body of `Exp` after the draw of the challenge bit `b`, against `FixedBitExp`. -/
private theorem probOutput_body_eq (A : Adversary proto) (b x : Bool) :
    Pr[= x | (do
        let (uk, tk) ← proto.setup
        let (cr, st) ← challengeSession probLift A uk tk
        if cr.K0.isNone then
          finalize probLift A st cr b none
        else if !isPingPong cr then
          return true
        else do
          let K1 ← some <$> (probLift).liftProbComp ($ᵗ K)
          finalize probLift A st cr b K1 : ProbComp Bool)] =
      Pr[= x | FixedBitExp probLift A b >>=
        fun z => pure (b == z)] := by
  simp only [FixedBitExp, bind_assoc]
  refine probOutput_bind_congr' _ x fun ukt => ?_
  obtain ⟨uk, tk⟩ := ukt
  refine probOutput_bind_congr' _ x fun crst => ?_
  obtain ⟨cr, st⟩ := crst
  split_ifs with h1 h2
  · exact probOutput_finalize_eq A st cr b none x
  · simp
  · simp only [bind_assoc]
    exact probOutput_bind_congr' _ x fun K1 => probOutput_finalize_eq A st cr b K1 x

/-- `Exp` draws the challenge bit and compares it with the guess of the matching fixed-bit
game. -/
private theorem probOutput_Exp_eq_branch (A : Adversary proto) (x : Bool) :
    Pr[= x | Exp probLift A] =
      Pr[= x | (do
        let b ← ($ᵗ Bool : ProbComp Bool)
        let z ← if b then FixedBitExp probLift A true
          else FixedBitExp probLift A false
        pure (b == z) : ProbComp Bool)] := by
  have hswap : Pr[= x | Exp probLift A] = Pr[= x | (do
      let b ← ($ᵗ Bool : ProbComp Bool)
      let (uk, tk) ← proto.setup
      let (cr, st) ← challengeSession probLift A uk tk
      if cr.K0.isNone then
        finalize probLift A st cr b none
      else if !isPingPong cr then
        return true
      else do
        let K1 ← some <$> (probLift).liftProbComp ($ᵗ K)
        finalize probLift A st cr b K1 : ProbComp Bool)] := by
    rw [Exp]
    exact probOutput_bind_bind_swap _ _ _ _
  rw [hswap]
  refine probOutput_bind_congr' _ x fun b => ?_
  cases b
  · exact probOutput_body_eq A false x
  · exact probOutput_body_eq A true x

/-- The signed form: the guess advantage before the absolute value is half the difference of
the two fixed-bit games. -/
private theorem probOutput_Exp_toReal_sub_half (A : Adversary proto) :
    (Pr[= true | Exp probLift A]).toReal - 1 / 2 =
      ((Pr[= true | FixedBitExp probLift A true]).toReal -
        (Pr[= true | FixedBitExp probLift A false]).toReal) / 2 := by
  rw [probOutput_Exp_eq_branch A true]
  exact probOutput_uniformBool_branch_toReal_sub_half _ _

/-- Under the `ProbComp` runtime, the guess-form advantage is half the real-versus-random
  advantage. -/
theorem advantage_eq_distAdvantage_div_two (A : Adversary proto) :
    advantage ProbCompRuntime.probComp A = distAdvantage ProbCompRuntime.probComp A / 2 := by
  -- `probOutput_Exp_toReal_sub_half` moves the draw of the challenge bit to the start of `Exp`,
  -- splits on it, and uses VCVio's `probOutput_uniformBool_branch_toReal_sub_half`.
  unfold advantage distAdvantage SPMF.boolDistAdvantage
  change |(Pr[= true | Exp probLift A]).toReal - 1 / 2| =
    |(Pr[= true | FixedBitExp probLift A true]).toReal -
      (Pr[= true | FixedBitExp probLift A false]).toReal| / 2
  rw [probOutput_Exp_toReal_sub_half, abs_div, abs_two]

end ProbComp

end AKE.UAKE
