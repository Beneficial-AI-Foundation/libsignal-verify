/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin, Alessandro D'Angelo
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import Protocols.ToVCVio.CryptoFoundations.AKE.UAKE.Partnering
import Protocols.ToVCVio.CryptoFoundations.AKE.UAKE.Transport

/-!
# The UAKE experiment over a session partnering

`PartneredExp` decides partnering on the states of two sessions, and `AKE.UAKE.Exp` decides it on
their transcripts. `SessionExp` takes a partnering relation that sees whole sessions, so both are
instances of it. `Partnering.toSession` embeds a state-level partnering, with the completed key and
the acceptance order of `authPartnered`, and `SessionExp_toSession` shows that the experiment is
then `PartneredExp`. `transcriptPartnering` is the transcript matching of DF'17, and
`SessionExp_transcript` shows that the experiment is then `Exp`. Each test reads its inputs where
the landed experiments read them: the authentication test at the end of the challenge stage, the
freshness test after the key-distinguishing stage with the challenge transcript of the challenge
stage.

The definitions and proofs in this file are AI-written.
-/

open OracleSpec OracleComp

namespace AKE.UAKE

variable {K UK TK W : Type} {m : Type → Type}

/-- A partnering relation over sessions. Both relations see the challenge session (its state and
transcript) and a session of T (its state, transcript, key and reveal flag). -/
structure SessionPartnering (proto : Scheme m K UK TK W) where
  /-- The session of T is an authentication partner of the challenge. -/
  partner : Session proto.U.State W → TSession proto → Prop
  /-- A revealed session of T in this relation makes the challenge not fresh. -/
  revealEq : Session proto.U.State W → TSession proto → Prop

variable {proto : Scheme m K UK TK W}

open Classical in
/-- The key-distinguishing stage over a session partnering: as `finalize`, except that a coin flip
replaces the guess when a revealed session of T is reveal-equivalent to the challenge. The
challenge session has the state after this stage and the transcript of the challenge stage. -/
noncomputable def finalizeSession [Monad m] (lift : ProbCompLift m) (π : SessionPartnering proto)
    (A : Adversary proto) (st : A.State × Env proto × TK) (cr : ChallengeResult proto)
    (b : Bool) (K1 : Option K) : m Bool := do
  let (aSt, env, tk) := st
  let Kb := if b then K1 else cr.K0
  let env := { env with challengeDone := true }
  let (b', env') ← (simulateQ (oracleImpl lift proto tk) (A.post aSt Kb)).run env
  if decide (∃ t ∈ env'.tSessions, t.revealed = true ∧
      π.revealEq ⟨env'.challenge.state, cr.challengeTr⟩ t) then
    lift.liftProbComp ($ᵗ Bool)
  else pure (b' == b)

open Classical in
/-- The UAKE experiment over a session partnering, with the three branches of `PartneredExp`. -/
noncomputable def SessionExp [SampleableType K] [Monad m] (lift : ProbCompLift m)
    (π : SessionPartnering proto) (A : Adversary proto) : m Bool := do
  let (uk, tk) ← proto.setup
  let b ← lift.liftProbComp ($ᵗ Bool)
  let (cr, st) ← challengeSession lift A uk tk
  let (_, env, _) := st
  if cr.K0.isNone then
    finalizeSession lift π A st cr b none
  else if !decide (∃ t ∈ env.tSessions, π.partner ⟨env.challenge.state, cr.challengeTr⟩ t) then
    return true
  else
    let K1 ← some <$> lift.liftProbComp ($ᵗ K)
    finalizeSession lift π A st cr b K1

/-- The guess-form advantage of `SessionExp`. -/
noncomputable def sessionAdvantage [SampleableType K] [Monad m] (runtime : ProbCompRuntime m)
    (π : SessionPartnering proto) (A : Adversary proto) : ℝ :=
  |(runtime.evalDist (SessionExp runtime.toProbCompLift π A) {true}).toReal - 1 / 2|

/-- A state-level partnering as a session partnering. Authentication adds the completed key and
the acceptance order of `authPartnered`. Reveal equivalence is `π.partner` on the two states. -/
def Partnering.toSession (π : Partnering proto) : SessionPartnering proto where
  partner c t := (∃ k, t.key = some (some k)) ∧ π.partner c.state t.state ∧
    ∃ tc ti, acceptTime c.transcript = some tc ∧ acceptTime t.transcript = some ti ∧ ti ≤ tc
  revealEq c t := π.partner c.state t.state

/-- DF'17 transcript matching as a session partnering: both relations are `Matching` of the
transcript of the session of T against the challenge transcript. -/
def transcriptPartnering (proto : Scheme m K UK TK W) : SessionPartnering proto where
  partner c t := Matching (proto.rounds % 2 == 1) t.transcript c.transcript
  revealEq c t := Matching (proto.rounds % 2 == 1) t.transcript c.transcript

/-- Over the embedding of a state-level partnering, the session experiment is `PartneredExp`. -/
theorem SessionExp_toSession [SampleableType K] [Monad m] (lift : ProbCompLift m)
    (π : Partnering proto) (A : Adversary proto) :
    SessionExp lift π.toSession A = PartneredExp lift π A := by
  unfold SessionExp PartneredExp finalizeSession finalizePartnered authPartnered revealedPartnered
  refine bind_congr fun x => ?_
  obtain ⟨uk, tk⟩ := x
  refine bind_congr fun b => bind_congr fun r => ?_
  obtain ⟨cr, aSt, env, tk'⟩ := r
  simp only [Partnering.toSession]
  congr! <;> exact decide_eq_decide.mpr Iff.rfl

/-- Over the embedding of a state-level partnering, the session advantage is
`partneredAdvantage`. -/
theorem sessionAdvantage_toSession [SampleableType K] [Monad m] (runtime : ProbCompRuntime m)
    (π : Partnering proto) (A : Adversary proto) :
    sessionAdvantage runtime π.toSession A = partneredAdvantage runtime π A := by
  unfold sessionAdvantage partneredAdvantage
  rw [SessionExp_toSession]

/-- `fullPingPong` holds when a revealed session of T matches the challenge transcript. -/
private lemma fullPingPong_iff [DecidableEq W] (ts : List (TSession proto))
    (cr : ChallengeResult proto) :
    fullPingPong ts cr = true ↔
      ∃ t ∈ ts, t.revealed = true ∧
        Matching (proto.rounds % 2 == 1) t.transcript cr.challengeTr := by
  simp [fullPingPong, pingPong]

/-- On a challenge result built from the sessions `ts`, `isPingPong` holds when a session of T
matches the challenge transcript. -/
private lemma isPingPong_iff [DecidableEq W] (k : Option K) (ctr : Transcript W)
    (ts : List (TSession proto)) :
    isPingPong (⟨k, ctr, ts.map (·.transcript)⟩ : ChallengeResult proto) = true ↔
      ∃ t ∈ ts, Matching (proto.rounds % 2 == 1) t.transcript ctr := by
  simp [isPingPong, pingPong]

/-- Over DF'17 transcript matching, the key-distinguishing stage is `finalize`. -/
private lemma finalizeSession_transcript [DecidableEq W] [Monad m] (lift : ProbCompLift m)
    (A : Adversary proto) (st : A.State × Env proto × TK) (cr : ChallengeResult proto)
    (b : Bool) (K1 : Option K) :
    finalizeSession lift (transcriptPartnering proto) A st cr b K1 =
      finalize lift A st cr b K1 := by
  obtain ⟨aSt, env, tk⟩ := st
  unfold finalizeSession finalize
  refine bind_congr fun y => ?_
  obtain ⟨b', env'⟩ := y
  dsimp only
  congr! 1
  simp only [decide_eq_true_eq, fullPingPong_iff]
  rfl

/-- Over DF'17 transcript matching, the session experiment is `Exp`. -/
theorem SessionExp_transcript [SampleableType K] [DecidableEq W] [Monad m] [LawfulMonad m]
    (lift : ProbCompLift m) (A : Adversary proto) :
    SessionExp lift (transcriptPartnering proto) A = Exp lift A := by
  unfold SessionExp Exp
  refine bind_congr fun x => ?_
  obtain ⟨uk, tk⟩ := x
  refine bind_congr fun b => ?_
  simp only [challengeSession, bind_assoc, pure_bind]
  refine bind_congr fun u0 => bind_congr fun p => bind_congr fun k0 => ?_
  obtain ⟨aSt, env⟩ := p
  dsimp only
  simp only [finalizeSession_transcript]
  congr! 2
  rw [Bool.not_eq_true', Bool.not_eq_true', Bool.eq_false_iff, Bool.eq_false_iff, ne_eq, ne_eq]
  simp only [decide_eq_true_eq, isPingPong_iff]
  rfl

/-- Over DF'17 transcript matching, the session advantage is `advantage`. -/
theorem sessionAdvantage_transcript [SampleableType K] [DecidableEq W] [Monad m] [LawfulMonad m]
    (runtime : ProbCompRuntime m) (A : Adversary proto) :
    sessionAdvantage runtime (transcriptPartnering proto) A = advantage runtime A := by
  unfold sessionAdvantage advantage
  rw [SessionExp_transcript]

/-- The transport theorem `Exp_transport` for the session experiment over DF'17 transcript
matching. -/
theorem SessionExp_transcript_transport [SampleableType K]
    {UK₁ TK₁ UK₂ TK₂ : Type} [Monad m] [LawfulMonad m]
    {proto₁ : Scheme m K UK₁ TK₁ W} {proto₂ : Scheme m K UK₂ TK₂ W} (lift : ProbCompLift m)
    {fU : UK₁ → UK₂} {fT : TK₁ → TK₂}
    {σU : proto₁.U.State → proto₂.U.State} {σT : proto₁.T.State → proto₂.T.State}
    (hU : Party.Sim proto₁.U proto₂.U fU σU) (hT : Party.Sim proto₁.T proto₂.T fT σT)
    (hrounds : proto₂.rounds = proto₁.rounds)
    (hsetup : proto₂.setup = Prod.map fU fT <$> proto₁.setup) (A : Adversary proto₂) :
    SessionExp lift (transcriptPartnering proto₂) A =
      SessionExp lift (transcriptPartnering proto₁) (A.transport fU) := by
  classical
  rw [SessionExp_transcript, SessionExp_transcript]
  exact Exp_transport lift hU hT hrounds hsetup A

end AKE.UAKE
