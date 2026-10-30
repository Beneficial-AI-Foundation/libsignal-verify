/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Alessandro D'Angelo
-/
import Protocols.ToVCVio.CryptoFoundations.AKE.UAKE.Defs
import VCVio.OracleComp.QueryTracking.QueryBound

/-!
# The UAKE experiment over a partnering relation

The UAKE experiment `AKE.UAKE.Exp` decides whether an adversary attacked the challenge session by
comparing transcripts: the adversary is trivial when it relayed the messages of some session of
the authenticated party T (the "ping-pong" relation of Dodis and Fiore). This file states the same
experiment over a general **partnering relation** between the state of the challenge session and
the state of a session of T, and records when each session accepted.

* `acceptTime tr` is the time at which a completed session accepted: the clock value of the last
  entry of its transcript. The experiment already timestamps every message, and a session that
  has accepted takes no further message, so no step counter is needed.
* The challenge is **authentication-partnered** (`authPartnered`) when some completed session of T
  is its partner and accepted no later than the challenge did. When the challenge accepted with no
  such partner, the adversary has impersonated T and wins.
* The challenge has a **revealed partner** (`revealedPartnered`) when some session of T whose key
  the adversary revealed is its partner, at any time. Such a challenge is not fresh: the adversary
  knows its key, and the experiment replaces its guess by a coin flip.

The adversary's only exposure query is `revealT`, which returns the key of a completed session of
T. There is no corruption of long-term keys and no reveal of session state, and the challenge key
is given only as the challenge. The oracle implementation, the challenge phase and the
environment are those of `AKE.UAKE.Exp`, unchanged; only the two decisions above differ.
`partneredAdvantage` is the guess-form advantage of this experiment.
-/

open OracleSpec OracleComp

namespace AKE.UAKE

variable {K UK TK W : Type} {m : Type → Type}

/-- A partnering relation for a UAKE scheme: when the state of a session of the unauthenticated
party U and the state of a session of the authenticated party T are partners. -/
structure Partnering (proto : Scheme m K UK TK W) where
  /-- The partner relation between a U state and a T state. -/
  partner : proto.U.State → proto.T.State → Prop

/-- The time at which a session accepted: the clock value of the last entry of its transcript. -/
def acceptTime (tr : Transcript W) : Option ℕ :=
  tr.entries.getLast?.map Prod.snd

variable {proto : Scheme m K UK TK W}

/-- The challenge, in state `cState` with transcript `cTr`, has an authentication partner among
the sessions `ts` of T: a session that completed with a key, whose state is a partner of the
challenge state, and which accepted no later than the challenge. -/
def authPartnered (π : Partnering proto) (cState : proto.U.State) (cTr : Transcript W)
    (ts : List (TSession proto)) : Prop :=
  ∃ t ∈ ts, (∃ k, t.key = some (some k)) ∧ π.partner cState t.state ∧
    ∃ tc ti, acceptTime cTr = some tc ∧ acceptTime t.transcript = some ti ∧ ti ≤ tc

/-- Some session of T whose key was revealed is a partner of the challenge state `cState`. -/
def revealedPartnered (π : Partnering proto) (cState : proto.U.State)
    (ts : List (TSession proto)) : Prop :=
  ∃ t ∈ ts, t.revealed = true ∧ π.partner cState t.state

open Classical in
/-- The key-distinguishing stage over a partnering relation: as `finalize`, except that the guess
is replaced by a coin flip when a revealed session of T is a partner of the challenge. -/
noncomputable def finalizePartnered [Monad m] (lift : ProbCompLift m) (π : Partnering proto)
    (A : Adversary proto) (st : A.State × Env proto × TK) (cr : ChallengeResult proto)
    (b : Bool) (K1 : Option K) : m Bool := do
  let (aSt, env, tk) := st
  let Kb := if b then K1 else cr.K0
  let env := { env with challengeDone := true }
  let (b', env') ← (simulateQ (oracleImpl lift proto tk) (A.post aSt Kb)).run env
  if decide (revealedPartnered π env'.challenge.state env'.tSessions) then
    lift.liftProbComp ($ᵗ Bool)
  else pure (b' == b)

open Classical in
/-- **The UAKE experiment over a partnering relation.**
1. Run setup, and choose the challenge bit `b`.
2. Run the adversary's challenge stage, with sessions of T and the challenge session.
3. If the challenge did not accept, run the key-distinguishing stage with no key.
4. If it accepted without an authentication partner, the adversary wins.
5. Otherwise run the key-distinguishing stage on the challenge key and a uniform key. -/
noncomputable def PartneredExp [SampleableType K] [Monad m] (lift : ProbCompLift m)
    (π : Partnering proto) (A : Adversary proto) : m Bool := do
  let (uk, tk) ← proto.setup
  let b ← lift.liftProbComp ($ᵗ Bool)
  let (cr, st) ← challengeSession lift A uk tk
  if cr.K0.isNone then
    finalizePartnered lift π A st cr b none
  else if !decide (authPartnered π st.2.1.challenge.state cr.challengeTr st.2.1.tSessions) then
    return true
  else
    let K1 ← some <$> lift.liftProbComp ($ᵗ K)
    finalizePartnered lift π A st cr b K1

/-- **Opening budget per phase.** The adversary opens at most `q` sessions of T in its challenge
stage and at most `q` in its key-distinguishing stage, so at most `2q` in all. -/
def Adversary.OpensAtMostPerPhase (A : Adversary proto) (q : ℕ) : Prop :=
  (∀ uk w, (A.challenge uk w).IsQueryBoundP (· matches Sum.inr .openT) q) ∧
    (∀ st k, (A.post st k).IsQueryBoundP (· matches Sum.inr .openT) q)

/-- The adversary's advantage in the partnered experiment: the distance of its winning
probability from `1/2`. Like `advantage`, it measures security only when the experiment loses
no probability mass against the adversary. -/
noncomputable def partneredAdvantage [SampleableType K] [Monad m]
    (runtime : ProbCompRuntime m) (π : Partnering proto) (A : Adversary proto) : ℝ :=
  |(Pr[= true | runtime.evalDist (PartneredExp runtime.toProbCompLift π A)]).toReal - 1 / 2|

end AKE.UAKE
