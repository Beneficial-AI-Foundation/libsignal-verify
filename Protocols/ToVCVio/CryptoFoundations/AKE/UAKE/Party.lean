/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin, Alessandro D'Angelo
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.SimSemantics.SimulateQ

/-!
# UAKE Scheme Party Definitions

This module defines a party for use in the UAKE security notion from DF'17. In
the paper, a party is an ITM. We instead model it as a Mealy machine with a
step function that outputs a protocol message and a new state. The output
function takes the party's state and produces its final output (in UAKE, this
is the key). It is up to the protocol realization to ensure that the output
function produces output only at the end.
-/

open OracleSpec OracleComp

namespace AKE.UAKE

namespace Party

/-- Result of a party's init function -/
inductive InitResult (State W : Type)
  | speakFirst (state : State) (msg : W) : InitResult State W
  | waitForMsg (state : State) : InitResult State W

namespace InitResult

@[simp] def state {State W : Type} : InitResult State W → State
  | .speakFirst st _ => st
  | .waitForMsg st => st

@[simp] def opening {State W : Type} : InitResult State W → Option W
  | .speakFirst _ msg => some msg
  | .waitForMsg _ => none

end InitResult

/-- Result of a party's step function -/
inductive StepResult (State W : Type)
  | acceptAndSend (state : State) (msg : W) (done : Bool) : StepResult State W
  | complete (state : State) : StepResult State W
  | reject : StepResult State W

end Party

/-- A party, structured as a Mealy machine with a final output function. -/
structure Party (m : Type → Type) (In W Out : Type) where
  State : Type
  init : In → m (Party.InitResult State W)
  step : State → W → m (Party.StepResult State W)
  output : State → m (Option Out)

namespace Party

variable {m : Type → Type} {In W Out : Type}

/-- True if a party is well-formed, i.e., if it outputs iff the state is
  the result of an execution of the step function that returns `done = true`
  or `.complete` (assuming the state is reachable). -/
def OutputsOnlyAtCompletion [Monad m] [MonadAttach m] (P : Party m In W Out) : Prop :=
  let init_output := ∀ i r, r ∈ support (P.init i) →
    ∀ out ∈ support (P.output r.state), out = none;
  let complete_output := ∀ st w st', .complete st' ∈ support (P.step st w) →
    ∀ out ∈ support (P.output st'), out ≠ none;
  let accept_output := ∀ st w st' w' (done : Bool),
    .acceptAndSend st' w' done ∈ support (P.step st w) →
      ∀ out ∈ support (P.output st'), out ≠ none ↔ done;
  init_output ∧ complete_output ∧ accept_output

/-- True if the output function has no effect in `m`, i.e., on every state it
  returns a fixed value. The correctness experiment reads both outputs after the
  honest run, while the security experiment reads T's output when its session
  completes and U's after the adversary's challenge phase. Pure outputs make
  these readings agree. -/
def PureOutput [Pure m] (P : Party m In W Out) : Prop :=
  ∀ st, ∃ out, P.output st = pure out

/-- Helper function for runHonest. Run the two parties against each other. The
  messages sent are returned in chronological order, along with P's and Q's
  states.
  * The `fuel` argument is an upper bound on the number of party step functions
    that may be run before the protocol completes.
  * The first Boolean indicates whether this is Q's (true) or P's (false) turn.
  * The second Boolean records whether the sender of the message `w` finished
    when it sent it, i.e. its step returned `done = true`. The receiver of `w`
    then takes the last step of the run: the sender is never stepped again,
    just as `opImpl` refuses every message to a T session whose key is set.
  * The `sent` list contains the messages sent in the protocol so far. Note
    that the `sent` list must be passed to this function in *reverse*
    chronological order. This is to support easy cons-ing of new messages. -/
def runHonestLoop [Monad m] {InP OutP InQ OutQ : Type}
    (P : Party m InP W OutP) (Q : Party m InQ W OutQ) :
    ℕ → P.State → Q.State → W → Bool → Bool → List W →
      m (P.State × Q.State × List W)
  | 0, pState, qState, _, _, _, sent => pure (pState, qState, sent.reverse)
  | fuel + 1, pState, qState, w, true, senderDone, sent => do
      match ← Q.step qState w with
      | .acceptAndSend qState' w' done =>
          if senderDone then pure (pState, qState', (w' :: sent).reverse)
          else runHonestLoop P Q fuel pState qState' w' false done (w' :: sent)
      | .complete qState' => pure (pState, qState', sent.reverse)
      | .reject => pure (pState, qState, sent.reverse)
  | fuel + 1, pState, qState, w, false, senderDone, sent => do
      match ← P.step pState w with
      | .acceptAndSend pState' w' done =>
          if senderDone then pure (pState', qState, (w' :: sent).reverse)
          else runHonestLoop P Q fuel pState' qState w' true done (w' :: sent)
      | .complete pState' => pure (pState', qState, sent.reverse)
      | .reject => pure (pState, qState, sent.reverse)

/-- Start an honest run of the protocol, initiating the loop function based on
  which party opens. -/
def runHonestStart [Monad m] {InP OutP InQ OutQ : Type}
    (P : Party m InP W OutP) (Q : Party m InQ W OutQ) (fuel : ℕ)
    (pInit : InitResult P.State W) (qInit : InitResult Q.State W) :
    m (P.State × Q.State × List W) :=
  match pInit.opening, qInit.opening with
  | some w, _ => runHonestLoop P Q fuel pInit.state qInit.state w true false [w]
  | none, some w => runHonestLoop P Q fuel pInit.state qInit.state w false false [w]
  | none, none => pure (pInit.state, qInit.state, [])

/-- Execute an honest run of the protocol. The result is a triple of P's
  output, Q's output, and the message list. The `fuel` argument is an upper
  bound on how many party step functions may be run in the execution of the
  protocol. -/
def runHonest [Monad m] {InP OutP InQ OutQ : Type}
    (P : Party m InP W OutP) (Q : Party m InQ W OutQ) (inP : InP) (inQ : InQ) (fuel : ℕ) :
    m (Option OutP × Option OutQ × List W) := do
  let pInit ← P.init inP
  let qInit ← Q.init inQ
  let (pState', qState', ms) ← runHonestStart P Q fuel pInit qInit
  let pOut ← P.output pState'
  let qOut ← Q.output qState'
  pure (pOut, qOut, ms)

end Party

namespace Party

section Stuck

variable {m : Type → Type} [Monad m] [LawfulMonad m] [MonadAttach m] [LawfulMonadAttach m]
  {InP OutP InQ OutQ W : Type} (P : Party m InP W OutP) (Q : Party m InQ W OutQ)

/-- If every step of `P` from a state satisfying `I` rejects, then an honest run that starts with
`P` in `I` ends with `P` in `I`. -/
theorem runHonestLoop_fst_of_stuck (I : P.State → Prop)
    (hI : ∀ st, I st → ∀ w r, r ∈ support (P.step st w) → r = .reject) :
    ∀ fuel pS qS w turn sd sent, I pS →
      ∀ x ∈ support (Party.runHonestLoop P Q fuel pS qS w turn sd sent), I x.1 := by
  intro fuel
  induction fuel with
  | zero =>
    intro pS qS w turn sd sent hpS x hx
    simp only [Party.runHonestLoop, MonadAttach.mem_support] at hx
    rw [← LawfulMonadAttach.eq_of_canReturn_pure hx]
    exact hpS
  | succ n ih =>
    intro pS qS w turn sd sent hpS x hx
    cases turn with
    | true =>
      simp only [Party.runHonestLoop, MonadAttach.mem_support] at hx
      obtain ⟨r, -, hx⟩ := LawfulMonadAttach.canReturn_bind_imp' hx
      split at hx
      · split at hx
        · rw [← LawfulMonadAttach.eq_of_canReturn_pure hx]
          exact hpS
        · exact ih _ _ _ _ _ _ hpS x hx
      all_goals
        rw [← LawfulMonadAttach.eq_of_canReturn_pure hx]
        exact hpS
    | false =>
      simp only [Party.runHonestLoop, MonadAttach.mem_support] at hx
      obtain ⟨r, hr, hx⟩ := LawfulMonadAttach.canReturn_bind_imp' hx
      rw [hI pS hpS w r hr] at hx
      rw [← LawfulMonadAttach.eq_of_canReturn_pure hx]
      exact hpS

/-- If every step of `Q` from a state satisfying `I` rejects, then an honest run that starts with
`Q` in `I` ends with `Q` in `I`. -/
theorem runHonestLoop_snd_of_stuck (I : Q.State → Prop)
    (hI : ∀ st, I st → ∀ w r, r ∈ support (Q.step st w) → r = .reject) :
    ∀ fuel pS qS w turn sd sent, I qS →
      ∀ x ∈ support (Party.runHonestLoop P Q fuel pS qS w turn sd sent), I x.2.1 := by
  intro fuel
  induction fuel with
  | zero =>
    intro pS qS w turn sd sent hqS x hx
    simp only [Party.runHonestLoop, MonadAttach.mem_support] at hx
    rw [← LawfulMonadAttach.eq_of_canReturn_pure hx]
    exact hqS
  | succ n ih =>
    intro pS qS w turn sd sent hqS x hx
    cases turn with
    | true =>
      simp only [Party.runHonestLoop, MonadAttach.mem_support] at hx
      obtain ⟨r, hr, hx⟩ := LawfulMonadAttach.canReturn_bind_imp' hx
      rw [hI qS hqS w r hr] at hx
      rw [← LawfulMonadAttach.eq_of_canReturn_pure hx]
      exact hqS
    | false =>
      simp only [Party.runHonestLoop, MonadAttach.mem_support] at hx
      obtain ⟨r, -, hx⟩ := LawfulMonadAttach.canReturn_bind_imp' hx
      split at hx
      · split at hx
        · rw [← LawfulMonadAttach.eq_of_canReturn_pure hx]
          exact hqS
        · exact ih _ _ _ _ _ _ hqS x hx
      all_goals
        rw [← LawfulMonadAttach.eq_of_canReturn_pure hx]
        exact hqS

/-- If `P` starts in `I` and every step of `P` from `I` rejects, then `P`'s output after any
honest run is an output of some state in `I`. -/
theorem runHonest_fst_of_stuck (I : P.State → Prop)
    (hI : ∀ st, I st → ∀ w r, r ∈ support (P.step st w) → r = .reject)
    (hInit : ∀ inP r, r ∈ support (P.init inP) → I r.state) (inP : InP) (inQ : InQ) (fuel : ℕ) :
    ∀ x ∈ support (P.runHonest Q inP inQ fuel), ∃ st, I st ∧ x.1 ∈ support (P.output st) := by
  intro x hx
  simp only [Party.runHonest, MonadAttach.mem_support] at hx
  obtain ⟨pInit, hpInit, hx⟩ := LawfulMonadAttach.canReturn_bind_imp' hx
  obtain ⟨qInit, -, hx⟩ := LawfulMonadAttach.canReturn_bind_imp' hx
  obtain ⟨⟨pS, qS, ms⟩, hrun, hx⟩ := LawfulMonadAttach.canReturn_bind_imp' hx
  obtain ⟨pOut, hpOut, hx⟩ := LawfulMonadAttach.canReturn_bind_imp' hx
  obtain ⟨qOut, -, hx⟩ := LawfulMonadAttach.canReturn_bind_imp' hx
  have hx := LawfulMonadAttach.eq_of_canReturn_pure hx
  refine ⟨pS, ?_, by rw [← hx]; exact hpOut⟩
  unfold Party.runHonestStart at hrun
  split at hrun
  · exact runHonestLoop_fst_of_stuck P Q I hI _ _ _ _ _ _ _ (hInit _ _ hpInit) _ hrun
  · exact runHonestLoop_fst_of_stuck P Q I hI _ _ _ _ _ _ _ (hInit _ _ hpInit) _ hrun
  · have hrun := LawfulMonadAttach.eq_of_canReturn_pure hrun
    simp only [Prod.mk.injEq] at hrun
    rw [← hrun.1]
    exact hInit _ _ hpInit

/-- If `Q` starts in `I` and every step of `Q` from `I` rejects, then `Q`'s output after any
honest run is an output of some state in `I`. -/
theorem runHonest_snd_of_stuck (I : Q.State → Prop)
    (hI : ∀ st, I st → ∀ w r, r ∈ support (Q.step st w) → r = .reject)
    (hInit : ∀ inQ r, r ∈ support (Q.init inQ) → I r.state) (inP : InP) (inQ : InQ) (fuel : ℕ) :
    ∀ x ∈ support (P.runHonest Q inP inQ fuel), ∃ st, I st ∧ x.2.1 ∈ support (Q.output st) := by
  intro x hx
  simp only [Party.runHonest, MonadAttach.mem_support] at hx
  obtain ⟨pInit, -, hx⟩ := LawfulMonadAttach.canReturn_bind_imp' hx
  obtain ⟨qInit, hqInit, hx⟩ := LawfulMonadAttach.canReturn_bind_imp' hx
  obtain ⟨⟨pS, qS, ms⟩, hrun, hx⟩ := LawfulMonadAttach.canReturn_bind_imp' hx
  obtain ⟨pOut, -, hx⟩ := LawfulMonadAttach.canReturn_bind_imp' hx
  obtain ⟨qOut, hqOut, hx⟩ := LawfulMonadAttach.canReturn_bind_imp' hx
  have hx := LawfulMonadAttach.eq_of_canReturn_pure hx
  refine ⟨qS, ?_, by rw [← hx]; exact hqOut⟩
  unfold Party.runHonestStart at hrun
  split at hrun
  · exact runHonestLoop_snd_of_stuck P Q I hI _ _ _ _ _ _ _ (hInit _ _ hqInit) _ hrun
  · exact runHonestLoop_snd_of_stuck P Q I hI _ _ _ _ _ _ _ (hInit _ _ hqInit) _ hrun
  · have hrun := LawfulMonadAttach.eq_of_canReturn_pure hrun
    simp only [Prod.mk.injEq] at hrun
    rw [← hrun.2.1]
    exact hInit _ _ hqInit

end Stuck

end Party

end AKE.UAKE
