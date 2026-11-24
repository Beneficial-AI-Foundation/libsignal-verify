/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Alessandro D'Angelo
-/

import Protocols.ToVCVio.CryptoFoundations.AKE.UAKE.OpeningBudget

/-!
# Opening-Budget Fixtures

A scheme whose parties never accept, and two adversaries that open sessions of T. The fixtures
check that the per-stage budget `OpensAtMost` is not vacuous, and that the composed bound
`2 * q` of `Adversary.OpensAtMost.openCount_le_two_mul` is reached at `q = 1`.
-/

open OracleSpec OracleComp

namespace AKE.UAKE

namespace OpeningBudgetFixtures

/-- A party that waits for a message and rejects every message it receives. -/
private def idleParty : Party ProbComp Unit Unit (Option Unit) where
  State := Unit
  init := fun _ => pure (.waitForMsg ())
  step := fun _ _ => pure .reject
  output := fun _ => pure none

/-- A scheme whose parties never accept. The challenge outputs no key, so `PartneredExp` runs
the key-distinguishing stage. -/
private def idle : Scheme ProbComp Unit Unit Unit Unit where
  rounds := 3
  setup := pure ((), ())
  U := idleParty
  T := idleParty

/-- One `openT` query. -/
private def openOnce : OracleComp (unifSpec + oracleSpec Unit Unit) Unit := do
  let _ ← query (spec := unifSpec + oracleSpec Unit Unit) (Sum.inr .openT)
  pure ()

/-- An adversary that opens one session of T in each stage and guesses `false`. -/
private def A₁ : Adversary idle where
  State := Unit
  challenge := fun _ _ => openOnce
  post := fun _ _ => do openOnce; pure false

/-- An adversary that opens two sessions of T in its challenge stage and none in its
key-distinguishing stage. -/
private def A₂ : Adversary idle where
  State := Unit
  challenge := fun _ _ => do openOnce; openOnce
  post := fun _ _ => pure false

/-- One `openT` query against `idle` appends one session. -/
private lemma run_openOnce (env : Env idle) :
    (simulateQ (oracleImpl ProbCompRuntime.probComp.toProbCompLift idle ()) openOnce).run env =
      pure ((), env.openNext (.waitForMsg ())) := by
  simp only [openOnce, simulateQ_bind, simulateQ_pure, StateT.run_bind, StateT.run_pure]
  rw [show (simulateQ (oracleImpl ProbCompRuntime.probComp.toProbCompLift idle ())
      (query (spec := unifSpec + oracleSpec Unit Unit) (Sum.inr .openT))).run env =
      (oracleImpl ProbCompRuntime.probComp.toProbCompLift idle () (Sum.inr .openT)).run env by
    simp [simulateQ_query]]
  rw [oracleImpl_openT_run]
  simp [idle, idleParty]

example : A₁.OpensAtMost 1 := by
  refine ⟨fun _ _ => ?_, fun _ _ => ?_⟩ <;> simp [A₁, openOnce]

/-- The bound `2 * q` is reached at `q = 1`. -/
example : ∃ z ∈ support (challengeSession ProbCompRuntime.probComp.toProbCompLift A₁ () ()),
    ∃ y ∈ support ((simulateQ (oracleImpl ProbCompRuntime.probComp.toProbCompLift idle ())
      (A₁.post z.2.1 none)).run { z.2.2.1 with challengeDone := true }),
      y.2.tSessions.length = 2 := by
  have hpost : ∀ env : Env idle,
      (simulateQ (oracleImpl ProbCompRuntime.probComp.toProbCompLift idle ())
        (A₁.post () none)).run env = pure (false, env.openNext (.waitForMsg ())) := by
    intro env
    simp only [A₁, simulateQ_bind, simulateQ_pure, StateT.run_bind, run_openOnce, pure_bind,
      StateT.run_pure]
  have hch : ∀ env : Env idle,
      (simulateQ (oracleImpl ProbCompRuntime.probComp.toProbCompLift idle ())
        (A₁.challenge () none)).run env = pure ((), env.openNext (.waitForMsg ())) :=
    run_openOnce
  have hinit : idle.U.init () = pure (.waitForMsg ()) := rfl
  have hout : ∀ s, idle.U.output s = pure none := fun _ => rfl
  simp only [challengeSession, hinit, pure_bind, Party.InitResult.opening,
    Party.InitResult.state, recordOpt, hch, hout]
  refine ⟨_, (mem_support_bind_iff _ _ _).2 ⟨_, (mem_support_pure_iff _ _).2 rfl,
    (mem_support_pure_iff _ _).2 rfl⟩, ?_⟩
  dsimp only
  rw [hpost]
  exact ⟨_, (mem_support_pure_iff _ _).2 rfl, rfl⟩

/-- The budget is not vacuous. -/
example : A₂.OpensAtMost 2 ∧ ¬ A₂.OpensAtMost 1 := by
  refine ⟨⟨fun _ _ => ?_, fun _ _ => ?_⟩, fun h => ?_⟩
  · simp [A₂, openOnce]
  · simp [A₂]
  · have h' : ∀ _u : oracleSpec Unit Unit .openT, False := by
      simpa [A₂, openOnce] using h.1 () none
    exact h' (0, none)

example : ¬ A₁.OpensAtMost 0 := by
  intro h
  have := h.1 () none
  simp [A₁, openOnce] at this

end OpeningBudgetFixtures

end AKE.UAKE
