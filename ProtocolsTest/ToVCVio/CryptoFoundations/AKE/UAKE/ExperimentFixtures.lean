/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Alessandro D'Angelo
-/

import Protocols.ToVCVio.CryptoFoundations.AKE.UAKE.Defs

/-!
# Experiment Fixtures

Toy schemes on which the honest run, the scheme conditions and the oracle of the UAKE
experiment can be evaluated by `rfl`. Each section isolates one way in which the
correctness experiment and the security experiment could disagree about the same
protocol, and checks the definition that rules it out.
-/

open OracleSpec OracleComp

namespace AKE.UAKE

namespace ExperimentFixtures

/-! ## A finished party is not stepped again

T replies to every message and reports `done = true` each time. Its state counts the
steps taken, and its output is that count once positive. U opens with message `1` and
answers every later message `w` with `w + 1`. -/

private def finishingU : Party Id Unit ℕ (Option ℕ) where
  State := ℕ
  init := fun _ => pure (.speakFirst 0 1)
  step := fun st w => pure (.acceptAndSend (st + 1) (w + 1) false)
  output := fun _ => pure none

private def finishingT : Party Id Unit ℕ (Option ℕ) where
  State := ℕ
  init := fun _ => pure (.waitForMsg 0)
  step := fun st w => pure (.acceptAndSend (st + 1) (w + 1) true)
  output := fun st => pure (if st = 0 then none else some (some st))

private def finishing : Scheme Id ℕ Unit Unit ℕ where
  rounds := 3
  setup := pure ((), ())
  U := finishingU
  T := finishingT

/-- T finishes on message `1` with key `1`. U receives T's last message `2` and answers
it with `3`, after which the run stops instead of stepping T a second time. -/
example : finishingU.runHonest finishingT () () 10 = (none, some (some 1), [1, 2, 3]) := rfl

/-- The environment `challengeSession` builds for `finishing`: U's opening is recorded at
tick 0. -/
private def finishingEnv : Env finishing := ⟨1, ⟨(0 : ℕ), ⟨[(1, 0)]⟩⟩, false, []⟩

/-- Relay U's messages `1` and `3` to a fresh T session, then reveal its key. -/
private def relayProbe :
    OracleComp (oracleSpec ℕ ℕ) ((ℕ ⊕ Unit) × (ℕ ⊕ Unit) × Option ℕ) := do
  let (sid, _) ← query (spec := oracleSpec ℕ ℕ) .openT
  let r₁ ← query (spec := oracleSpec ℕ ℕ) (.stepT sid 1)
  let r₂ ← query (spec := oracleSpec ℕ ℕ) (.stepT sid 3)
  let key ← query (spec := oracleSpec ℕ ℕ) (.revealT sid)
  pure (r₁, r₂, key)

/-- The oracle answers message `1` with `2`, refuses message `3`, and reveals key `1`:
the key T outputs in the honest run. -/
example : ((simulateQ (opImpl finishing ()) relayProbe).run' finishingEnv : Id _)
    = (.inl 2, .inr (), some 1) := rfl

end ExperimentFixtures

end AKE.UAKE
