/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Alessandro D'Angelo
-/
import VCVio.OracleComp.ProbComp

/-!
# Nonempty result types of `ProbComp`

A `ProbComp` computation always has an output, so its result type is nonempty. The hop-4 proof of
the PQXDH model uses this to show that a bound on a key generator's outputs is nonnegative.

The lemma statements and proofs in this file are AI-written.
-/

namespace ProbComp

/-- A `ProbComp` computation has an output, so its result type is nonempty. -/
theorem nonempty_of_probComp {α : Type} (oa : ProbComp α) : Nonempty α := by
  induction oa using ProbComp.inductionOn with
  | pure a => exact ⟨a⟩
  | query_bind n mx ih => exact ih 0

end ProbComp
