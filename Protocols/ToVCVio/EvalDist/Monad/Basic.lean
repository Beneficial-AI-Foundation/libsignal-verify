/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Alessandro D'Angelo
-/
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.ProbComp

/-!
# Bounds on the probability of an event after a bind

`probEvent_bind_le_tsum` bounds an event after a bind by the expected value of any pointwise
bound on the continuation. The hop-4 proof of the PQXDH model uses it.

The lemma statements and proofs in this file are AI-written.
-/

open OracleComp
open scoped ENNReal

/-- A bind is bounded by the expected value of any pointwise bound on its continuation. -/
theorem probEvent_bind_le_tsum {α β : Type} {mx : ProbComp α} {my : α → ProbComp β}
    {q : β → Prop} (g : α → ℝ≥0∞) (h : ∀ x ∈ support mx, Pr[ q | my x] ≤ g x) :
    Pr[ q | mx >>= my] ≤ ∑' x, Pr[= x | mx] * g x := by
  rw [probEvent_bind_eq_tsum]
  refine ENNReal.tsum_le_tsum fun x => ?_
  by_cases hx : x ∈ support mx
  · exact mul_le_mul' le_rfl (h x hx)
  · simp [probOutput_eq_zero_of_not_mem_support hx]
