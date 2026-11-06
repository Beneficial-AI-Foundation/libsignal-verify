/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Alessandro D'Angelo
-/
import VCVio.EvalDist.Monad.Basic
import VCVio.OracleComp.ProbComp
import Protocols.ToVCVio.OracleComp.ProbComp

/-!
# Bounds on the probability of an event

`probEvent_bind_le_tsum` bounds an event after a bind by the expected value of any pointwise
bound on the continuation. `probEvent_fst_mem_finset_le` bounds the chance that a drawn pair's
first component lands in a finite set, and `nonneg_of_probOutput_le` says that a bound on
every output probability is nonnegative.

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

/-- A bound on the probability of every output of a `ProbComp` computation is nonnegative. -/
theorem nonneg_of_probOutput_le {α : Type} (oa : ProbComp α) {ε : ℝ}
    (h : ∀ a, (Pr[= a | oa]).toReal ≤ ε) : 0 ≤ ε := by
  obtain ⟨a⟩ := ProbComp.nonempty_of_probComp oa
  exact le_trans ENNReal.toReal_nonneg (h a)

/-- The first component of a pair drawn from `gen` lands in a fixed finite set `T` with
probability at most `|T| * ε`, when every value has probability at most `ε`. -/
theorem probEvent_fst_mem_finset_le {α β : Type} (gen : ProbComp (α × β)) (T : Finset α)
    (ε : ℝ≥0∞) (h : ∀ a, Pr[= a | Prod.fst <$> gen] ≤ ε) :
    Pr[ fun x => x.1 ∈ T | gen] ≤ ε * (T.card : ℝ≥0∞) := by
  calc Pr[ fun x => x.1 ∈ T | gen]
      = Pr[ fun a => ∃ x ∈ T, a = x | Prod.fst <$> gen] := by
        rw [probEvent_map]
        congr 1
        ext x
        simp
    _ ≤ ∑ x ∈ T, Pr[ fun a => a = x | Prod.fst <$> gen] :=
        probEvent_exists_finset_le_sum _ _ _
    _ ≤ ∑ _x ∈ T, ε :=
        Finset.sum_le_sum fun x _ => by rw [probEvent_eq_eq_probOutput]; exact h x
    _ = ε * (T.card : ℝ≥0∞) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
