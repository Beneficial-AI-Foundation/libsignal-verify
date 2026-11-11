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
    {q : β → Prop} (g : α → ℝ≥0∞) (h : ∀ x ∈ support mx, Pr{let y ← (my x)}[(q) y] ≤ g x) :
    Pr{let y ← (mx >>= my)}[(q) y] ≤ ∑' x, Pr{let y ← mx}[y = x] * g x := by
  let _ : MeasurableSpace α := ⊤
  have hae : ∀ᵐ x ∂𝒟[mx], x ∈ support mx :=
    evalDist.ae_of_forall_mem_support mx (· ∈ support mx) MeasurableSet.of_discrete
      fun _ h ↦ h
  rw [prEvent_bind_eq_lintegral_of_discrete]
  calc ∫⁻ x, Pr{let y ← my x}[q y] ∂𝒟[mx]
      ≤ ∫⁻ x, g x ∂𝒟[mx] := MeasureTheory.lintegral_mono_ae
        (evalDist.ae_of_forall_mem_support mx _ MeasurableSet.of_discrete h)
    _ = ∫⁻ x in support mx, g x ∂𝒟[mx] := by
        rw [MeasureTheory.Measure.restrict_eq_self_of_ae_mem hae]
    _ = ∑' x : support mx, g x * 𝒟[mx] {(x : α)} :=
        MeasureTheory.lintegral_countable g (support_finite mx).countable
    _ ≤ ∑' x, g x * 𝒟[mx] {x} :=
        ENNReal.tsum_comp_le_tsum_of_injective Subtype.val_injective
          (fun x => g x * 𝒟[mx] {x})
    _ = ∑' x, Pr{let y ← mx}[y = x] * g x := by
        simp only [mul_comm, prEvent_eq_evalDist_singleton]

/-- A bound on the probability of every output of a `ProbComp` computation is nonnegative. -/
theorem nonneg_of_probOutput_le {α : Type} (oa : ProbComp α) {ε : ℝ}
    (h : ∀ a, (Pr{let y ← oa}[y = a]).toReal ≤ ε) : 0 ≤ ε := by
  obtain ⟨a⟩ := ProbComp.nonempty_of_probComp oa
  exact le_trans ENNReal.toReal_nonneg (h a)

/-- The first component of a pair drawn from `gen` lands in a fixed finite set `T` with
probability at most `|T| * ε`, when every value has probability at most `ε`. -/
theorem probEvent_fst_mem_finset_le {α β : Type} (gen : ProbComp (α × β)) (T : Finset α)
    (ε : ℝ≥0∞) (h : ∀ a, Pr{let y ← (Prod.fst <$> gen)}[y = a] ≤ ε) :
    Pr{let x ← gen}[x.1 ∈ T] ≤ ε * (T.card : ℝ≥0∞) := by
  calc Pr{let x ← gen}[x.1 ∈ T]
      = Pr{let a ← (Prod.fst <$> gen)}[∃ x ∈ T, a = x] := by
        simp
    _ ≤ ∑ x ∈ T, Pr{let a ← (Prod.fst <$> gen)}[a = x] :=
        prEvent_exists_finset_le T _ (fun x a => a = x)
    _ ≤ ∑ _x ∈ T, ε :=
        Finset.sum_le_sum fun x _ => h x
    _ = ε * (T.card : ℝ≥0∞) := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
