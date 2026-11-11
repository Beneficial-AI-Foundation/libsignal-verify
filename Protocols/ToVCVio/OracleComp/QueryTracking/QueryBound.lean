/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Alessandro D'Angelo
-/
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.SimSemantics.SimulateQ
import Protocols.ToVCVio.EvalDist.Monad.Basic

/-!
# A potential bound for bad events of simulated oracle computations

`OracleComp.probEvent_simulateQ_bad_le` bounds the probability that a computation, simulated
with a stateful oracle implementation, ends in a bad state. The bound depends only on the
current state and on the remaining budget of counted queries, so adaptive stopping needs no
extra argument.

The lemma statements and proofs in this file are AI-written.
-/

open OracleSpec
open scoped ENNReal

namespace OracleComp

variable {ι : Type} {spec : OracleSpec ι} {σ : Type}

theorem lintegral_evalDist_eq_tsum_aux {β : Type} [MeasurableSpace β]
    [DiscreteMeasurableSpace β] (mx : ProbComp β) (g : β → ℝ≥0∞) :
    ∫⁻ x, g x ∂𝒟[mx] = ∑' x, Pr{let y ← mx}[y = x] * g x := by
  have hae : ∀ᵐ x ∂𝒟[mx], x ∈ support mx :=
    evalDist.ae_of_forall_mem_support mx (· ∈ support mx) MeasurableSet.of_discrete
      fun _ h ↦ h
  calc ∫⁻ x, g x ∂𝒟[mx]
      = ∫⁻ x in support mx, g x ∂𝒟[mx] := by
        rw [MeasureTheory.Measure.restrict_eq_self_of_ae_mem hae]
    _ = ∑' x : support mx, g x * 𝒟[mx] {(x : β)} :=
        MeasureTheory.lintegral_countable g (support_finite mx).countable
    _ = ∑' x, g x * 𝒟[mx] {x} := by
        refine tsum_subtype_eq_of_support_subset (f := fun x => g x * 𝒟[mx] {x})
          (s := support mx) fun x hx => ?_
        by_contra hx'
        refine hx ?_
        simp only [← prEvent_eq_evalDist_singleton, prEvent_eq_zero_of_not_mem_support mx hx',
          mul_zero]
    _ = ∑' x, Pr{let y ← mx}[y = x] * g x := by
        simp only [mul_comm, prEvent_eq_evalDist_singleton]

/-- Potential bound for a bad event of a simulated oracle computation. Queries in `isCounted`
consume the budget `b`, raise `count` by one, and from a good state reach a bad state with
probability at most `ε * (count + 1)`. Other queries change neither `bad` nor `count`. Then,
from a state satisfying `inv`, the run ends bad with probability at most
`1{bad} + ε * b * (count + b)`. -/
theorem probEvent_simulateQ_bad_le (impl : QueryImpl spec (StateT σ ProbComp))
    (isCounted : ι → Prop) [DecidablePred isCounted] (bad : σ → Bool) (count : σ → ℕ)
    (inv : σ → Prop) (ε : ℝ≥0∞)
    (h_inv : ∀ t s, inv s → ∀ z ∈ support ((impl t).run s), inv z.2)
    (h_free : ∀ t s, ¬ isCounted t → inv s → ∀ z ∈ support ((impl t).run s),
      bad z.2 = bad s ∧ count z.2 = count s)
    (h_count : ∀ t s, isCounted t → inv s → ∀ z ∈ support ((impl t).run s),
      count z.2 = count s + 1)
    (h_hit : ∀ t s, isCounted t → inv s → bad s = false →
      Pr{let z ← ((impl t).run s)}[bad z.2 = true] ≤ ε * ((count s + 1 : ℕ) : ℝ≥0∞))
    {α : Type} (oa : OracleComp spec α) :
    ∀ b : ℕ, oa.IsQueryBoundP isCounted b → ∀ s, inv s →
      Pr{let z ← ((simulateQ impl oa).run s)}[bad z.2 = true] ≤
        (if bad s then 1 else 0) + ε * ((b * (count s + b) : ℕ) : ℝ≥0∞) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro b _ s _
    rw [simulateQ_pure, StateT.run_pure, prEvent_pure]
    exact le_add_right (by split_ifs <;> simp_all)
  | query_bind t k ih =>
    intro b hb s hs
    rw [isQueryBoundP_query_bind_iff] at hb
    obtain ⟨hvalid, hcont⟩ := hb
    rw [simulateQ_bind, simulateQ_spec_query, StateT.run_bind]
    by_cases ht : isCounted t
    · obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 :=
        ⟨b - 1, by have := hvalid.resolve_left (not_not.mpr ht); omega⟩
      simp only [ht, if_true, Nat.add_sub_cancel] at hcont
      cases hbad : bad s
      · refine le_add_left ?_
        calc Pr{let z ← ((impl t).run s >>= fun p =>
              (simulateQ impl (k p.1)).run p.2)}[bad z.2 = true]
            ≤ ∑' z, Pr{let y ← ((impl t).run s)}[y = z] * ((if bad z.2 then 1 else 0) +
                ε * ((b' * (count s + 1 + b') : ℕ) : ℝ≥0∞)) := by
              refine probEvent_bind_le_tsum _ fun z hz => ?_
              have h1 := ih z.1 b' (hcont z.1) z.2 (h_inv t s hs z hz)
              rwa [h_count t s ht hs z hz] at h1
          _ ≤ Pr{let z ← ((impl t).run s)}[bad z.2 = true] +
                ε * ((b' * (count s + 1 + b') : ℕ) : ℝ≥0∞) := by
              let _ : MeasurableSpace (spec.Range t × σ) := ⊤
              rw [← lintegral_evalDist_eq_tsum_aux,
                MeasureTheory.lintegral_add_right _ measurable_const, MeasureTheory.lintegral_const]
              have hp := prEvent_bind_eq_lintegral_of_discrete ((impl t).run s) pure
                (fun z : spec.Range t × σ => bad z.2 = true)
              simp only [bind_pure, prEvent_pure] at hp
              rw [hp]
              exact add_le_add le_rfl (mul_le_of_le_one_right zero_le MeasureTheory.prob_le_one)
          _ ≤ ε * ((count s + 1 : ℕ) : ℝ≥0∞) + ε * ((b' * (count s + 1 + b') : ℕ) : ℝ≥0∞) := by
              gcongr; exact h_hit t s ht hs hbad
          _ ≤ ε * (((b' + 1) * (count s + (b' + 1)) : ℕ) : ℝ≥0∞) := by
              rw [← mul_add, ← Nat.cast_add]
              gcongr
              nlinarith
      · exact le_add_right (by simp)
    · simp only [ht, if_false] at hcont
      refine prEvent_bind_le_of_forall_le_of_support _ _ _ fun z hz => ?_
      obtain ⟨hbad, hcount⟩ := h_free t s ht hs z hz
      have h1 := ih z.1 b (hcont z.1) z.2 (h_inv t s hs z hz)
      rwa [hbad, hcount] at h1

end OracleComp
