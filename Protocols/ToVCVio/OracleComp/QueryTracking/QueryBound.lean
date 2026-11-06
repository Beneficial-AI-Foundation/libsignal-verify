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
      Pr[ fun z => bad z.2 = true | (impl t).run s] ≤ ε * ((count s + 1 : ℕ) : ℝ≥0∞))
    {α : Type} (oa : OracleComp spec α) :
    ∀ b : ℕ, oa.IsQueryBoundP isCounted b → ∀ s, inv s →
      Pr[ fun z => bad z.2 = true | (simulateQ impl oa).run s] ≤
        (if bad s then 1 else 0) + ε * ((b * (count s + b) : ℕ) : ℝ≥0∞) := by
  induction oa using OracleComp.inductionOn with
  | pure a =>
    intro b _ s _
    rw [simulateQ_pure, StateT.run_pure, probEvent_pure]
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
        calc Pr[ fun z => bad z.2 = true |
              (impl t).run s >>= fun p => (simulateQ impl (k p.1)).run p.2]
            ≤ ∑' z, Pr[= z | (impl t).run s] * ((if bad z.2 then 1 else 0) +
                ε * ((b' * (count s + 1 + b') : ℕ) : ℝ≥0∞)) := by
              refine probEvent_bind_le_tsum _ fun z hz => ?_
              have h1 := ih z.1 b' (hcont z.1) z.2 (h_inv t s hs z hz)
              rwa [h_count t s ht hs z hz] at h1
          _ ≤ Pr[ fun z => bad z.2 = true | (impl t).run s] +
                ε * ((b' * (count s + 1 + b') : ℕ) : ℝ≥0∞) := by
              simp only [mul_add, ENNReal.tsum_add, mul_ite, mul_one, mul_zero]
              rw [← probEvent_eq_tsum_ite, ENNReal.tsum_mul_right]
              exact add_le_add le_rfl (mul_le_of_le_one_left zero_le
                (tsum_probOutput_le_one (mx := (impl t).run s)))
          _ ≤ ε * ((count s + 1 : ℕ) : ℝ≥0∞) + ε * ((b' * (count s + 1 + b') : ℕ) : ℝ≥0∞) := by
              gcongr; exact h_hit t s ht hs hbad
          _ ≤ ε * (((b' + 1) * (count s + (b' + 1)) : ℕ) : ℝ≥0∞) := by
              rw [← mul_add, ← Nat.cast_add]
              gcongr
              nlinarith
      · exact le_add_right (by simp)
    · simp only [ht, if_false] at hcont
      refine probEvent_bind_le_of_forall_le fun z hz => ?_
      obtain ⟨hbad, hcount⟩ := h_free t s ht hs z hz
      have h1 := ih z.1 b (hcont z.1) z.2 (h_inv t s hs z hz)
      rwa [hbad, hcount] at h1

end OracleComp
