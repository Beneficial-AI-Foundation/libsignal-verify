/-
Copyright (c) 2026 Devon Tuma. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Devon Tuma, Alessandro D'Angelo
Ported with changes from https://github.com/Verified-zkEVM/VCVio/pull/476, see
Protocols/ATTRIBUTION.md.
-/
import VCVio.OracleComp.EvalDist
import VCVio.OracleComp.ProbCompLift

/-!
# Coherent runtimes for the UAKE experiment

The UAKE experiment samples its challenge bit and replacement key through the
`ProbCompLift` of a `ProbCompRuntime`, and scores the result through the runtime's
`SemanticsVia`. Neither structure constrains the other. A lift that answers every
uniform query with a constant is still a monad morphism, and against such a runtime an
adversary that guesses the constant bit wins every run.

`RuntimeCoherent` ties a runtime to the native output measure `𝒟[·]` of its monad:

* the possible outputs satisfy the attachment laws;
* the native measure preserves `pure` and measurable `bind`;
* the runtime observes every computation through `𝒟[·]`;
* lifting public randomness leaves its distribution unchanged;
* on a discrete output space, the observed outputs are possible outputs almost surely.

So an invariant proved on `support` holds almost surely for the outputs the runtime observes.
-/

open MeasureTheory OracleComp

namespace AKE.UAKE

variable {m : Type → Type} [Monad m] [MonadAttach m] [EvalDistSemantics m]

/-- A runtime whose observation and public randomness agree with the native output
measure `𝒟[·]` of `m`. -/
structure RuntimeCoherent (runtime : ProbCompRuntime m) : Prop where
  /-- The possible outputs satisfy the attachment laws. -/
  lawfulAttach : LawfulMonadAttach m
  /-- The native output measure preserves `pure` and measurable `bind`. -/
  lawful : LawfulEvalDistSemantics m
  /-- The runtime observes every computation through the native output measure. -/
  evalDist_eq : ∀ {α : Type} [MeasurableSpace α] (mx : m α), runtime.evalDist mx = 𝒟[mx]
  /-- Lifting public randomness into `m` leaves its distribution unchanged. -/
  lift_evalDist_eq : ∀ {α : Type} [MeasurableSpace α] (mx : ProbComp α),
    𝒟[runtime.liftProbComp mx] = 𝒟[mx]
  /-- On a discrete output space, observed outputs are possible outputs almost surely. -/
  ae_mem_support : ∀ {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α] (mx : m α),
    ∀ᵐ x ∂𝒟[mx], x ∈ support mx

/-- The canonical runtime of `ProbComp` is coherent. -/
theorem runtimeCoherent_probComp : RuntimeCoherent ProbCompRuntime.probComp where
  lawful := inferInstance
  evalDist_eq _ := rfl
  lift_evalDist_eq _ := rfl
  support_evalDist_subset mx := (support_eq_SPMF_support mx).symm.subset

/-- Under a coherent runtime, a property of every possible output holds almost surely for
the outputs the runtime observes. -/
theorem RuntimeCoherent.forall_mem_support_evalDist {runtime : ProbCompRuntime m}
    (h : RuntimeCoherent runtime) {α : Type} [MeasurableSpace α] [DiscreteMeasurableSpace α]
    (mx : m α) {p : α → Prop}
    (hp : ∀ x ∈ support mx, p x) : ∀ᵐ x ∂runtime.evalDist mx, p x := by
  rw [h.evalDist_eq]
  exact fun x hx => hp x (h.support_evalDist_subset mx hx)

end AKE.UAKE
