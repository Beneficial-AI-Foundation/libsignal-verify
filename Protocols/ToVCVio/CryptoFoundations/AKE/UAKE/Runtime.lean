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
`SPMFSemantics`. Neither structure constrains the other. A lift that answers every
uniform query with a constant is still a monad morphism, and against such a runtime an
adversary that guesses the constant bit wins every run.

`RuntimeCoherent` ties a runtime to the native distribution `𝒟[·]` of its monad: the
runtime observes every computation through `𝒟[·]`, which preserves `pure` and `bind`;
lifting public randomness leaves its distribution unchanged; and every output of positive
probability is a possible output, so invariants proved on `support` hold for every output
the runtime observes. The certificate is stated for the `SPMF` semantics of the pinned
VCVio rather than the measure semantics of VCVio PR #476.
-/

open OracleComp

namespace AKE.UAKE

variable {m : Type → Type} [Monad m] [MonadLiftT m SetM] [MonadLiftT m SPMF]

/-- A runtime whose observation and public randomness agree with the native distribution
`𝒟[·]` of `m`. -/
structure RuntimeCoherent (runtime : ProbCompRuntime m) : Prop where
  /-- The native distribution preserves `pure` and `bind`. -/
  lawful : LawfulMonadLiftT m SPMF
  /-- The runtime observes every computation through the native distribution. -/
  evalDist_eq : ∀ {α : Type} (mx : m α), runtime.evalDist mx = 𝒟[mx]
  /-- Lifting public randomness into `m` leaves its distribution unchanged. -/
  lift_evalDist_eq : ∀ {α : Type} (mx : ProbComp α), 𝒟[runtime.liftProbComp mx] = 𝒟[mx]
  /-- Every output of positive probability is a possible output. -/
  support_evalDist_subset : ∀ {α : Type} (mx : m α), support 𝒟[mx] ⊆ support mx

/-- The canonical runtime of `ProbComp` is coherent. -/
theorem runtimeCoherent_probComp : RuntimeCoherent ProbCompRuntime.probComp where
  lawful := inferInstance
  evalDist_eq _ := rfl
  lift_evalDist_eq _ := rfl
  support_evalDist_subset mx := (support_eq_SPMF_support mx).symm.subset

/-- Under a coherent runtime, a property of every possible output holds for every output
of positive probability. -/
theorem RuntimeCoherent.forall_mem_support_evalDist {runtime : ProbCompRuntime m}
    (h : RuntimeCoherent runtime) {α : Type} (mx : m α) {p : α → Prop}
    (hp : ∀ x ∈ support mx, p x) : ∀ x ∈ support (runtime.evalDist mx), p x := by
  rw [h.evalDist_eq]
  exact fun x hx => hp x (h.support_evalDist_subset mx hx)

end AKE.UAKE
