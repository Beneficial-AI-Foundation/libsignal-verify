/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Alessandro D'Angelo
-/
import Aeneas
import VCVio.EvalDist.Instances.ErrorT
import VCVio.OracleComp.ProbCompLift
import Protocols.ToVCVio.CryptoFoundations.AKE.UAKE.Runtime

/-!
# Extracted code as an oracle computation

The extraction translates a Rust function into a computation in Aeneas's `Result` monad. Such a
computation either returns a value, panics with an Aeneas error (an arithmetic overflow, an
out-of-bounds index, a failed `expect`, …), or does not terminate. A protocol model, on the other
hand, is an oracle computation in VCVio: a program that may sample randomness and whose output is
read as a probability distribution. This file connects the two.

`RustOracleComp O α` is `ExceptT Fault (OracleComp O) α`: an oracle computation for the oracle
specification `O` that may in addition stop with a `Fault`, either a panic carrying its Aeneas
error or divergence. `liftResult` sends a `Result` computation into it: a returned value becomes
`pure`, a panic becomes `throw (.panic e)` and divergence becomes `throw .divergence`.

A fault is not a protocol outcome. A Rust function that reports a protocol error returns it as an
ordinary value, for example `Err(SignalProtocolError::…)`, and `liftResult` passes such a value
through unchanged. A fault is an execution that produces no value at all. When the computation is
read as a distribution (`rustRuntime`), every fault is missing probability mass, so a fault can
never be mistaken for a rejection, a default value or a successful run
(`probOutput_rustRuntime`, `probFailure_rustRuntime`).

The M1 instance is `O = unifSpec`, the oracle for uniform sampling, so that
`RustOracleComp unifSpec` is `ExceptT Fault ProbComp`. `rustRuntime` packages its semantics as
a `ProbCompRuntime`, and `rustRuntime_coherent` shows that this runtime is coherent in the sense
of `AKE.UAKE.RuntimeCoherent`.
-/

open OracleSpec OracleComp Aeneas Aeneas.Std

namespace Protocols.Realization

/-- How an execution of extracted code can fail to return a value: a panic, carrying the Aeneas
error that caused it, or divergence. -/
inductive Fault where
  /-- The extracted code panicked with this error. -/
  | panic (e : Aeneas.Std.Error)
  /-- The extracted code does not terminate. -/
  | divergence

/-- An oracle computation for the specification `O` that may also stop with a `Fault`. -/
abbrev RustOracleComp {ι : Type} (O : OracleSpec ι) (α : Type) : Type :=
  ExceptT Fault (OracleComp O) α

variable {ι : Type} {O : OracleSpec ι} {α β : Type}

/-- The non-terminating computation. -/
def RustOracleComp.div : RustOracleComp O α := throw Fault.divergence

/-- Interpret an extracted computation as an oracle computation that may fault: a returned
value is returned, a panic with error `e` becomes the fault `.panic e`, and divergence becomes
the fault `.divergence`. Aeneas's `Result` has a single effect, `fail`, so every computation is
one of these three cases. -/
def liftResult (x : Result α) : RustOracleComp O α :=
  match x.match with
  | .ok a => pure a
  | .vis (.fail e) _ => throw (Fault.panic e)
  | .div => RustOracleComp.div

instance : MonadLift Result (RustOracleComp O) := ⟨liftResult⟩

@[simp] theorem liftResult_ok (a : α) : liftResult (O := O) (Result.ok a) = pure a := by
  simp [liftResult]

@[simp] theorem liftResult_pure (a : α) : liftResult (O := O) (pure a : Result α) = pure a :=
  liftResult_ok a

@[simp] theorem liftResult_fail (e : Error) :
    liftResult (O := O) (Result.fail e : Result α) = throw (Fault.panic e) := by
  simp [liftResult]

@[simp] theorem liftResult_div :
    liftResult (O := O) (Result.div : Result α) = RustOracleComp.div := by
  simp [liftResult]

/-- `liftResult` preserves sequencing: running an extracted computation and then a continuation
is the same as lifting the computation and then lifting the continuation. -/
theorem liftResult_bind (x : Result α) (f : α → Result β) :
    liftResult (O := O) (x >>= f) = liftResult x >>= fun a => liftResult (f a) := by
  cases x using Result.cases with
  | ret a => simp
  | vis i k =>
    cases i with
    | fail e =>
      have hk : Result.vis (.fail e) k = (Result.fail e : Result α) := by
        rw [Result.fail_eq_vis]
        congr
        funext x
        exact x.elim
      rw [hk]
      simp
  | div =>
    simp only [bind_tc_div, liftResult_div, RustOracleComp.div]
    rfl

/-- A computation that satisfies the specification `(· = a)` lifts to `pure a`. This is how a
functional-correctness specification of extracted code is used inside a protocol model. -/
theorem liftResult_eq_pure_of_spec {x : Result α} {a : α} (h : x ⦃ (· = a) ⦄) :
    liftResult (O := O) x = pure a := by
  obtain ⟨y, rfl, rfl⟩ := WP.spec_imp_exists h
  simp

/-- The possible outputs of a lifted computation are exactly the values it returns: a panic or
divergence has no possible output. -/
theorem mem_support_liftResult (x : Result α) (a : α) :
    a ∈ support (liftResult (O := O) x) ↔ x = Result.ok a := by
  cases x using Result.cases with
  | ret b => simp [eq_comm]
  | vis i k =>
    cases i with
    | fail e =>
      have hk : Result.vis (.fail e) k = (Result.fail e : Result α) := by
        rw [Result.fail_eq_vis]
        congr
        funext x
        exact x.elim
      rw [hk, liftResult_fail, ExceptT.mem_support_iff]
      simp [throw, throwThe, MonadExceptOf.throw, ExceptT.mk, ExceptT.run]
  | div =>
    rw [liftResult_div, RustOracleComp.div, ExceptT.mem_support_iff]
    simp [throw, throwThe, MonadExceptOf.throw, ExceptT.mk, ExceptT.run]

/-- The M1 runtime for `RustOracleComp unifSpec`: computations are observed through their native
distribution, in which every fault is missing mass, and public randomness is lifted from
`ProbComp` without faults. -/
noncomputable def rustRuntime : ProbCompRuntime (RustOracleComp unifSpec) where
  toSPMFSemantics := SPMFSemantics.ofMonadLift _
  toProbCompLift := ProbCompLift.ofMonadLift _

/-- `rustRuntime` is coherent: it observes every computation through the native distribution of
`RustOracleComp unifSpec`, lifting public randomness leaves its distribution unchanged, and every
output of positive probability is a possible output. -/
theorem rustRuntime_coherent : AKE.UAKE.RuntimeCoherent rustRuntime where
  lawful := inferInstance
  evalDist_eq _ := rfl
  lift_evalDist_eq mx := by
    change 𝒟[(liftM mx : ExceptT Fault ProbComp _)] = 𝒟[mx]
    exact SPMF.ext (ExceptT.probOutput_liftM mx)
  support_evalDist_subset mx := (support_eq_SPMF_support mx).symm.subset

/-- **Fault erasure, outputs.** The runtime gives an output `a` the probability that the
underlying computation returns `a` without a fault. -/
theorem probOutput_rustRuntime (mx : RustOracleComp unifSpec α) (a : α) :
    Pr[= a | rustRuntime.evalDist mx] = Pr[= Except.ok a | mx.run] :=
  ExceptT.probOutput_eq mx a

/-- **Fault erasure, missing mass.** The probability that the runtime returns no value is exactly
the probability of a fault; nothing else is lost. -/
theorem probFailure_rustRuntime (mx : RustOracleComp unifSpec α) :
    Pr[⊥ | rustRuntime.evalDist mx] = Pr[fun r => r.toBool = false | mx.run] := by
  change Pr[⊥ | mx] = _
  rw [ExceptT.probFailure_eq, probFailure_eq_zero, zero_add]
  congr 1
  funext r
  cases r <;> simp [Except.toBool]

/-- An output has probability `0` exactly when it is not a possible output. -/
theorem probOutput_rustRuntime_eq_zero_iff (mx : RustOracleComp unifSpec α) (a : α) :
    Pr[= a | rustRuntime.evalDist mx] = 0 ↔ a ∉ support mx := by
  rw [probOutput_rustRuntime, probOutput_eq_zero_iff, ExceptT.mem_support_iff]

/-- A panic has no output: every value has probability `0`. -/
@[simp] theorem probOutput_rustRuntime_liftResult_fail (e : Error) (a : α) :
    Pr[= a | rustRuntime.evalDist (liftResult (Result.fail e : Result α))] = 0 := by
  simp [probOutput_rustRuntime, liftResult_fail]

/-- Divergence has no output: every value has probability `0`. -/
@[simp] theorem probOutput_rustRuntime_liftResult_div (a : α) :
    Pr[= a | rustRuntime.evalDist (liftResult (Result.div : Result α))] = 0 := by
  simp [probOutput_rustRuntime, liftResult_div, RustOracleComp.div]

end Protocols.Realization
