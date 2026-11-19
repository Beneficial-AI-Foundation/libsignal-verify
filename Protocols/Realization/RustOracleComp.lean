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
out-of-bounds index, a failed `expect`, …), or does not terminate. A protocol model is an oracle
computation in VCVio: a program that can sample randomness, with its output read as a probability
distribution. This file connects the two.

`RustOracleComp O α` is `ExceptT Fault (OracleComp O) α`: an oracle computation for the oracle
specification `O` that can also stop with a `Fault`, either a panic carrying its Aeneas error or
divergence. `liftResult` sends a `Result` computation into it: a returned value becomes
`pure`, a panic becomes `throw (.panic e)` and divergence becomes `throw .divergence`.

A Rust function reports a protocol error as an ordinary value, for example
`Err(SignalProtocolError::…)`, and `liftResult` passes such a value through unchanged. A fault is
an execution that produces no value. The runtime `rustRuntime` represents faults only as missing
probability mass (`probOutput_rustRuntime`, `probFailure_rustRuntime`).

The instance used here is `O = unifSpec`, the oracle for uniform sampling, so that
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

/-- Faults carry the discrete σ-algebra. The output measure of an `ExceptT` computation needs a
measurable space on its error type. -/
instance : MeasurableSpace Fault := ⊤

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
  cases x using Result.cases with
  | ret b =>
    rw [WP.spec_ok] at h
    subst h
    simp
  | vis i k => exact ((WP.spec_vis i k).mp h).elim
  | div => exact (WP.spec_div.mp h).elim

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

/-- The runtime for `RustOracleComp unifSpec`. It reads a computation through its native
distribution, in which every fault is missing mass, and it lifts public randomness from
`ProbComp` without faults. -/
noncomputable def rustRuntime : ProbCompRuntime (RustOracleComp unifSpec) where
  toSemanticsVia := SemanticsVia.ofEvalDistSemantics _
  toProbCompLift := ProbCompLift.ofMonadLift _
  evalDist_map_eq _f hf mx := _root_.evalDist_map mx hf

/-- `rustRuntime` is coherent. It reads every computation through the native distribution of
`RustOracleComp unifSpec`, a lift of public randomness keeps its distribution, and every output of
positive probability is a possible output. -/
theorem rustRuntime_coherent : AKE.UAKE.RuntimeCoherent rustRuntime := by
  refine
    { lawfulAttach := inferInstance
      lawful := inferInstance
      evalDist_eq := fun _ => rfl
      lift_evalDist_eq := ?_
      ae_mem_support := ?_ }
  · intro α _ mx
    exact ExceptT.evalDist_liftM mx
  · intro α _ _ mx
    exact evalDist.ae_of_forall_mem_support mx _ MeasurableSet.of_discrete fun _ hx ↦ hx

/-- Fault erasure for outputs: the runtime gives an output `a` the probability that the
computation returns `a` without a fault. -/
theorem probOutput_rustRuntime [MeasurableSpace α] [MeasurableSingletonClass α]
    (mx : RustOracleComp unifSpec α) (a : α) :
    rustRuntime.evalDist mx {a} = Pr{let r ← mx.run}[r = Except.ok a] := by
  change evalDist mx {a} = _
  rw [ExceptT.evalDist_apply, Set.image_singleton]
  have hs : MeasurableSet ({Except.ok a} : Set (Except Fault α)) := by
    change MeasurableSet ((Except.error : Fault → Except Fault α) ⁻¹' {Except.ok a}) ∧
      MeasurableSet ((Except.ok : α → Except Fault α) ⁻¹' {Except.ok a})
    refine ⟨?_, ?_⟩
    · convert MeasurableSet.empty
      ext e
      simp
    · convert measurableSet_singleton a
      ext x
      simp
  rw [prEvent_eq_evalDist (ExceptT.run mx) (fun r => r = Except.ok a)
    (measurableSet_setOfPred.mp hs)]
  rfl

/-- Fault erasure for missing mass: the probability that the runtime returns no value is the
probability of a fault. No other mass is lost. -/
theorem probFailure_rustRuntime [MeasurableSpace α] (mx : RustOracleComp unifSpec α) :
    rustRuntime.prFail mx = Pr{let r ← mx.run}[r.toBool = false] := by
  change 1 - evalDist mx Set.univ = _
  rw [ExceptT.evalDist_apply_univ]
  have hr : MeasurableSet (Set.range (Except.ok : α → Except Fault α)) := by
    change MeasurableSet ((Except.error : Fault → Except Fault α) ⁻¹' Set.range Except.ok) ∧
      MeasurableSet ((Except.ok : α → Except Fault α) ⁻¹' Set.range Except.ok)
    refine ⟨?_, ?_⟩
    · convert MeasurableSet.empty
      ext e
      simp
    · convert MeasurableSet.univ
      ext x
      simp
  have hc : {r : Except Fault α | r.toBool = false} = (Set.range Except.ok)ᶜ := by
    ext r
    cases r <;> simp [Except.toBool]
  have hs : MeasurableSet {r : Except Fault α | r.toBool = false} := hc ▸ hr.compl
  rw [prEvent_eq_evalDist (ExceptT.run mx) (fun r => r.toBool = false)
    (measurableSet_setOfPred.mp hs)]
  change _ = 𝒟[ExceptT.run mx] {r : Except Fault α | r.toBool = false}
  rw [hc, MeasureTheory.prob_compl_eq_one_sub hr]

/-- An output has probability `0` exactly when it is not a possible output. -/
theorem probOutput_rustRuntime_eq_zero_iff [MeasurableSpace α] [MeasurableSingletonClass α]
    (mx : RustOracleComp unifSpec α) (a : α) :
    rustRuntime.evalDist mx {a} = 0 ↔ a ∉ support mx := by
  rw [probOutput_rustRuntime, prEvent_eq_zero_iff, ExceptT.mem_support_iff]
  exact ⟨fun h hm ↦ h _ hm rfl, fun h x hx hxa ↦ h (hxa ▸ hx)⟩

/-- A panic has no output: every value has probability `0`. -/
@[simp] theorem probOutput_rustRuntime_liftResult_fail [MeasurableSpace α] (e : Error) (a : α) :
    rustRuntime.evalDist (liftResult (Result.fail e : Result α)) {a} = 0 := by
  rw [liftResult_fail]
  change evalDist (throw (Fault.panic e) : RustOracleComp unifSpec α) {a} = 0
  rw [ExceptT.evalDist_apply]
  have hr : MeasurableSet (Set.range (Except.ok : α → Except Fault α)) := by
    change MeasurableSet ((Except.error : Fault → Except Fault α) ⁻¹' Set.range Except.ok) ∧
      MeasurableSet ((Except.ok : α → Except Fault α) ⁻¹' Set.range Except.ok)
    refine ⟨?_, ?_⟩
    · convert MeasurableSet.empty
      ext e
      simp
    · convert MeasurableSet.univ
      ext x
      simp
  refine MeasureTheory.measure_mono_null (Set.image_subset_range _ _) ?_
  simp only [ExceptT.run_throw, evalDist_pure]
  rw [MeasureTheory.Measure.dirac_apply' _ hr]
  simp

/-- Divergence has no output: every value has probability `0`. -/
@[simp] theorem probOutput_rustRuntime_liftResult_div [MeasurableSpace α] (a : α) :
    rustRuntime.evalDist (liftResult (Result.div : Result α)) {a} = 0 := by
  rw [liftResult_div, RustOracleComp.div]
  change evalDist (throw Fault.divergence : RustOracleComp unifSpec α) {a} = 0
  rw [ExceptT.evalDist_apply]
  have hr : MeasurableSet (Set.range (Except.ok : α → Except Fault α)) := by
    change MeasurableSet ((Except.error : Fault → Except Fault α) ⁻¹' Set.range Except.ok) ∧
      MeasurableSet ((Except.ok : α → Except Fault α) ⁻¹' Set.range Except.ok)
    refine ⟨?_, ?_⟩
    · convert MeasurableSet.empty
      ext e
      simp
    · convert MeasurableSet.univ
      ext x
      simp
  refine MeasureTheory.measure_mono_null (Set.image_subset_range _ _) ?_
  simp only [ExceptT.run_throw, evalDist_pure]
  rw [MeasureTheory.Measure.dirac_apply' _ hr]
  simp

/-- The runtime's probability of the output `true` is the event probability of `b = true` under
the native output measure. -/
theorem rustRuntime_evalDist_true (mx : RustOracleComp unifSpec Bool) :
    rustRuntime.evalDist mx {true} = Pr{let b ← mx}[b = true] := by
  rw [rustRuntime_coherent.evalDist_eq, prEvent_eq_evalDist_of_discrete]
  rfl

/-- A draw lifted from `ProbComp` into `RustOracleComp unifSpec` loses no mass. -/
theorem prEvent_true_liftM {α : Type} (mx : ProbComp α) :
    Pr{let _ ← (liftM mx : RustOracleComp unifSpec α)}[True] = 1 := by
  let : MeasurableSpace α := ⊤
  rw [prEvent_true_eq_evalDist_apply_univ, ExceptT.evalDist_liftM,
    ← prEvent_true_eq_evalDist_apply_univ, prEvent_true_eq_one]

end Protocols.Realization
