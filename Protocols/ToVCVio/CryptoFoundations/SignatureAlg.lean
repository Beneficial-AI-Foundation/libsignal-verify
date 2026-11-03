/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import Protocols.ToVCVio.OracleComp.QueryTracking.Structures
import VCVio.CryptoFoundations.SignatureAlg

universe u v

open OracleSpec OracleComp ENNReal

namespace SignatureAlg

variable {ι : Type u} {spec : OracleSpec ι} {M PK SK S : Type}
  [DecidableEq M] [DecidableEq S]

/-- The SUF-CMA experiment, observed through `runtime`. Identical to
  `unforgeableExperiment`, except that the adversary may win by outputting a σ for a
  queried message, as long as no such query returned σ. -/
noncomputable def stronglyUnforgeableExp
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adv : UnforgeableAdversary sigAlg) : MeasureTheory.Measure Bool :=
  letI : DecidableEq M := Classical.decEq M
  letI : DecidableEq S := Classical.decEq S
  runtime.evalDist do
    let (pk, sk) ← sigAlg.keygen
    let impl : QueryImpl (spec + (M →ₒ S))
        (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) :=
      (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget
        (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) +
        sigAlg.signingOracle pk sk
    let sim_adv : WriterT (QueryLog (M →ₒ S)) (OracleComp spec) (M × S) :=
      simulateQ impl (adv.main pk)
    let ((msg, σ), log) ← sim_adv.run
    let verified ← sigAlg.verify pk msg σ
    return !log.wasQueriedWith msg σ && verified

/-- The success probability of a CMA adversary in the SUF-CMA experiment. -/
noncomputable def UnforgeableAdversary.strongAdvantage
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    (adv : UnforgeableAdversary sigAlg) : ℝ≥0∞ := stronglyUnforgeableExp runtime adv {true}

omit [DecidableEq M] [DecidableEq S] in
lemma unforgeableAdv.advantage_le_strongAdvantage
    {sigAlg : SignatureAlg (OracleComp spec) M PK SK S}
    (runtime : ProbCompRuntime (OracleComp spec))
    (h_pull : ∀ {α β : Type} [MeasurableSpace α] [MeasurableSpace β] (f : α → β),
      Measurable f → ∀ (mx : OracleComp spec α),
        runtime.evalDist (mx >>= fun x => pure (f x)) = (runtime.evalDist mx).map f)
    (adv : UnforgeableAdversary sigAlg) :
    unforgeableAdvantage runtime adv ≤ adv.strongAdvantage runtime := by
  letI : DecidableEq M := Classical.decEq M
  letI : DecidableEq S := Classical.decEq S
  unfold unforgeableAdv.advantage unforgeableExp
    unforgeableAdv.strongAdvantage stronglyUnforgeableExp
  set joint : OracleComp spec ((M × S) × QueryLog (M →ₒ S) × Bool) := do
    let (pk, sk) ← sigAlg.keygen
    let impl : QueryImpl (spec + (M →ₒ S))
        (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) :=
      (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget
        (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) +
        sigAlg.signingOracle pk sk
    let sim_adv : WriterT (QueryLog (M →ₒ S)) (OracleComp spec) (M × S) :=
      simulateQ impl (adv.main pk)
    let ((msg, σ), log) ← sim_adv.run
    let verified ← sigAlg.verify pk msg σ
    pure ((msg, σ), log, verified) with hjoint_def
  have hExp : (runtime.evalDist do
        let (pk, sk) ← sigAlg.keygen
        let impl : QueryImpl (spec + (M →ₒ S))
            (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) :=
          (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget
            (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) +
            sigAlg.signingOracle pk sk
        let sim_adv : WriterT (QueryLog (M →ₒ S)) (OracleComp spec) (M × S) :=
          simulateQ impl (adv.main pk)
        let ((msg, σ), log) ← sim_adv.run
        let verified ← sigAlg.verify pk msg σ
        pure (!log.wasQueried msg && verified)) =
      (fun t : (M × S) × QueryLog (M →ₒ S) × Bool =>
        !t.2.1.wasQueried t.1.1 && t.2.2) <$> runtime.evalDist joint := by
    rw [← h_pull]
    congr 1
    simp only [hjoint_def, monad_norm]
  have hStrong : (runtime.evalDist do
        let (pk, sk) ← sigAlg.keygen
        let impl : QueryImpl (spec + (M →ₒ S))
            (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) :=
          (HasQuery.toQueryImpl (spec := spec) (m := OracleComp spec)).liftTarget
            (WriterT (QueryLog (M →ₒ S)) (OracleComp spec)) +
            sigAlg.signingOracle pk sk
        let sim_adv : WriterT (QueryLog (M →ₒ S)) (OracleComp spec) (M × S) :=
          simulateQ impl (adv.main pk)
        let ((msg, σ), log) ← sim_adv.run
        let verified ← sigAlg.verify pk msg σ
        pure (!log.wasQueriedWith msg σ && verified)) =
      (fun t : (M × S) × QueryLog (M →ₒ S) × Bool =>
        !t.2.1.wasQueriedWith t.1.1 t.1.2 && t.2.2) <$> runtime.evalDist joint := by
    rw [← h_pull]
    congr 1
    simp only [hjoint_def, monad_norm]
  rw [hExp, hStrong, ← probEvent_eq_eq_probOutput, ← probEvent_eq_eq_probOutput,
    probEvent_map, probEvent_map]
  refine probEvent_mono fun t _ hv => ?_
  obtain ⟨hfresh, hver⟩ := (Bool.and_eq_true _ _).mp hv
  refine (Bool.and_eq_true _ _).mpr ⟨?_, hver⟩
  cases hqw : t.2.1.wasQueriedWith t.1.1 t.1.2
  · rfl
  · rw [QueryLog.wasQueried_of_wasQueriedWith hqw] at hfresh
    exact absurd hfresh (by simp)

end SignatureAlg
