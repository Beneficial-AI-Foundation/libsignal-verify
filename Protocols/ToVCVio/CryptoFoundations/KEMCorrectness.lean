/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSES/Apache-2.0.txt.
Authors: Beneficial AI Foundation
Ported with changes from https://github.com/Beneficial-AI-Foundation/secure-messaging, see
Protocols/ATTRIBUTION.md.
-/
import VCVio.CryptoFoundations.KeyEncapMech

/-!
# Quantitative KEM correctness

The correctness experiment `KEMScheme.CorrectExp` generates a key pair, encapsulates to the public
key and decapsulates the ciphertext with the secret key. It returns `true` when decapsulation
recovers the encapsulated key. The **correctness error** of a KEM under a runtime is the missing
success mass of this experiment,

`ε = 1 - Pr[CorrectExp = true]`,

and the KEM is **`δ`-correct** when `ε ≤ δ`. Because the error is missing success mass and not
the probability of the output `false`, it also counts executions that return no Boolean, such as
a computation that panics or does not terminate. So `ε = 0` is exactly VCVio's
`KEMScheme.PerfectlyCorrect`, even for a runtime whose output distribution has total mass below
one (`correctnessError_eq_zero_iff_perfectlyCorrect`).

The declarations `correctnessError`, `correctnessError_eq_zero_iff_perfectlyCorrect` and
`deltaCorrect` come from `ToVCVio/CryptoFoundations/KeyEncapMech.lean` of secure-messaging at
`8369ee7`. This file restates them for the subprobability API of the pinned VCVio.
-/

open OracleSpec OracleComp ENNReal

namespace KEMScheme

variable {m : Type → Type} [Monad m] {K PK SK C : Type} [DecidableEq K]

/-- Correctness error of `kem` under `runtime`: the missing success mass
`1 - Pr[CorrectExp = true]`. It counts both a `false` result and the mass of executions that
return nothing. -/
noncomputable def correctnessError (kem : KEMScheme m K PK SK C)
    (runtime : ProbCompRuntime m) : ℝ≥0∞ :=
  1 - Pr[= true | runtime.evalDist kem.CorrectExp]

/-- `δ`-correctness of `kem` under `runtime`: the correctness error is at most `δ`. -/
def deltaCorrect (kem : KEMScheme m K PK SK C) (runtime : ProbCompRuntime m) (δ : ℝ≥0∞) :
    Prop :=
  kem.correctnessError runtime ≤ δ

/-- Zero correctness error is VCVio's perfect correctness, with no totality assumption on the
runtime. -/
theorem correctnessError_eq_zero_iff_perfectlyCorrect (kem : KEMScheme m K PK SK C)
    (runtime : ProbCompRuntime m) :
    kem.correctnessError runtime = 0 ↔ kem.PerfectlyCorrect runtime := by
  rw [correctnessError, PerfectlyCorrect, tsub_eq_zero_iff_le]
  exact ⟨fun h => le_antisymm probOutput_le_one h, fun h => h.ge⟩

/-- A `δ`-correct KEM's correctness experiment succeeds with probability at least `1 - δ`. -/
theorem one_sub_le_probOutput_of_deltaCorrect {kem : KEMScheme m K PK SK C}
    {runtime : ProbCompRuntime m} {δ : ℝ≥0∞} (h : kem.deltaCorrect runtime δ) :
    1 - δ ≤ Pr[= true | runtime.evalDist kem.CorrectExp] := by
  rw [deltaCorrect, correctnessError] at h
  exact tsub_le_iff_tsub_le.mp h

end KEMScheme
