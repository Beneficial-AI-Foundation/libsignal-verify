/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import VCVio.CryptoFoundations.SecExp
import VCVio.OracleComp.QueryTracking.QueryBound
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.SimSemantics.SimulateQ

open OracleSpec OracleComp

universe u

namespace AEAD

structure Scheme (m : Type → Type u) [Monad m] (Msg Key AD C : Type) where
  encrypt : Key → AD → Msg → m C
  decrypt : Key → AD → C → Option Msg

def withUnif {ι : Type} {spec : OracleSpec ι} {σ : Type}
    (impl : QueryImpl spec (StateT σ ProbComp)) :
    QueryImpl (unifSpec + spec) (StateT σ ProbComp) :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)).liftTarget (StateT σ ProbComp) + impl

variable {Msg Key AD C : Type} [DecidableEq Msg] [SampleableType Key]
  [DecidableEq AD] [DecidableEq C]

def CorrectExp (aead : Scheme ProbComp Msg Key AD C) (msg : Msg) (ad : AD) : ProbComp Bool := do
  let k ← $ᵗ Key
  let c ← aead.encrypt k ad msg
  pure (decide (aead.decrypt k ad c = some msg))

def PerfectlyCorrect (aead : Scheme ProbComp Msg Key AD C) : Prop :=
  ∀ msg ad, Pr[= true | CorrectExp aead msg ad] = 1

structure IND_CPA_Adversary (_aead : Scheme ProbComp Msg Key AD C) where
  run : OracleComp (unifSpec + ((AD × Msg × Msg) →ₒ C)) Bool

def cpaImpl (aead : Scheme ProbComp Msg Key AD C) (k : Key) (b : Bool) :
    QueryImpl (unifSpec + ((AD × Msg × Msg) →ₒ C)) ProbComp :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) +
    fun p : AD × Msg × Msg => (aead.encrypt k p.1 (if b then p.2.2 else p.2.1) : ProbComp C)

def IND_CPA_Game (aead : Scheme ProbComp Msg Key AD C)
    (A : IND_CPA_Adversary aead) : ProbComp Bool := do
  let k ← $ᵗ Key
  let b ← $ᵗ Bool
  let b' ← simulateQ (cpaImpl aead k b) A.run
  pure (b' == b)

noncomputable def IND_CPA_Advantage (aead : Scheme ProbComp Msg Key AD C)
    (A : IND_CPA_Adversary aead) : ℝ :=
  |(Pr[= true | IND_CPA_Game aead A]).toReal - 1 / 2|

def ctxtImpl (aead : Scheme ProbComp Msg Key AD C) (k : Key) :
    QueryImpl ((AD × Msg) →ₒ C) (StateT (List (AD × C)) ProbComp) :=
  fun p => do
    let c ← (aead.encrypt k p.1 p.2 : ProbComp C)
    modify (fun log => log ++ [(p.1, c)])
    pure c

structure INT_CTXT_Adversary (_aead : Scheme ProbComp Msg Key AD C) where
  run : OracleComp (unifSpec + ((AD × Msg) →ₒ C)) (AD × C)

def INT_CTXT_Game (aead : Scheme ProbComp Msg Key AD C)
    (A : INT_CTXT_Adversary aead) : ProbComp Bool := do
  let k ← $ᵗ Key
  let (forge, log) ← (simulateQ (withUnif (ctxtImpl aead k)) A.run).run []
  pure ((aead.decrypt k forge.1 forge.2).isSome && decide (forge ∉ log))

noncomputable def INT_CTXT_Advantage (aead : Scheme ProbComp Msg Key AD C)
    (A : INT_CTXT_Adversary aead) : ℝ :=
  (Pr[= true | INT_CTXT_Game aead A]).toReal

def ctxtVfImpl (aead : Scheme ProbComp Msg Key AD C) (k : Key) :
    QueryImpl (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Bool))
      (StateT (List (AD × C) × Bool) ProbComp) :=
  (show QueryImpl ((AD × Msg) →ₒ C) (StateT (List (AD × C) × Bool) ProbComp) from
    fun p => do
      let c ← (aead.encrypt k p.1 p.2 : ProbComp C)
      modify (fun s => (s.1 ++ [(p.1, c)], s.2))
      pure c) +
  (show QueryImpl ((AD × C) →ₒ Bool) (StateT (List (AD × C) × Bool) ProbComp) from
    fun p => do
      let ok := (aead.decrypt k p.1 p.2).isSome
      modify (fun s => (s.1, s.2 || (ok && decide (p ∉ s.1))))
      pure ok)

structure INT_CTXT_VF_Adversary (_aead : Scheme ProbComp Msg Key AD C) where
  run : OracleComp (unifSpec + (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Bool))) Unit

def INT_CTXT_VF_Game (aead : Scheme ProbComp Msg Key AD C)
    (A : INT_CTXT_VF_Adversary aead) : ProbComp Bool := do
  let k ← $ᵗ Key
  let (_, _, won) ← (simulateQ (withUnif (ctxtVfImpl aead k)) A.run).run ([], false)
  pure won

noncomputable def INT_CTXT_VF_Advantage (aead : Scheme ProbComp Msg Key AD C)
    (A : INT_CTXT_VF_Adversary aead) : ℝ :=
  (Pr[= true | INT_CTXT_VF_Game aead A]).toReal

def ctxtDecImpl (aead : Scheme ProbComp Msg Key AD C) (k : Key) :
    QueryImpl (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Option Msg))
      (StateT (List (AD × C) × Bool) ProbComp) :=
  (show QueryImpl ((AD × Msg) →ₒ C) (StateT (List (AD × C) × Bool) ProbComp) from
    fun p => do
      let c ← (aead.encrypt k p.1 p.2 : ProbComp C)
      modify (fun s => (s.1 ++ [(p.1, c)], s.2))
      pure c) +
  (show QueryImpl ((AD × C) →ₒ Option Msg) (StateT (List (AD × C) × Bool) ProbComp) from
    fun p => do
      modify (fun s => (s.1, s.2 || ((aead.decrypt k p.1 p.2).isSome && decide (p ∉ s.1))))
      pure (aead.decrypt k p.1 p.2))

structure INT_CTXT_D_Adversary (_aead : Scheme ProbComp Msg Key AD C) where
  run : OracleComp (unifSpec + (((AD × Msg) →ₒ C) + ((AD × C) →ₒ Option Msg))) Unit

def INT_CTXT_D_Game (aead : Scheme ProbComp Msg Key AD C)
    (A : INT_CTXT_D_Adversary aead) : ProbComp Bool := do
  let k ← $ᵗ Key
  let (_, _, won) ← (simulateQ (withUnif (ctxtDecImpl aead k)) A.run).run ([], false)
  pure won

noncomputable def INT_CTXT_D_Advantage (aead : Scheme ProbComp Msg Key AD C)
    (A : INT_CTXT_D_Adversary aead) : ℝ :=
  (Pr[= true | INT_CTXT_D_Game aead A]).toReal

omit [DecidableEq Msg] in
/-- Plain INT-CTXT is no harder than the verification-oracle variant: `B` runs `A` and submits
its forgery to the verification oracle. No PQXDH theorem uses this lemma. A proof constructs `B`
and compares the two games under `simulateQ`. -/
theorem INT_CTXT_Advantage_le_INT_CTXT_VF_Advantage
    (aead : Scheme ProbComp Msg Key AD C) (A : INT_CTXT_Adversary aead) :
    ∃ B : INT_CTXT_VF_Adversary aead,
      INT_CTXT_Advantage aead A ≤ INT_CTXT_VF_Advantage aead B := by
  sorry

/-- The verification-oracle variant loses at most the query bound `v`: `A` guesses which of
`B`'s verification queries is the first fresh valid one and outputs it. No PQXDH theorem uses
this lemma. A proof is a hybrid over the `v` verification queries, using `hcorrect` to answer the
honest ones. -/
theorem INT_CTXT_VF_Advantage_le_mul_INT_CTXT_Advantage
    (aead : Scheme ProbComp Msg Key AD C) (hcorrect : PerfectlyCorrect aead)
    (B : INT_CTXT_VF_Adversary aead) (v : ℕ)
    (hv : B.run.IsQueryBoundP (· matches Sum.inr (Sum.inr _)) v) :
    ∃ A : INT_CTXT_Adversary aead,
      INT_CTXT_VF_Advantage aead B ≤ (v : ℝ) * INT_CTXT_Advantage aead A := by
  sorry

omit [DecidableEq Msg] in
/-- Plain INT-CTXT is no harder than the decryption-oracle variant: `B` runs `A` and submits
its forgery to the decryption oracle. No PQXDH theorem uses this lemma. The PQXDH security
theorems assume a bound on `INT_CTXT_D_Advantage` directly. A proof follows
`INT_CTXT_Advantage_le_INT_CTXT_VF_Advantage`. -/
theorem INT_CTXT_Advantage_le_INT_CTXT_D_Advantage
    (aead : Scheme ProbComp Msg Key AD C) (A : INT_CTXT_Adversary aead) :
    ∃ B : INT_CTXT_D_Adversary aead,
      INT_CTXT_Advantage aead A ≤ INT_CTXT_D_Advantage aead B := by
  sorry

/-- The decryption-oracle variant loses at most the query bound `v`. No PQXDH theorem uses this
lemma. A proof follows `INT_CTXT_VF_Advantage_le_mul_INT_CTXT_Advantage`. -/
theorem INT_CTXT_D_Advantage_le_mul_INT_CTXT_Advantage
    (aead : Scheme ProbComp Msg Key AD C) (hcorrect : PerfectlyCorrect aead)
    (B : INT_CTXT_D_Adversary aead) (v : ℕ)
    (hv : B.run.IsQueryBoundP (· matches Sum.inr (Sum.inr _)) v) :
    ∃ A : INT_CTXT_Adversary aead,
      INT_CTXT_D_Advantage aead B ≤ (v : ℝ) * INT_CTXT_Advantage aead A := by
  sorry

end AEAD
