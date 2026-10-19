/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import VCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import VCVio.OracleComp.SimSemantics.Append
import VCVio.OracleComp.SimSemantics.SimulateQ

/-!
# Nominal-group DDH assumptions
-/

open OracleSpec OracleComp ENNReal

namespace Protocols.PQXDH.DiffieHellman

def NominalDDHAdversary (PK : Type) := PK → PK → PK → ProbComp Bool

def nominalDDHExpReal {KP PK : Type} (keygen : ProbComp KP) (pk : KP → PK)
    (dh : KP → PK → PK) (adversary : NominalDDHAdversary PK) : ProbComp Bool := do
  let kpA ← keygen
  let kpB ← keygen
  adversary (pk kpA) (pk kpB) (dh kpA (pk kpB))

def nominalDDHExpRand {KP PK : Type} (keygen : ProbComp KP) (pk : KP → PK)
    (adversary : NominalDDHAdversary PK) : ProbComp Bool := do
  let kpA ← keygen
  let kpB ← keygen
  let kpC ← keygen
  adversary (pk kpA) (pk kpB) (pk kpC)

noncomputable def nominalDDHDistAdvantage {KP PK : Type} (keygen : ProbComp KP)
    (pk : KP → PK) (dh : KP → PK → PK) (adversary : NominalDDHAdversary PK) : ℝ :=
  |(Pr[= true | nominalDDHExpReal keygen pk dh adversary]).toReal -
    (Pr[= true | nominalDDHExpRand keygen pk adversary]).toReal|

section Nominal

variable {F : Type} [Field F]
variable {G : Type} [AddCommGroup G] [Module F G]
variable [SampleableType F]

def groupKeygen (g : G) : ProbComp (G × F) := do
  let a ← $ᵗ F
  return (a • g, a)

lemma ddhExpReal_eq_nominalDDHExpReal (g : G) (A : _root_.DiffieHellman.DDHAdversary F G) :
    _root_.DiffieHellman.ddhExpReal g A
      = nominalDDHExpReal (groupKeygen (F := F) g) Prod.fst
        (fun kp pk => kp.2 • pk) (A g) := by
  simp [_root_.DiffieHellman.ddhExpReal, nominalDDHExpReal, groupKeygen, smul_smul]

lemma ddhExpRand_eq_nominalDDHExpRand (g : G) (A : _root_.DiffieHellman.DDHAdversary F G) :
    _root_.DiffieHellman.ddhExpRand g A
      = nominalDDHExpRand (groupKeygen (F := F) g) Prod.fst (A g) := by
  simp [_root_.DiffieHellman.ddhExpRand, nominalDDHExpRand, groupKeygen]

lemma ddhDistAdvantage_eq_nominalDDHDistAdvantage (g : G)
    (A : _root_.DiffieHellman.DDHAdversary F G) :
    _root_.DiffieHellman.ddhDistAdvantage g A
      = nominalDDHDistAdvantage (groupKeygen (F := F) g) Prod.fst
        (fun kp pk => kp.2 • pk) (A g) := by
  unfold _root_.DiffieHellman.ddhDistAdvantage nominalDDHDistAdvantage
  rw [ddhExpReal_eq_nominalDDHExpReal, ddhExpRand_eq_nominalDDHExpRand]

end Nominal

section Gap

variable {F : Type} [Field F]
variable {G : Type} [AddCommGroup G] [Module F G]

def IsDH (g X Y Z : G) : Prop := ∃ x y : F, X = x • g ∧ Y = y • g ∧ Z = (x * y) • g

def GapDHAdversary (_F G : Type) :=
  G → G → G → OracleComp (unifSpec + ((G × G × G) →ₒ Bool)) G

open Classical in
noncomputable def ddhOracle (g : G) :
    QueryImpl (unifSpec + ((G × G × G) →ₒ Bool)) ProbComp :=
  (HasQuery.toQueryImpl (spec := unifSpec) (m := ProbComp)) +
    fun q : G × G × G => (pure (decide (IsDH (F := F) g q.1 q.2.1 q.2.2)) : ProbComp Bool)

variable [SampleableType F] [DecidableEq G]

noncomputable def gapDHExp (g : G) (adversary : GapDHAdversary F G) : ProbComp Bool := do
  let a ← $ᵗ F
  let b ← $ᵗ F
  let h ← simulateQ (ddhOracle (F := F) g) (adversary g (a • g) (b • g))
  return decide (h = (a * b) • g)

noncomputable def gapDHAdvantage (g : G) (adversary : GapDHAdversary F G) : ℝ :=
  (Pr[= true | gapDHExp g adversary]).toReal

end Gap

end Protocols.PQXDH.DiffieHellman
