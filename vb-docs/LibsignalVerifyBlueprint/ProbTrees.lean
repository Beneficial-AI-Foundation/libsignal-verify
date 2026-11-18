import VCVio.OracleComp.ProbComp.Basic
import VCVio.OracleComp.Constructions.SampleableType.Basic
import VCVio.OracleComp.Constructions.UniformFinMeasure
import VCVio.OracleComp.EvalDist.Measure
import VCVio.EvalDist.ProbabilityNotation

/-!
# Three probabilistic programs as trees

Examples for the first chapter of the book. Each program draws uniformly from `{0, 1}`, either
with `uniformFin 1` and a comparison with `1`, or with the sampler `$ᵗ Bool`. The theorems state
the tree of each program and the probabilities of its outputs. They are checked with the pinned
version of VCV-io.
-/

open OracleComp ProbComp
open scoped ENNReal

namespace ProbTrees

/-- `node k` is the tree whose root draws uniformly from `{0, 1}` and whose child at the outcome
`x` is `k x`. -/
abbrev node {α : Type} (k : Fin 2 → ProbComp α) : ProbComp α :=
  PFunctor.FreeM.liftBind (P := unifSpec.toPFunctor) (1 : ℕ) k

/-- A single draw from `{0, 1}` is the node whose children are the leaves `0` and `1`. -/
theorem draw_eq : (uniformFin 1 : ProbComp (Fin 2)) = node pure := rfl

/-- Drawing from `{0, 1}` and continuing with `k` is the node `node k`. -/
theorem node_eq_bind {α : Type} (k : Fin 2 → ProbComp α) :
    node k = uniformFin 1 >>= k := rfl

/-- The shape of a tree: the tree with every leaf label replaced by `()`. -/
def shape {α : Type} (t : ProbComp α) : ProbComp Unit :=
  (fun _ => ()) <$> t

/-- Changing the labels of the leaves does not change the shape. -/
theorem shape_map {α β : Type} (f : α → β) (t : ProbComp α) :
    shape (f <$> t) = shape t := by
  simp [shape]

/-- One draw, and the same truth value twice. -/
def t₁ : ProbComp (Bool × Bool) := do
  let x ← uniformFin 1
  return (x == 1, x == 1)

/-- Two draws, one truth value from each. -/
def t₂ : ProbComp (Bool × Bool) := do
  let x ← uniformFin 1
  let y ← uniformFin 1
  return (x == 1, y == 1)

/-- A second draw only if the first draw gave `true`. -/
def t₃ : ProbComp Bool := do
  let x ← $ᵗ Bool
  let y ← if x then $ᵗ Bool else pure true
  return y

/-- The tree of `t₁`. -/
theorem t₁_eq : t₁ = node (fun x => pure (x == 1, x == 1)) := rfl

/-- The tree of `t₂`. -/
theorem t₂_eq : t₂ = node (fun x => node (fun y => pure (x == 1, y == 1))) := rfl

/-- The sampler of `Bool` is a draw from `{0, 1}`: the outcome `0` stands for `true` and the
outcome `1` for `false`. -/
theorem uniformBool_eq : ($ᵗ Bool : ProbComp Bool) = node (fun i => pure (i == 0)) := by
  change PFunctor.FreeM.liftBind (P := unifSpec.toPFunctor) (1 : ℕ) _ = _
  congr 1
  funext u
  simp
  fin_cases u <;> (refine congrArg PFunctor.FreeM.pure ?_; decide)

/-- The tree of `t₃`. -/
theorem t₃_eq :
    t₃ = node (fun i => if i == 0 then node (fun j => pure (j == 0)) else pure true) := by
  unfold t₃
  rw [uniformBool_eq]
  simp

/-- `t₁` has one draw node. -/
theorem shape_t₁ : shape t₁ = node (fun _ => pure ()) := rfl

/-- `t₂` has three draw nodes. -/
theorem shape_t₂ : shape t₂ = node (fun _ => node (fun _ => pure ())) := rfl

/-- `t₃` has two draw nodes. -/
theorem shape_t₃ :
    shape t₃ = node (fun i => if i == 0 then node (fun _ => pure ()) else pure ()) := by
  unfold shape
  rw [t₃_eq]
  show node _ = node _
  congr 1
  funext i
  by_cases h : (i == 0) = true <;> simp [h]

private theorem two_mul_inv : (2 : ℝ≥0∞) * 2⁻¹ = 1 :=
  ENNReal.mul_inv_cancel two_ne_zero ENNReal.ofNat_ne_top

private theorem half_mul_half : (2⁻¹ : ℝ≥0∞) * 2⁻¹ = 4⁻¹ := by
  rw [← ENNReal.mul_inv (Or.inl two_ne_zero) (Or.inl ENNReal.ofNat_ne_top)]
  norm_num

private theorem half_add_quarter : (2⁻¹ : ℝ≥0∞) + 2⁻¹ * 2⁻¹ = 3 / 4 := by
  rw [ENNReal.eq_div_iff (by norm_num) ENNReal.ofNat_ne_top]
  calc (4 : ℝ≥0∞) * (2⁻¹ + 2⁻¹ * 2⁻¹)
      = 2 * (2 * 2⁻¹) + (2 * 2⁻¹) * (2 * 2⁻¹) := by ring
    _ = 3 := by rw [two_mul_inv]; norm_num

/-- Each outcome of a draw from `{0, 1}` has probability `1/2`. -/
private theorem pr_draw (i : Fin 2) : Pr{let x ← uniformFin 1}[x = i] = 2⁻¹ := by
  have h : (Finset.univ.filter (fun x : Fin 2 => x = i)).card = 1 := by
    fin_cases i <;> decide
  rw [prEvent_uniformFin, h]
  norm_num

/-- Comparing the outcome of a draw from `{0, 1}` with `c` gives each truth value with
probability `1/2`. -/
private theorem pr_draw_beq (c : Fin 2) (b : Bool) :
    Pr{let a ← uniformFin 1}[(a == c) = b] = 2⁻¹ := by
  have h : (Finset.univ.filter (fun a : Fin 2 => (a == c) = b)).card = 1 := by
    fin_cases c <;> cases b <;> decide
  rw [prEvent_uniformFin, h]
  norm_num

/-- The same statement for the term `lift 1`, which is how `simp` displays `uniformFin 1`. -/
private theorem pr_lift_beq (c : Fin 2) (b : Bool) :
    Pr{let a ← (PFunctor.FreeM.lift (P := unifSpec.toPFunctor) (1 : ℕ) : ProbComp (Fin 2))}[(a == c) = b]
      = 2⁻¹ :=
  pr_draw_beq c b

/-- The law of `t₁`: its two outputs are always equal. -/
theorem t₁_pr (b c : Bool) : Pr{let q ← t₁}[q = (b, c)] = if b = c then 2⁻¹ else 0 := by
  unfold t₁
  rw [prEvent_bind_eq_sum_fintype]
  simp only [prEvent_pure, pr_draw]
  rw [Fin.sum_univ_two]
  cases b <;> cases c <;> simp

/-- The law of `t₂`: its two outputs are uniform and independent. -/
theorem t₂_pr (b c : Bool) : Pr{let q ← t₂}[q = (b, c)] = 4⁻¹ := by
  unfold t₂
  rw [prEvent_bind_eq_sum_fintype]
  simp only [prEvent_bind_eq_sum_fintype, prEvent_pure, pr_draw]
  rw [Fin.sum_univ_two]
  cases b <;> cases c <;> simp [Fin.sum_univ_two] <;> exact half_mul_half

/-- The law of `t₃`. -/
theorem t₃_pr (b : Bool) : Pr{let y ← t₃}[y = b] = if b then 3 / 4 else 1 / 4 := by
  rw [t₃_eq, node_eq_bind, prEvent_bind_eq_sum_fintype, Fin.sum_univ_two]
  simp only [pr_draw]
  simp
  rw [pr_lift_beq]
  cases b
  · simp [half_mul_half]
  · simp
    rw [add_comm]
    exact half_add_quarter

/-- Each of the four outputs of `t₁` and `t₂`, taken alone, is uniform on `Bool`. -/
theorem marginal_pr (b : Bool) :
    Pr{let q ← t₁}[q.1 = b] = 2⁻¹ ∧ Pr{let q ← t₁}[q.2 = b] = 2⁻¹ ∧
    Pr{let q ← t₂}[q.1 = b] = 2⁻¹ ∧ Pr{let q ← t₂}[q.2 = b] = 2⁻¹ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · unfold t₁
    rw [prEvent_bind_eq_sum_fintype]
    simp only [prEvent_pure, pr_draw]
    rw [Fin.sum_univ_two]
    cases b <;> simp
  · unfold t₁
    rw [prEvent_bind_eq_sum_fintype]
    simp only [prEvent_pure, pr_draw]
    rw [Fin.sum_univ_two]
    cases b <;> simp
  · unfold t₂
    rw [prEvent_bind_eq_sum_fintype]
    simp only [prEvent_bind_eq_sum_fintype, prEvent_pure, pr_draw]
    rw [Fin.sum_univ_two]
    cases b <;> simp <;> rw [two_mul_inv, mul_one]
  · unfold t₂
    rw [prEvent_bind_eq_sum_fintype]
    simp only [prEvent_bind_eq_sum_fintype, prEvent_pure, pr_draw]
    rw [Fin.sum_univ_two]
    cases b <;> simp <;> rw [← mul_add, ENNReal.inv_two_add_inv_two, mul_one]

/-- The pairs of outputs of `t₁` and `t₂` have different laws. -/
theorem evalDist_ne : 𝒟[t₁] ≠ 𝒟[t₂] := by
  intro h
  have h1 := congrArg (fun μ => μ {((false, true) : Bool × Bool)}) h
  rw [← prEvent_eq_evalDist_singleton, ← prEvent_eq_evalDist_singleton, t₁_pr, t₂_pr] at h1
  simp at h1
  exact ENNReal.inv_ne_zero.2 ENNReal.ofNat_ne_top h1.symm

end ProbTrees
