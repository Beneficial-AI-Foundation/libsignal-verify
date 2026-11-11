/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Aeneas

/-! # Spec theorems for `Vec::extend_from_slice`

`alloc.vec.Vec.extend_from_slice` is the Aeneas model of Rust's
`alloc::vec::Vec::<T>::extend_from_slice`, defined in the Aeneas standard library
(`Aeneas/Std/Vec.lean`). The model checks the combined length before cloning and returns
`fail .panic` if it exceeds `Usize.max`. Otherwise it clones the slice, propagates a failure or
divergence of the clone, and on success appends the cloned contents. Capacity is not represented.

When every element of the slice clones successfully to itself, as for the byte type `U8`, the two
theorems together characterise success by the length bound and identify the result as the
concatenation: `extend_from_slice_spec` covers the bounded case and `extend_from_slice_overflow`
the overflowing one.

The approach follows `extend_from_slice_U8_spec` in SparsePostQuantumRatchet-verify
(`Spqr/Specs/Aeneas/VecExtendFromSlice.lean`, Hoang Le Truong, Apache 2.0), generalised here to
any clone instance that returns its argument, as in `alloc.slice.Slice.to_vec_spec`.

**Source**: Aeneas standard library, `Aeneas/Std/Vec.lean`
(`alloc::vec::{alloc::vec::Vec<@T>}::extend_from_slice`).
-/

open Aeneas Aeneas.Std Result

namespace Aeneas.Std.alloc.vec.Vec

/-
natural language description:

• If `v.length + s.length ≤ Usize.max`, attempts to clone `s` and, if cloning succeeds, returns
  the vector whose contents are `v` followed by the clones; a clone failure or divergence
  propagates. Otherwise panics before cloning.

natural language specs:

• If every element of `s` clones to itself and `v.length + s.length ≤ Usize.max`, the call
  succeeds and returns a vector with contents `v.val ++ s.val` and length
  `v.length + s.length`.
• If `Usize.max < v.length + s.length`, the call panics.
-/

/-- **Spec theorem for `alloc.vec.Vec.extend_from_slice`**:
if every element of `s` clones to itself and the combined length fits in `usize`, the call
succeeds and appends `s` to `v`. -/
@[step]
theorem extend_from_slice_spec {T : Type} (cloneInst : core.clone.Clone T)
    (v : alloc.vec.Vec T) (s : Slice T)
    (h_clone : ∀ x ∈ s.val, cloneInst.clone x = ok x)
    (h_len : v.length + s.length ≤ Usize.max) :
    extend_from_slice cloneInst v s ⦃ (v' : alloc.vec.Vec T) =>
      v'.val = v.val ++ s.val ∧ v'.length = v.length + s.length ⦄ := by
  have h_cl : Slice.clone cloneInst.clone s = ok s := by
    obtain ⟨s', h_eq, hs⟩ := WP.spec_imp_exists (Slice.clone_spec h_clone)
    rw [h_eq, ← hs]
  unfold extend_from_slice
  rw [dif_pos h_len]
  grind

/-- `alloc.vec.Vec.extend_from_slice` panics when the combined length exceeds `usize`. -/
theorem extend_from_slice_overflow {T : Type} (cloneInst : core.clone.Clone T)
    (v : alloc.vec.Vec T) (s : Slice T) (h_len : Usize.max < v.length + s.length) :
    extend_from_slice cloneInst v s = fail .panic := by
  unfold extend_from_slice
  rw [dif_neg (Nat.not_le.mpr h_len)]

-- `step` applies `extend_from_slice_spec` to a byte-vector call: the clone premise for `U8` is
-- discharged automatically and the length premise is taken from the context.
example (v : alloc.vec.Vec U8) (s : Slice U8) (h_len : v.length + s.length ≤ Usize.max) :
    extend_from_slice core.clone.CloneU8 v s ⦃ (v' : alloc.vec.Vec U8) =>
      v'.val = v.val ++ s.val ⦄ := by
  step*

end Aeneas.Std.alloc.vec.Vec
