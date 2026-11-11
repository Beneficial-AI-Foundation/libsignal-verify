/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Aeneas

/-! # Spec theorem for comparing a byte slice with a byte array

The extraction of `slice == array[..]`, with `slice : &[u8]` and `array : [u8; N]`, indexes the
array with `RangeFull` (`core.array.Array.index` with `core.slice.index.SliceIndexRangeFullSlice`)
and then calls `core.slice.cmp.PartialEqSlice.eq`. All three are models in the Aeneas standard
library. The Aeneas library has no model of `<[T] as PartialEq<[U; N]>>::eq`, which is why the
translation patch `core-curve-slice_eq_array` compares two slices.

At the pinned rustc, `<[T] as PartialEq<[U; N]>>::eq` is `false` unless the slice has length `N`
and otherwise compares the two arrays. `<[T] as PartialEq<[U]>>::eq` is `false` on unequal lengths
and otherwise compares the elements. For `u8` both are equality of the byte lists. The theorem
states that the two-call form succeeds and returns whether the byte lists are equal. It is a
property of the models.

**Source**: `library/core/src/array/equality.rs` and `library/core/src/slice/cmp.rs`, rustc
1.100.0-nightly (923c95cdf 2026-09-16), the `rust_channel` of the pinned Aeneas release in
`rust/aeneas-config.yml`.
-/

open Aeneas Aeneas.Std Result

namespace Aeneas.Std.core.array.equality

/-- **Spec and proof concerning `slice == array[..]` on bytes**: for every byte slice `s` and byte
array `a`, indexing `a` with `RangeFull` and comparing the result with `s` succeeds and returns
`true` exactly when the byte lists of `s` and `a` are equal. -/
theorem slice_eq_array_u8 {N : Usize} (s : Slice U8) (a : Array U8 N) :
    (do
      let s1 ← core.array.Array.index
        (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeFullSlice U8)) a ()
      core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8 s s1)
      ⦃ b => b = decide (s.val = a.val) ⦄ := by
  have hne : ∀ x y : U8, core.cmp.PartialEqU8.ne x y ⦃ b => b ↔ ¬ x = y ⦄ := by
    intro x y
    simp [core.cmp.impls.PartialEqU8.ne, liftFun2]
  have hidx : core.array.Array.index
      (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeFullSlice U8)) a () =
      ok a.to_slice := rfl
  rw [hidx, bind_ok]
  refine WP.spec_mono (core.slice.cmp.PartialEqSlice.eq_homo_spec core.cmp.PartialEqU8 s
    a.to_slice hne) fun b hb => ?_
  rw [Slice.eq_iff] at hb
  have hP : b = true ↔ s.val = a.val := by simpa [Array.to_slice] using hb
  cases b <;> simp_all

end Aeneas.Std.core.array.equality
