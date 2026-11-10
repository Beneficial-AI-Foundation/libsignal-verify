/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Aeneas

/-! # Spec theorem for `Box::<[u8]>::from(&[u8])`

The extraction of `Box::from(slice.to_vec())`, with `slice : &[u8]`, is `alloc.slice.Slice.to_vec`
followed by `alloc.vec.FromBoxSliceVec.from`. Both are models in the Aeneas standard library. The
Aeneas library has no model of `<Box<[T]> as From<&[T]>>::from`, which is why the translation patch
`protocol-kem-box_from_slice` writes the two-call form.

At the pinned rustc, `From<&[T]> for Box<[T]>` clones each element of the slice into a new box, and
`to_vec` followed by `Box::from(vec)` clones each element into a vector that the box then takes over.
For `u8` the clone is the identity. The theorem states that the two-call form succeeds and
returns a slice equal to its argument. It is a property of the models.

**Source**: `library/alloc/src/boxed/convert.rs`, `impl From<&[T]> for Box<[T]>`, rustc
1.100.0-nightly (923c95cdf 2026-09-16), the `rust_channel` of the pinned Aeneas release in
`rust/aeneas-config.yml`.
-/

open Aeneas Aeneas.Std Result

namespace Aeneas.Std.alloc.boxed

/-- **Spec and proof concerning `Box::from(slice.to_vec())` on bytes**: for every byte slice `s`,
the call `alloc.slice.Slice.to_vec` followed by `alloc.vec.FromBoxSliceVec.from` succeeds and
returns `s`. -/
theorem from_slice_u8 (s : Slice U8) :
    (do
      let v ← alloc.slice.Slice.to_vec core.clone.CloneU8 s
      alloc.vec.FromBoxSliceVec.from v) ⦃ r => r = s ⦄ :=
  WP.spec_bind (alloc.slice.Slice.to_vec_spec core.clone.CloneU8 s (fun _ _ => rfl))
    fun v hs => WP.spec_mono (alloc.vec.FromBoxSliceVec.from_spec v) fun r ⟨_, hr⟩ =>
      Slice.ext _ _ (by simpa [hs, alloc.vec.Vec.val] using hr)

end Aeneas.Std.alloc.boxed
