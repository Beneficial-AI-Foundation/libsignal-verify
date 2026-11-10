/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Aeneas

/-! # Spec theorem for `Box::<[T]>::from(Vec<T>)`

`alloc.vec.FromBoxSliceVec.from` is the Aeneas model of `<Box<[T]> as From<Vec<T>>>::from`, defined
in the Aeneas standard library (`Aeneas/Std/Vec.lean`, and `Aeneas/Std/Alloc/Vec.lean` from the
release `nightly-2026.10.30-de16f3c`). At the pinned rustc the impl is
`fn from(v: Vec<T, A>) -> Self { v.into_boxed_slice() }`, so the extraction of `Box::from(vec)` and
of `vec.into_boxed_slice()` is the same call. The extraction does not model `into_boxed_slice`
itself, which is why the translation patches `protocol-kem-box_from_vec` and
`protocol-identity_key-box_from_vec` write `Box::from(vec)`.

The theorem is a property of the model. It states that the call succeeds and returns the slice of
the vector, which excludes failure and divergence.

**Source**: `library/alloc/src/vec/mod.rs`, `impl From<Vec<T, A>> for Box<[T], A>`, rustc
1.100.0-nightly (923c95cdf 2026-09-16), the `rust_channel` of the pinned Aeneas release in
`rust/aeneas-config.yml`.
-/

open Aeneas Aeneas.Std Result

namespace Aeneas.Std.alloc.vec.FromBoxSliceVec

/-- **Spec and proof concerning `alloc.vec.FromBoxSliceVec.from`**: for every vector `v`, the call
succeeds and returns the slice `v.deref` with the elements of `v`. -/
theorem from_deref {T : Type} (v : alloc.vec.Vec T) :
    alloc.vec.FromBoxSliceVec.from v ⦃ s => s = alloc.vec.Vec.deref v ⦄ :=
  WP.spec_mono (alloc.vec.FromBoxSliceVec.from_spec v) fun s ⟨_, hv⟩ =>
    Slice.ext _ _ (by simpa [alloc.vec.Vec.deref] using hv)

end Aeneas.Std.alloc.vec.FromBoxSliceVec
