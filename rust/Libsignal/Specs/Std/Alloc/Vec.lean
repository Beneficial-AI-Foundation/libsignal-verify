/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Libsignal.Proofs.Std.Alloc.Vec.ExtendFromSlice

/-!
# Spec summary: `alloc::vec::Vec`

This file freezes the specifications of `alloc::vec::Vec::extend_from_slice` and of the conversion
`Box::<[T]>::from(Vec<T>)` from the Rust standard library, through their models in the Aeneas
standard library. Each theorem is restated with `recall` and has a `#guard_msgs` check on the axioms
it depends on. For the conversion, the theorem is `alloc.vec.FromBoxSliceVec.from_spec` of the
Aeneas library itself.

At the pinned rustc, `impl From<Vec<T>> for Box<[T]>` is
`fn from(v) -> Self { v.into_boxed_slice() }` (`library/alloc/src/vec/mod.rs`). So `Box::from(vec)`
and `vec.into_boxed_slice()` run the same std code. Their extracted Lean calls differ. The Aeneas
library models `From` as `alloc.vec.FromBoxSliceVec.from`, and it has no model of
`into_boxed_slice`, which the extraction declares as an axiom. The translation patches
`protocol-kem-box_from_vec`, `protocol-identity_key-box_from_vec` and `core-curve-box_from_vec`
therefore write `Box::from(vec)`, so that the extracted code calls the model.
-/

open Aeneas Aeneas.Std Result in
recall Aeneas.Std.alloc.vec.Vec.extend_from_slice_spec {T : Type} (cloneInst : core.clone.Clone T)
    (v : alloc.vec.Vec T) (s : Slice T)
    (h_clone : ∀ x ∈ s.val, cloneInst.clone x = ok x)
    (h_len : v.length + s.length ≤ Usize.max) :
    alloc.vec.Vec.extend_from_slice cloneInst v s ⦃ (v' : alloc.vec.Vec T) =>
      v'.val = v.val ++ s.val ∧ v'.length = v.length + s.length ⦄

/--
info: 'Aeneas.Std.alloc.vec.Vec.extend_from_slice_spec' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Aeneas.Std.alloc.vec.Vec.extend_from_slice_spec

open Aeneas Aeneas.Std Result in
recall Aeneas.Std.alloc.vec.Vec.extend_from_slice_overflow {T : Type}
    (cloneInst : core.clone.Clone T) (v : alloc.vec.Vec T) (s : Slice T)
    (h_len : Usize.max < v.length + s.length) :
    alloc.vec.Vec.extend_from_slice cloneInst v s = fail .panic

/--
info: 'Aeneas.Std.alloc.vec.Vec.extend_from_slice_overflow' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Aeneas.Std.alloc.vec.Vec.extend_from_slice_overflow

open Aeneas Aeneas.Std Result in
recall Aeneas.Std.alloc.vec.FromBoxSliceVec.from_spec {T : Type _} (v : alloc.vec.Vec T) :
    alloc.vec.FromBoxSliceVec.from v ⦃ s => s.length = v.length ∧ s.val = v.val ⦄

/--
info: 'Aeneas.Std.alloc.vec.FromBoxSliceVec.from_spec' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Aeneas.Std.alloc.vec.FromBoxSliceVec.from_spec
