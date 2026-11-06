/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Mathlib.Tactic.Recall
import Libsignal.Proofs.Std.Alloc.Vec.ExtendFromSlice

/-!
# Spec summary: `library/alloc/src/vec/mod.rs`

This file freezes the specifications of `Vec::extend_from_slice` from the Rust standard library,
as the Aeneas standard library models it. Each theorem is restated with `recall` and has a
`#guard_msgs` check on the axioms it depends on.
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
