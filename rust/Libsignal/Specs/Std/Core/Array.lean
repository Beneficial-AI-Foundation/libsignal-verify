/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Mathlib.Tactic.Recall
import Libsignal.Proofs.Std.Core.Array.Equality

/-!
# Spec summary: `library/core/src/array/equality.rs`

This file freezes the specification of the comparison of a byte slice with a byte array from the
Rust standard library, through its models in the Aeneas standard library. The theorem is restated
with `recall` and has a `#guard_msgs` check on the axioms it depends on.
-/

open Aeneas Aeneas.Std Result in
recall Aeneas.Std.core.array.equality.slice_eq_array_u8 {N : Usize} (s : Slice U8)
    (a : Array U8 N) :
    (do
      let s1 ← core.array.Array.index
        (core.ops.index.IndexSlice (core.slice.index.SliceIndexRangeFullSlice U8)) a ()
      core.slice.cmp.PartialEqSlice.eq core.cmp.PartialEqU8 s s1)
      ⦃ b => b = decide (s.val = a.val) ⦄

/--
info: 'Aeneas.Std.core.array.equality.slice_eq_array_u8' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Aeneas.Std.core.array.equality.slice_eq_array_u8
