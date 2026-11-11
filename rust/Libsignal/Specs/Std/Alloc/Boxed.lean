/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Libsignal.Proofs.Std.Alloc.Boxed.AsRef
import Libsignal.Proofs.Std.Alloc.Boxed.Convert

/-!
# Spec summary: `library/alloc/src/boxed.rs` and `library/alloc/src/boxed/convert.rs`

This file freezes the specifications of `<Box<T, A> as AsRef<T>>::as_ref` and of the conversion
`Box::<[u8]>::from(&[u8])` from the Rust standard library. The extraction places `as_ref` in the
namespace `libsignal_protocol.Box`. Each theorem is restated with `recall` and has a
`#guard_msgs` check on the axioms it depends on.
-/

open Aeneas Aeneas.Std Result libsignal_protocol in
recall libsignal_protocol.Box.Insts.CoreConvertAsRef.as_ref_spec {T : Type} (A : Type) (x : T) :
    Box.Insts.CoreConvertAsRef.as_ref A x ⦃ y => y = x ⦄

/--
info: 'libsignal_protocol.Box.Insts.CoreConvertAsRef.as_ref_spec' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms libsignal_protocol.Box.Insts.CoreConvertAsRef.as_ref_spec

open Aeneas Aeneas.Std Result in
recall Aeneas.Std.alloc.boxed.from_slice_u8 (s : Slice U8) :
    (do
      let v ← alloc.slice.Slice.to_vec core.clone.CloneU8 s
      alloc.vec.FromBoxSliceVec.from v) ⦃ r => r = s ⦄

/--
info: 'Aeneas.Std.alloc.boxed.from_slice_u8' depends on axioms:
 [propext,
 Classical.choice,
 Quot.sound]
-/
#guard_msgs (whitespace := lax) in
#print axioms Aeneas.Std.alloc.boxed.from_slice_u8
