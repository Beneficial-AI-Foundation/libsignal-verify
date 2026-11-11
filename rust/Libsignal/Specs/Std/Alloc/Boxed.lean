/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Libsignal.Proofs.Std.Alloc.Boxed.AsRef

/-!
# Spec summary: `library/alloc/src/boxed.rs`

This file freezes the specification of `<Box<T, A> as AsRef<T>>::as_ref` from the Rust standard
library, which the extraction places in the namespace `libsignal_protocol.Box`. The theorem is
restated with `recall` and has a `#guard_msgs` check on the axioms it depends on.
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
