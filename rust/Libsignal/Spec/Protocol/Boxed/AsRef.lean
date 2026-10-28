/-
Copyright 2026 The Beneficial AI Foundation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Alessandro D'Angelo
-/
import Libsignal.Translated.Protocol.FunsExternal

/-! # Spec theorem for `Box::as_ref`

`Box.Insts.CoreConvertAsRef.as_ref` is the Lean model of `<Box<T, A> as AsRef<T>>::as_ref`.
The Rust body is `self`: deref coercion turns `&Box<T, A>` into `&T`, a shared borrow of the
boxed value. The call allocates nothing, copies nothing and has no panicking path. Aeneas
translates both `Box<T, A>` and `&T` as `T`, so the model in `Protocol/FunsExternal.lean` is the
identity `fun x => ok x`.

The model is a modelling choice that is trusted, not verified: no Lean proof connects it to the
Rust source or to the Charon/Aeneas translation. The theorem below is a property of the model.
It states that the call succeeds and returns its argument, which excludes failure and
divergence.

**Source**: `library/alloc/src/boxed.rs`, lines 2428:0-2432:1, rustc 1.100.0-nightly
(923c95cdf 2026-09-16), the `rust_channel` of the pinned Aeneas release in
`rust/aeneas-config.yml`.
-/

open Aeneas Aeneas.Std Result

namespace libsignal_protocol.Box.Insts.CoreConvertAsRef

/-- **Spec and proof concerning `Box.Insts.CoreConvertAsRef.as_ref`**: for every value type `T`,
allocator type `A` and value `x`, the call succeeds and returns `x`. -/
@[step]
theorem as_ref_spec {T : Type} (A : Type) (x : T) :
    Box.Insts.CoreConvertAsRef.as_ref A x ⦃ y => y = x ⦄ := by
  simp [Box.Insts.CoreConvertAsRef.as_ref]

end libsignal_protocol.Box.Insts.CoreConvertAsRef
