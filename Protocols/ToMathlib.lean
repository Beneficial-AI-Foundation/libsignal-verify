/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under the Apache License 2.0, as in the PQXDH-model repository.
Authors: Ben Hamlin
-/
import ToMathlib.Control.WriterT

/-! # Lift laws for `WriterT` over append-based logs

VCVio's `ToMathlib.Control.WriterT` proves `LawfulMonadLift m (WriterT ω m)` for the `Monoid ω`
instance of `WriterT`. The PQXDH model uses the `EmptyCollection`/`Append` instance instead (list
logs), whose `MonadLift` is `WriterT.liftTell ∅`. This file supplies the matching lawfulness
instance. Staged for upstreaming into VCVio's `ToMathlib`. -/

instance instLawfulMonadLiftWriterTAppend {ω : Type} {m : Type → Type}
    [Monad m] [EmptyCollection ω] [Append ω] [LawfulAppend ω] [LawfulMonad m] :
    LawfulMonadLift m (WriterT ω m) where
  monadLift_pure x := map_pure (·, ∅) x
  monadLift_bind {α β} x y := by
    change WriterT.mk _ = WriterT.mk _
    simp [WriterT.monadLift_def', WriterT.mk, WriterT.run]
