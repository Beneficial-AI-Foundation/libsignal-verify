/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Alessandro D'Angelo
-/
import Libsignal.Proofs.Core.Curve.KeyPair
import Protocols.PQXDH.Params
import Protocols.Realization.RustOracleComp
import VCVio.EvalDist.EvalDistEq

/-!
# The law of PQXDH ephemeral key generation

Alice draws her generator state from `P.coins` and passes it to Core's `KeyPair::generate`. For
every law `P.coins`, `generate` and `readClampDerive` give the same law on the returned key pair
and generator state, and a fault counts only as missing mass.

The result says nothing about the bytes that `fill_bytes` returns on a state drawn from `P.coins`,
nor about the state it leaves. It does not relate Alice's key to `P.ecKeygen`, nor her
encapsulation state to `P.coins`; each of these needs a separate result.
-/

open Protocols.Realization

namespace Protocols.PQXDH

variable {Rand Msg C IdC IdK : Type}

/-- The law of Core's `generate` on a state drawn from `P.coins` is the law of `readClampDerive` on
that state. Every event has the same probability under both, and a fault counts only as missing
mass. The statement holds for every law `P.coins`; it says nothing about what `fill_bytes` returns
on a state from `P.coins`, nor about the state it leaves. -/
theorem generate_coins_evalDistEq (P : Params Rand Msg C IdC IdK) :
    ((do
        let r ← (liftM P.coins : RustOracleComp unifSpec Rand)
        liftResult (curve.KeyPair.generate P.rngInst P.cryptoRngInst r)) :
      RustOracleComp unifSpec (ECKeyPair × Rand)) =ᵈ
    ((do
        let r ← (liftM P.coins : RustOracleComp unifSpec Rand)
        liftResult (libsignal_core.curve.KeyPair.readClampDerive P.cryptoRngInst r)) :
      RustOracleComp unifSpec (ECKeyPair × Rand))
    := by
  have h : ∀ r : Rand, curve.KeyPair.generate P.rngInst P.cryptoRngInst r =
      libsignal_core.curve.KeyPair.readClampDerive P.cryptoRngInst r := fun r =>
    libsignal_core.curve.KeyPair.generate_eq_readClampDerive P.rngInst P.cryptoRngInst r
  simp only [h]
  exact EvalDistEq.rfl

end Protocols.PQXDH
