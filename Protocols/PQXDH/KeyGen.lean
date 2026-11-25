/-
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the terms of the LICENSE file in the project root.
Authors: Alessandro D'Angelo
-/
import Libsignal.Proofs.Core.Curve.KeyPair
import Libsignal.Proofs.Core.Curve.PrivateKey
import Protocols.PQXDH.BranchHelpers
import Protocols.PQXDH.Contracts
import Protocols.PQXDH.Params
import Protocols.Realization.RustOracleComp
import VCVio.EvalDist.EvalDistEq

/-!
# Core's `KeyPair::generate`: its law on `P.coins`, and `GenerateTotal`

Alice draws her generator state from `P.coins` and passes it to Core's `KeyPair::generate`. For
every law `P.coins`, `generate` and `readClampDerive` give the same law on the returned key pair
and generator state, and a fault counts only as missing mass.

The result says nothing about the bytes that `fill_bytes` returns on a state drawn from `P.coins`,
nor about the state it leaves. It does not relate Alice's key to `P.ecKeygen`, nor her
encapsulation state to `P.coins`; each of these needs a separate result.

`generateTotal_of_contracts` proves the contract `GenerateTotal` from `ClampIntegerContract` and
`X25519SecretContract`, the contracts on curve25519-dalek's `clamp_integer` and on x25519-dalek's
`StaticSecret` and public-key derivation. It uses the totality of the generator's `CryptoRng` view,
which `GenerateTotal` assumes, and not the totality of its `rand::Rng` view.
-/

open Protocols.Realization

namespace Protocols.PQXDH

variable {Rand Msg C IdC IdK : Type}

/-- The law of Core's `generate` on a state drawn from `P.coins` is the law of `readClampDerive` on
that state. Every event has the same probability under both, and a fault counts only as missing
mass. The statement holds for every law `P.coins`; it says nothing about what `fill_bytes` returns
on a state from `P.coins`, nor about the state it leaves. The two computations are also equal as
terms, by `generate_eq_readClampDerive` at each state. Use that equation where the kind of a fault
matters: the law does not tell a panic from a divergence. -/
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

section Total

open Aeneas Aeneas.Std Result

/-- Core's `KeyPair::generate` satisfies `GenerateTotal` when curve25519-dalek's `clamp_integer`
satisfies `ClampIntegerContract` and x25519-dalek's `StaticSecret` and public-key derivation
satisfy `X25519SecretContract`. The proof reads the generator through its `CryptoRng` view only:
the premise of `GenerateTotal` that the `rand::Rng` view is total is not used. -/
theorem generateTotal_of_contracts (hClamp : ClampIntegerContract)
    (hX : X25519SecretContract) : GenerateTotal := by
  intro R rng crng Dom hRng _ r hr
  have hgen : curve.KeyPair.generate rng crng r =
      libsignal_core.curve.KeyPair.readClampDerive crng r :=
    libsignal_core.curve.KeyPair.generate_eq_readClampDerive rng crng r
  obtain ⟨⟨r₁, s⟩, hfill, hpost⟩ := exists_ok_of_spec
    ((hRng r hr).2.2 (Array.to_slice (Array.repeat 32#usize 0#u8)))
  obtain ⟨-, hr₁⟩ := hpost
  obtain ⟨c, hc, hcc⟩ := hClamp (Array.from_slice (Array.repeat 32#usize 0#u8) s)
  obtain ⟨sec, hsec, hbytes⟩ := hX.1 c
  obtain ⟨pk, a, hpk, ha⟩ := hX.2 sec
  have hpub : curve.PrivateKey.public_key { key := .DjbPrivateKey c } =
      .ok (.Ok { key := .DjbPublicKey a }) := by
    have h := libsignal_core.curve.PrivateKey.public_key_djb_eq c
    simp only [hcc, hsec, hpk, ha, bind_ok] at h
    exact h
  rw [hgen]
  simp only [libsignal_core.curve.KeyPair.readClampDerive, hfill, bind_ok, uncurry_apply_pair, hc,
    hsec, hpk, ha, hbytes, WP.spec_ok]
  exact ⟨hpub, hr₁⟩

end Total

end Protocols.PQXDH
