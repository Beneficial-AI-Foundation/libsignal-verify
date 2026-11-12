/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin, Alessandro D'Angelo
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import Libsignal.Translated.Protocol.Funs
import Protocols.PQXDH.Defs
import Protocols.ToVCVio.CryptoFoundations.AEAD

/-!
# Parameters of the Full realization

`Params` collects what the Full realization takes from outside the extracted code. The caller
chooses the two random-number-generator instances, as in Rust, where every entry point is generic
in its generator. The other four fields are modelling choices, each with its own ledger row. The
file also provides uniform sampling of bytes and byte arrays, which the AEAD and UAKE definitions
need for 32-byte keys, following PQXDH-model (`PQXDH/Aeneas/Full/UAKE/Defs.lean:52-64`).

`EntryPoints` packages the two entry points of the handshake, and `EntryPoints.extracted` is the
extracted `pqxdh_initiate` and `pqxdh_accept`. Every definition of the realization is generic in
the entry points, so the fault fixtures can substitute entry points that always panic, always
return an error or never terminate.
-/

open OracleSpec OracleComp
open Aeneas Aeneas.Std
open libsignal_protocol

namespace Protocols.PQXDH

/-- Uniform sampling of a byte, through its 8-bit vector. -/
instance : SampleableType Aeneas.Std.U8 :=
  SampleableType.ofEquiv (α := BitVec 8)
    ⟨fun bv => ⟨bv⟩, fun x => x.bv, fun _ => rfl, fun _ => rfl⟩

/-- A fixed-length Aeneas array is a vector of its elements. -/
def arrayEquivVector (α : Type) (n : Aeneas.Std.Usize) :
    List.Vector α n.val ≃ Aeneas.Std.Array α n where
  toFun v := Aeneas.Std.Array.from v.1 v.2
  invFun a := ⟨a.val, a.property⟩
  left_inv _ := Subtype.ext (Aeneas.Std.Array.from_val _ _)
  right_inv a := Aeneas.Std.Array.val_from a _

/-- Uniform sampling of a fixed-length array, through the vector of its elements. -/
instance {α : Type} {n : Aeneas.Std.Usize} [SampleableType α] :
    SampleableType (Aeneas.Std.Array α n) :=
  SampleableType.ofEquiv (arrayEquivVector α n)

/-- The bytes form a finite type. -/
instance : Fintype Aeneas.Std.U8 :=
  Fintype.ofEquiv (BitVec 8) ⟨fun bv => ⟨bv⟩, fun x => x.bv, fun _ => rfl, fun _ => rfl⟩

/-- Fixed-length arrays over a finite type form a finite type. -/
instance {α : Type} {n : Aeneas.Std.Usize} [Fintype α] : Fintype (Aeneas.Std.Array α n) :=
  Fintype.ofEquiv _ (arrayEquivVector α n)

/-- What the Full realization takes from outside the extracted code. -/
structure Params (Rand Msg C IdC IdK : Type) where
  /-- The caller's generator, as `rand::Rng`. -/
  rngInst : rand.rng.Rng Rand
  /-- The caller's generator, as `rand_core::CryptoRng`. -/
  cryptoRngInst : rand_core_1.CryptoRng Rand
  /-- The law of the caller's generator state at the start of a session, drawn once per session
  (modelling choice). Production's generator is long-lived, and the model does not relate its
  sessions. -/
  coins : ProbComp Rand
  /-- The ideal curve25519 key generator (modelling choice). Every curve25519 key pair comes from
  it, except Alice's ephemeral key in the wrapper (`initiate`), which comes from Core's
  `KeyPair::generate` on her generator state, as in production
  (`rust/protocol/src/session.rs:237`). The core statements and the premise games still draw her
  ephemeral key from it. Its law is related neither to
  production's clamped generation (`rust/core/src/curve/curve25519.rs:27-37`) nor to the abstract
  model's uniform exponent. -/
  ecKeygen : ProbComp ECKeyPair
  /-- The ideal Kyber key generator (modelling choice), in place of production's
  `KeyPair::generate` on the caller's generator. Bob's one-time and last-resort Kyber prekeys come
  from it. -/
  pqKeygen : ProbComp PQKeyPair
  /-- The synthetic AEAD of the UAKE wrapper, with associated data `(IK_A, IK_B, PQPK_B)`.
  Production has no counterpart. -/
  aead : AEAD.Scheme ProbComp Msg Key (ECPub × ECPub × PQPub) C
  /-- Identifiers of curve25519 prekeys. -/
  idEC : ECPub → IdC
  /-- Identifiers of Kyber prekeys. -/
  idKEM : PQPub → IdK

/-- The two entry points of the handshake, with the types of the extracted functions. -/
structure EntryPoints (Rand : Type) where
  /-- The initiator's entry point: from Alice's parameters and her generator state, the agreement
  or a protocol error, and the new generator state. -/
  initiate : rand.rng.Rng Rand → rand_core_1.CryptoRng Rand → pqxdh.InitiatorParameters → Rand →
    Result (core.result.Result InitiatorAgreement error.SignalProtocolError × Rand)
  /-- The responder's entry point: from Bob's parameters, the handshake keys or a protocol
  error. -/
  accept : pqxdh.RecipientParameters →
    Result (core.result.Result HandshakeKeys error.SignalProtocolError)

/-- The extracted entry points `pqxdh_initiate` (`rust/protocol/src/pqxdh.rs:201-247`) and
`pqxdh_accept` (`rust/protocol/src/pqxdh.rs:337-387`). -/
noncomputable def EntryPoints.extracted {Rand : Type} : EntryPoints Rand where
  initiate := pqxdh.pqxdh_initiate
  accept := pqxdh.pqxdh_accept

end Protocols.PQXDH
