/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin, Alessandro D'Angelo
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import Protocols.PQXDH.Realization.Kdf
import Protocols.PQXDH.Realization.Scheme
import Protocols.ToVCVio.CryptoFoundations.AKE.UAKE.Partnering

/-!
# Original-key partnering for the Full realization

Two sessions of PQXDH are partners when they agree on the associated data and on the original key
material `km`, the exact input of the key derivation: 32 bytes of `0xFF`, the Diffie-Hellman
outputs DH1 to DH4 and the Kyber shared secret. Equal inputs give equal keys, since the derivation
is a function, but distinct inputs that give equal keys do not make partners. The identifiers and
the bytes of an unsigned one-time prekey in the initiator's message are not authenticated.

The extracted entry points return the derived keys but not `km`. So each completed state records
the exact inputs of its entry-point call, and `InitiateKdfInput` and `AcceptKdfInput` specify the
`km` of that call. The leaf functions are deterministic, so the inputs of a call determine its
`km`. `initiate_kdfInput_witness` and `accept_kdfInput_witness` state that a successful call
derives its keys from that `km`, and their proofs are stubs. `fullPartnering` is the resulting
partnering relation of `uakeInitiator`. The session identifier `(ad, km)` exists only for
completed states, so it is fixed when a session accepts.
-/

open OracleSpec OracleComp AKE AKE.UAKE
open Aeneas Aeneas.Std
open libsignal_protocol

namespace Protocols.PQXDH.Realization

variable {Rand Msg C IdC IdK : Type}

/-- The original key material of an initiator call. On the inputs `ip` and the generator
state `r`, the agreements of Alice's identity key with Bob's signed prekey, of her ephemeral key
with Bob's identity key and signed prekey, and with his one-time prekey when there is one, return
`d1`, `d2`, `d3` and `d4`; the encapsulation to Bob's Kyber prekey returns the shared secret `ss`;
and `km` is the key-derivation input that these values make (`rust/protocol/src/pqxdh.rs:201-247`).
-/
def InitiateKdfInput (crng : rand_core_1.CryptoRng Rand) (ip : pqxdh.InitiatorParameters)
    (r : Rand) (km : Slice U8) : Prop :=
  ∃ (d1 d2 d3 : Slice U8) (d4 : Option (Slice U8)) (ss ct : Slice U8) (r' : Rand),
    curve.PrivateKey.calculate_agreement ip.our_identity_key_pair.private_key
        ip.their_signed_pre_key = .ok (.Ok d1) ∧
      curve.PrivateKey.calculate_agreement ip.our_ephemeral_key_pair.private_key
        ip.their_identity_key.public_key = .ok (.Ok d2) ∧
      curve.PrivateKey.calculate_agreement ip.our_ephemeral_key_pair.private_key
        ip.their_signed_pre_key = .ok (.Ok d3) ∧
      (match ip.their_one_time_pre_key with
        | none => d4 = none
        | some opk => ∃ d, curve.PrivateKey.calculate_agreement
            ip.our_ephemeral_key_pair.private_key opk = .ok (.Ok d) ∧ d4 = some d) ∧
      kem.KeyPublic.encapsulate crng ip.their_kyber_pre_key r = .ok (.Ok (ss, ct), r') ∧
      kdfInput d1 d2 d3 d4 ss = .ok km

/-- The original key material of a responder call. On the inputs `rp`, the agreements of
Bob's signed prekey with Alice's identity key, of his identity key with her ephemeral key, of his
signed prekey with her ephemeral key, and of his one-time prekey with her ephemeral key when he
uses one, return `d1`, `d2`, `d3` and `d4`; decapsulating Alice's ciphertext returns `ss`; and
`km` is the key-derivation input that these values make (`rust/protocol/src/pqxdh.rs:337-387`). -/
def AcceptKdfInput (rp : pqxdh.RecipientParameters) (km : Slice U8) : Prop :=
  ∃ (d1 d2 d3 : Slice U8) (d4 : Option (Slice U8)) (ss : Slice U8),
    curve.PrivateKey.calculate_agreement rp.our_signed_pre_key_pair.private_key
        rp.their_identity_key.public_key = .ok (.Ok d1) ∧
      curve.PrivateKey.calculate_agreement rp.our_identity_key_pair.private_key
        rp.their_ephemeral_key = .ok (.Ok d2) ∧
      curve.PrivateKey.calculate_agreement rp.our_signed_pre_key_pair.private_key
        rp.their_ephemeral_key = .ok (.Ok d3) ∧
      (match rp.our_one_time_pre_key_pair with
        | none => d4 = none
        | some opk => ∃ d, curve.PrivateKey.calculate_agreement opk.private_key
            rp.their_ephemeral_key = .ok (.Ok d) ∧ d4 = some d) ∧
      kem.KeySecret.decapsulate rp.our_kyber_pre_key_pair.secret_key
        rp.their_kyber_ciphertext = .ok (.Ok ss) ∧
      kdfInput d1 d2 d3 d4 ss = .ok km

/-- If `pqxdh_initiate` succeeds on `ip` and `r`, its keys are derived from the original key
material of that call. The proof is a stub. -/
theorem initiate_kdfInput_witness (crng : rand_core_1.CryptoRng Rand)
    (rng : rand.rng.Rng Rand) (ip : pqxdh.InitiatorParameters) (r r' : Rand)
    (ag : InitiatorAgreement) (h : pqxdh.pqxdh_initiate rng crng ip r = .ok (.Ok ag, r')) :
    ∃ km, InitiateKdfInput crng ip r km ∧ pqxdh.HandshakeKeys.derive km = .ok ag.keys := by
  sorry

/-- If `pqxdh_accept` succeeds on `rp`, its keys are derived from the original key material of
that call. The proof is a stub. -/
theorem accept_kdfInput_witness (rp : pqxdh.RecipientParameters) (hk : HandshakeKeys)
    (h : pqxdh.pqxdh_accept rp = .ok (.Ok hk)) :
    ∃ km, AcceptKdfInput rp km ∧ pqxdh.HandshakeKeys.derive km = .ok hk := by
  sorry

/-- The session identifier of a completed Alice state: its associated data and the original key
material of its entry-point call. States before completion have none. -/
def InitiatorState.Sid (crng : rand_core_1.CryptoRng Rand) :
    InitiatorState Rand Msg → (ECPub × ECPub × PQPub) → Slice U8 → Prop
  | .done s, ad, km => s.ad = ad ∧ InitiateKdfInput crng s.inputs s.coins km
  | _, _, _ => False

/-- The session identifier of a completed Bob state: its associated data and the original key
material of its entry-point call. States before completion have none. -/
def RecipientState.Sid : RecipientState Msg → (ECPub × ECPub × PQPub) → Slice U8 → Prop
  | .done s, ad, km => s.ad = ad ∧ AcceptKdfInput s.inputs km
  | _, _, _ => False

/-- Original-key partnering for `uakeInitiator`: Alice's state and Bob's state are partners
when both are completed with the same associated data and the same original key material. -/
def fullPartnering [DecidableEq Msg] [DecidableEq IdC] [DecidableEq IdK]
    (P : Params Rand Msg C IdC IdK) (E : EntryPoints Rand) (msg : Msg) (hasOPK : Bool) :
    Partnering (uakeInitiator P E msg hasOPK) where
  partner sa sb := ∃ ad km,
    InitiatorState.Sid (Msg := Msg) P.cryptoRngInst sa ad km ∧ RecipientState.Sid sb ad km

end Protocols.PQXDH.Realization
