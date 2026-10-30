/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import Libsignal.Translated.Core.FunsExternal
import Libsignal.Translated.Protocol.Types

/-!
# Byte and key types of the extracted PQXDH code

Names for the extracted `libsignal_protocol` types that the Full realization uses: fixed-length
byte arrays, curve25519 and Kyber keys, 32-byte keys and the extracted handshake keys, with the
projections of the three derived keys.

The file also defines the joint output of the handshake that the Full realization keeps in both
parties' states. `JointKeys` records all of what `pqxdh_initiate` and `pqxdh_accept` derive: the
root key, the chain key with its index, and the post-quantum ratchet key. The UAKE game reads only
the root key. The states keep the rest so that the correctness statements can compare the whole
record.
`AeadRoleKeys` names the two keys that the synthetic AEAD wrapper of the Full realization uses.

Two predicates describe the key pairs that honest key generation must produce. `ECKeyPairValid`
says that a curve25519 key pair's public half is the one derived from its private half. It does
not say that the private bytes are clamped or how they are distributed. `PQKeyPairShape` says that a
Kyber key pair has the Kyber1024 type and the Kyber1024 byte lengths.

**Source**: `PQXDH/Aeneas/Full/UAKE/Defs.lean` of libsignal-docs-and-models, the declarations of
the same names (`ECKeyPairValid` at lines 282-286). `JointKeys`, `AeadRoleKeys` and
`PQKeyPairShape` are new here.
-/

open Aeneas Aeneas.Std
open libsignal_protocol

namespace Protocols.PQXDH.Realization

/-- Fixed-length byte arrays from the Aeneas extraction. -/
abbrev Bytes (n : Aeneas.Std.Usize) : Type := Aeneas.Std.Array Aeneas.Std.U8 n

/-- An extracted curve25519 public key. -/
abbrev ECPub : Type := libsignal_core.curve.PublicKey

/-- A 32-byte derived key. -/
abbrev Key : Type := Bytes 32#usize

/-- The extracted KDF output: root, chain, and post-quantum ratchet keys. -/
abbrev HandshakeKeys : Type := pqxdh.HandshakeKeys

/-- The root-key bytes of the extracted handshake keys. -/
def rootKeyBytes (hk : HandshakeKeys) : Key := hk.root_key.key

/-- The chain-key bytes of the extracted handshake keys. -/
def chainKeyBytes (hk : HandshakeKeys) : Key := hk.chain_key.key

/-- The post-quantum-ratchet-key bytes of the extracted handshake keys. -/
def pqrKeyBytes (hk : HandshakeKeys) : Key := hk.pqr_key

/-- An extracted curve25519 private key. -/
abbrev ECPriv : Type := libsignal_core.curve.PrivateKey

/-- An extracted curve25519 key pair. Nothing in the structure relates its two halves (see
`ECKeyPairValid`). -/
abbrev ECKeyPair : Type := libsignal_core.curve.KeyPair

/-- An extracted identity public key, a wrapped curve25519 public key. -/
abbrev IdKey : Type := identity_key.IdentityKey

/-- An extracted identity key pair. One key pair both signs and performs Diffie-Hellman, as in
production. -/
abbrev IdKeyPair : Type := identity_key.IdentityKeyPair

/-- An extracted Kyber public key. -/
abbrev PQPub : Type := kem.Key kem.Public

/-- An extracted Kyber secret key. -/
abbrev PQPriv : Type := kem.Key kem.Secret

/-- An extracted Kyber key pair. -/
abbrev PQKeyPair : Type := kem.KeyPair

/-- The extracted result of `pqxdh_initiate`: the handshake keys and the serialized KEM
ciphertext. -/
abbrev InitiatorAgreement : Type := pqxdh.InitiatorAgreement

/-- The joint output of the handshake: the root key, the chain key with its index, and the
post-quantum ratchet key, in the order in which `HandshakeKeys::derive_with_label` cuts them from
the 96 bytes of HKDF output (`rust/protocol/src/pqxdh.rs:79-96`). -/
structure JointKeys where
  /-- The root key, bytes 0 to 31 of the derivation. -/
  root : Key
  /-- The chain key, bytes 32 to 63 of the derivation. -/
  chain : Key
  /-- The index of the chain key, which the derivation sets to `0`. -/
  chainIndex : Aeneas.Std.U32
  /-- The post-quantum ratchet key, bytes 64 to 95 of the derivation. -/
  pqr : Key
  deriving DecidableEq

/-- The joint output read off the extracted handshake keys. -/
def JointKeys.ofHandshakeKeys (hk : HandshakeKeys) : JointKeys where
  root := rootKeyBytes hk
  chain := chainKeyBytes hk
  chainIndex := hk.chain_key.index
  pqr := pqrKeyBytes hk

/-- The keys of the synthetic AEAD wrapper: `alice` keys Alice's initial ciphertext and `bob`
keys Bob's confirmation. Production has neither ciphertext: it encrypts Alice's first message
under keys that the Double Ratchet and SPQR derive later. -/
structure AeadRoleKeys where
  /-- The key of Alice's initial ciphertext. -/
  alice : Key
  /-- The key of Bob's confirmation. -/
  bob : Key

/-- The role assignment of the synthetic wrapper, a modelling choice taken from PQXDH-model:
Alice's ciphertext uses the chain key and Bob's confirmation the post-quantum ratchet key.
Production uses neither key for these purposes. On the honest path, the chain key at index `0`
keys no message. -/
def syntheticAeadRoles (j : JointKeys) : AeadRoleKeys where
  alice := j.chain
  bob := j.pqr

/-- A curve25519 key pair is valid when its public half is the one that the extracted
`PrivateKey::public_key` derives from its private half. Production's `KeyPair::generate`
produces valid pairs (`rust/core/src/curve.rs:327-341`), but `KeyPair::new` accepts any two
halves. -/
def ECKeyPairValid (kp : ECKeyPair) : Prop :=
  _root_.curve.PrivateKey.public_key kp.private_key = .ok (.Ok kp.public_key)

/-- A Kyber key pair has the shape of a Kyber1024 key pair: both halves carry the Kyber1024 type,
the public key has 1568 bytes and the secret key 3168 bytes. -/
def PQKeyPairShape (kp : PQKeyPair) : Prop :=
  kp.public_key.key_type = .Kyber1024 ∧ kp.secret_key.key_type = .Kyber1024 ∧
    kp.public_key.key_data.data.length = 1568 ∧ kp.secret_key.key_data.data.length = 3168

end Protocols.PQXDH.Realization
