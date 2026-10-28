/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import Libsignal.Translated.Core.Types
import Libsignal.Translated.Protocol.Types

/-!
# Byte and key types of the extracted PQXDH code

Names for the extracted `libsignal_protocol` types that the KDF mirror in
`Protocols.PQXDH.Realization.Kdf` uses: fixed-length byte arrays, curve25519 public keys, 32-byte
keys and the extracted handshake keys, with the projections of the three derived keys.

**Source**: `PQXDH/Aeneas/Full/UAKE/Defs.lean` of libsignal-docs-and-models, the declarations of
the same names.
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

end Protocols.PQXDH.Realization
