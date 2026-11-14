/-
Copyright (c) 2026 Galois Inc. All rights reserved.
Copyright (c) 2026 Beneficial AI Foundation. All rights reserved.
Released under the Apache License 2.0 as described in the file LICENSES/Apache-2.0.txt.
Authors: Ben Hamlin, Alessandro D'Angelo
Ported with changes from https://github.com/GaloisInc/libsignal-docs-and-models, see
Protocols/ATTRIBUTION.md.
-/
import Protocols.ToVCVio.CryptoFoundations.AEAD
import VCVio.CryptoFoundations.KeyEncapMech
import VCVio.CryptoFoundations.SignatureAlg

open OracleSpec OracleComp

/-!
# PQXDH model

This is a direct Lean model of PQXDH based on the spec at
https://signal.org/docs/specifications/pqxdh/pqxdh.pdf. Like that document, we
use the convention that the initiator is Alice, and the recipient is Bob.

Model simplifications
* **Bob's extra message:** In the PQXDH spec, the exchange ends at Alice's
  first message to Bob, but UAKE requires that the last message be sent by the
  keyed party (Bob). Therefore we add an extra message from Bob under the AEAD
  at the end of the protocol in the T=Bob case. This would represent the second
  message in the conversation between Alice and Bob. We represent this by
  returning `⟨sk, kb, ad, m⟩`, rather than just the shared key `sk`, if Bob's
  `accept` procedure succeeds. Here, `m` and `ad` are the same as the message
  and additional data sent by Alice in her AEAD message, and `kb` is an AEAD
  key (output by the KDF independently from the shared secret and Alice's AEAD
  key). This is then sent to Alice, who uses the `confirm` procedure to check
  that it decrypts under the same `kb` and has the correct content, and returns
  `sk`, if so. The T=Alice scheme `uakeRecipient` follows PQXDH's message flow
  without Bob's extra message. Its role assignment comes from the UAKE definition and
  carries no security claim. Alice's ciphertext models the specification's initial
  ciphertext. Production sends it as the first Double Ratchet message under
  ratchet-derived keys, so it does not correspond to extracted code. Bob's confirmation
  message exists only in the model.
* **Single identity key:** Bob's identity key pair `ikB = (x • gen, x)` signs his
  signed pre-key and every KEM pre-key, and it also takes part in the Diffie-Hellman
  exchange. Production also uses one identity key for XEdDSA signing and X25519
  agreement. So `Parameters.sig` draws its keys with `dhKeygen`. The source gives Bob
  a separate signature key pair, the "no key reuse" simplification of Sec. 4 of the
  spec (see `Protocols/ATTRIBUTION.md`). `dhKeygen` samples a uniform exponent, and
  production clamps its scalars; the relation between the two generators is open
  (`Protocols/LEDGER.md`).
* **Separate AEAD key:** The PQXDH spec uses the same KDF output for both
  Alice's AEAD key and the final result of the key exchange, but this seems to
  preclude key indistinguishability. This is because the adversary can try
  using the candidate key to decrypt Alice's message. This will fail for a
  random key (with high likelihood) but succeed for the real key, thus
  distinguishing them. The spec allows KA to be SK or PRF(SK, ·), but both
  variants break key indistinguishability. This could be easily fixed by using
  the KDF output as the key to a PRF that generates **both** SK and KA, but
  the spec **only describes a PRF-derived KA**, which is insufficient. We
  sidestep this and model the final key and Alice's AEAD (and Bob's AEAD key)
  as separate KDF outputs.
-/

namespace Protocols.Models.PQXDH

variable {F G SS PQPK PQSK CT S C Msg K IdC IdK : Type}

/-- The input type to the abstract SignatureAlg. We need the same signature
   scheme to sign both DH and KEM public keys, so we use a sum of these. -/
abbrev SignatureInput (G PQPK : Type) : Type := G ⊕ PQPK

/-- Encode a DH key as an input to the signature scheme. -/
def EncodeEC {G PQPK : Type} (pk : G) : SignatureInput G PQPK := Sum.inl pk

/-- Encode a KEM key as an input to the signature scheme. -/
def EncodeKEM {G PQPK : Type} (pk : PQPK) : SignatureInput G PQPK := Sum.inr pk

/-- The key material used as input to the KDF. -/
abbrev KeyMaterial (G SS : Type) : Type := G × G × G × Option G × SS

/-- Constants and primitive cryptographic operations used by PQXDH. Rather than
  instantiating the model with concrete cryptographic algorithms
  (the paper gives several alternatives), we use VCVio's existing abstract
  notions of a `KemScheme` and `SignatureAlg`. A relevant AEAD primitive does
  not appear in VCVio, so we use our own formalization (under `Protocols/ToVCVio/`,
  for potential upstreaming). The signing and verification algorithms are fields;
  the signature scheme `Parameters.sig` built from them draws its keys with
  `dhKeygen`, because the identity key both signs and does Diffie-Hellman. -/
structure Parameters (F G SS PQPK PQSK CT S C Msg K IdC IdK : Type) where
  /-- Generator for the Diffie-Hellman group -/
  gen : G
  /-- KEM used for the post-quantum portion of the key exchange -/
  pqkem : KEMScheme ProbComp SS PQPK PQSK CT
  /-- Signing with an identity key pair: public key in `G`, secret exponent in `F`. -/
  sign : G → F → SignatureInput G PQPK → ProbComp S
  /-- Verification of a signature against an identity public key. -/
  verify : G → SignatureInput G PQPK → S → ProbComp Bool
  /-- AEAD used for the initial PQXDH message -/
  aead : AEAD.Scheme ProbComp Msg K (G × G × PQPK) C
  /-- Key derivation function used to generate the session key that results
    from the exchange, as well as the AEAD keys. We model this as an arbitrary
    function that might be instantiated by, e.g., a PRF or a RO. -/
  kdf : KeyMaterial G SS → K × K × K
  /-- Function that maps a DH public key to key identifiers. -/
  idEC : G → IdC
  /-- Function that maps a KEM public key to key identifiers. -/
  idKEM : PQPK → IdK

/-- Generate a DH keypair (pk, sk) = (g^x, x), for a uniformly chosen
  exponent x. -/
def dhKeygen [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    (gen : G) : ProbComp (G × F) := do
  let sk ← $ᵗ F
  return (sk • gen, sk)

/-- Generate a DH shared key g^xy, given a secret key y and a public key g^x. -/
def DH [Field F] [AddCommGroup G] [Module F G] (sk : F) (pk : G) : G := sk • pk

/-- The signature scheme on the Diffie-Hellman identity keys drawn by `dhKeygen`.
  VCVio's completeness and unforgeability notions for `P.sig` use this distribution. -/
@[reducible] def Parameters.sig [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK) :
    SignatureAlg ProbComp (SignatureInput G PQPK) G F S where
  keygen := dhKeygen P.gen
  sign := P.sign
  verify := P.verify

/-- Generate a DH OPK only if hasOPK is true. -/
def genOPK [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    (gen : G) (hasOPK : Bool) : ProbComp (Option (G × F)) :=
  if hasOPK then some <$> dhKeygen gen else pure none

/-- The parameters given to Alice on startup. -/
structure InitiatorParameters (F G Msg : Type) where
  /-- Alice's long-term identity DH keypair. -/
  ikA : G × F
  /-- Bob's identity public key, used for Diffie-Hellman and to verify his signatures,
    pinned to Alice. This models the out-of-band key fingerprinting from Sec. 4.1 of
    the spec. -/
  ikB : G
  /-- The message Alice intends to send to Bob in the initial AEAD ciphertext. -/
  msg : Msg

/-- Bob's long- and medium-term key pairs: the identity key, which also signs, and
  the signed (medium-term) pre-key with its signature. -/
structure RecipientIdentity (F G S : Type) where
  /-- Bob's identity key pair, used for Diffie-Hellman and for signing. -/
  ikB : G × F
  /-- Bob's signed (medium-term) DH pre-key pair. -/
  spkB : G × F
  /-- Bob's signature for his SPK. -/
  spkSigB : S

/-- The parameters given to Bob on startup. -/
structure RecipientParameters (F G PQPK PQSK S : Type) where
  /-- Bob's identity key pair, used for Diffie-Hellman and for signing. -/
  ikB : G × F
  /-- Bob's signed (medium-term) DH pre-key pair. -/
  spkB : G × F
  /-- Bob's signature for his SPK. -/
  spkSigB : S
  /-- Bob's one-time key pair (which may be empty). -/
  opkB : Option (G × F)
  /-- Bob's (short-term) KEM key pair. -/
  pqpkB : PQPK × PQSK

/-- The bundle of Bob's public key material fetched by Alice at the start of
  the protocol. -/
structure PreKeyBundle (G PQPK S IdC IdK : Type) where
  /-- Bob's identity public key. -/
  ikB : G
  /-- Public half of Bob's signed DH pre-key, along with its identifier. -/
  spkB : G × IdC
  /-- Bob's signature for his SPK. -/
  spkSigB : S
  /-- Bob's post-quantum KEM public pre-key, along with its identifier. -/
  pqpkB : PQPK × IdK
  /-- Bob's signature for his PQ pre-key. -/
  pqpkSigB : S
  /-- Public half of Bob's one-time DH pre-key, along with its identifier (which
    may be absent). -/
  opkB : Option (G × IdC)
  deriving DecidableEq

/-- Initial message from Alice to Bob. -/
structure InitialMessage (G CT C IdC IdK : Type) where
  /-- Alice's identity DH public key. -/
  ikA : G
  /-- Alice's ephemeral DH public key. -/
  ekA : G
  /-- Alice's KEM ciphertext. -/
  ct : CT
  /-- Key identifier for Bob's signed DH pre-key. -/
  idSPK : IdC
  /-- Key identifier for Bob's PQ pre-key. -/
  idPQPK : IdK
  /-- Key identifier for Bob's (optional) one-time DH pre-key. -/
  idOPK : Option IdC
  /-- AEAD ciphertext of Alice's initial message, encrypted using the derived
    shared key. -/
  ctxt : C
  deriving DecidableEq

/-- Session context of an accepted exchange. Alice stores it after `initiate` and keeps it after
  `confirm`; Bob stores the context that `accept` returns. (See bullet 1 of "Model
  simplifications".) -/
structure SessionContext (G PQPK Msg K SS : Type) where
  /-- Shared key output by the KDF. -/
  sk : K
  /-- Bob's AEAD key, output by the KDF independently of `sk`.
    * DEVIATION FROM SPEC: In the PQXDH spec, Bob does not send an AEAD
      message, only Alice does. This extra AEAD ciphertext from Bob (which
      might represent the second message in the exchange, in the same way that
      Alice's AEAD ciphertext represents the first) is required in order to
      realize the T=Bob UAKE direction without being trivially insecure. See
      bullet 1 of "Model simplifications". -/
  kb : K
  /-- Additional data used in the AEAD ciphertexts. -/
  ad : G × G × PQPK
  /-- Message encrypted in the AEAD ciphertexts. -/
  msg : Msg
  /-- The key material `(DH1, DH2, DH3, DH4, SS)` that the session passed to `P.kdf`. The model
    keeps it so that the security experiment can compare the original key material of two
    sessions (`originalKeyPartnering`). Production keeps no such value. -/
  km : KeyMaterial G SS

/-- Create the long-term state used by Alice and Bob respectively for all
  sessions. Bob signs his signed pre-key with his identity key. -/
def setup [Field F] [AddCommGroup G] [Module F G] [SampleableType F]
    (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK) (msg : Msg) :
    ProbComp (InitiatorParameters F G Msg × RecipientIdentity F G S) := do
  let ikA ← dhKeygen P.gen
  let ikB ← dhKeygen P.gen
  let spkB ← dhKeygen P.gen
  let spkSigB ← P.sig.sign ikB.1 ikB.2 (EncodeEC spkB.1)
  return ({ ikA := ikA, ikB := ikB.1, msg := msg },
    { ikB := ikB, spkB := spkB, spkSigB := spkSigB })

/-- Compute Bob's key bundle to send to Alice.
  * DEVIATION FROM SPEC: In the spec, this is retrieved by Alice from a
    third-party server, however in UAKE, we have only two parties. Therefore,
    we make this a message from Bob. -/
def publish (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK)
    (p : RecipientParameters F G PQPK PQSK S) :
    ProbComp (PreKeyBundle G PQPK S IdC IdK) := do
  let pqpkSigB ← P.sign p.ikB.1 p.ikB.2 (EncodeKEM p.pqpkB.1)
  return { ikB := p.ikB.1
           spkB := (p.spkB.1, P.idEC p.spkB.1)
           spkSigB := p.spkSigB
           pqpkB := (p.pqpkB.1, P.idKEM p.pqpkB.1)
           pqpkSigB := pqpkSigB
           opkB := p.opkB.map fun opk => (opk.1, P.idEC opk.1) }

/-- Compute Alice's initial message to Bob, including her public keys, and the
  initial AEAD ciphertext.
  * DEVIATION FROM SPEC: It seems necessary to assume that the keys used for
    the AEAD encrypted ciphertexts are independent of SK and of each other.
    Here, we make them distinct outputs of the KDF. Using SK to key the AEAD
    and revealing the message appears to be incompatible with key
    indistinguishability, since an attacker can distinguish the key from random
    by using the candidate key to decrypt the initial message and checking
    whether it succeeds. -/
def initiate [Field F] [AddCommGroup G] [Module F G] [SampleableType F] [DecidableEq G]
    (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK)
    (p : InitiatorParameters F G Msg)
    (bundle : PreKeyBundle G PQPK S IdC IdK) :
    ProbComp (Option (InitialMessage G CT C IdC IdK × SessionContext G PQPK Msg K SS)) := do
  if bundle.ikB ≠ p.ikB then return none
  let okSPK ← P.sig.verify p.ikB (EncodeEC bundle.spkB.1) bundle.spkSigB
  let okPQPK ← P.sig.verify p.ikB (EncodeKEM bundle.pqpkB.1) bundle.pqpkSigB
  if !(okSPK && okPQPK) then return none
  let ekA : G × F ← dhKeygen P.gen
  let (CT, SS) ← P.pqkem.encaps bundle.pqpkB.1
  let DH1 := DH p.ikA.2 bundle.spkB.1
  let DH2 := DH ekA.2 bundle.ikB
  let DH3 := DH ekA.2 bundle.spkB.1
  let DH4 := bundle.opkB.map fun opk => DH ekA.2 opk.1
  let (SK, KA, KB) := P.kdf (DH1, DH2, DH3, DH4, SS)
  let AD := (p.ikA.1, bundle.ikB, bundle.pqpkB.1)
  let ctxt ← P.aead.encrypt KA AD p.msg
  return some ({ ikA := p.ikA.1
                 ekA := ekA.1
                 ct := CT
                 idSPK := bundle.spkB.2
                 idPQPK := bundle.pqpkB.2
                 idOPK := bundle.opkB.map Prod.snd
                 ctxt := ctxt },
    { sk := SK, kb := KB, ad := AD, msg := p.msg, km := (DH1, DH2, DH3, DH4, SS) })

/-- Bob's confirmation procedure. Check if Alice's AEAD ciphertext decrypts with
  the correct AD and KDF-derived key. Return sk, if so. Also return the key,
  message, and AD for Bob's own AEAD ciphertext, and the key material.
  * DEVIATION FROM SPEC: Bob's AEAD ciphertext is not present in the spec, but
    it's needed in order to fit the UAKE security definition in the T=Bob case.
    See bullet 1 of "Model simplifications". -/
def accept [Field F] [AddCommGroup G] [Module F G] [DecidableEq IdC] [DecidableEq IdK]
    (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK)
    (p : RecipientParameters F G PQPK PQSK S)
    (msg : InitialMessage G CT C IdC IdK) :
    ProbComp (Option (SessionContext G PQPK Msg K SS)) := do
  if msg.idSPK ≠ P.idEC p.spkB.1 ∨ msg.idPQPK ≠ P.idKEM p.pqpkB.1 ∨
      msg.idOPK ≠ p.opkB.map (fun opk => P.idEC opk.1) then return none
  let some SS ← P.pqkem.decaps p.pqpkB.2 msg.ct | return none
  let DH1 := DH p.spkB.2 msg.ikA
  let DH2 := DH p.ikB.2 msg.ekA
  let DH3 := DH p.spkB.2 msg.ekA
  let DH4 := p.opkB.map fun opk => DH opk.2 msg.ekA
  let (SK, KA, KB) := P.kdf (DH1, DH2, DH3, DH4, SS)
  let AD := (msg.ikA, p.ikB.1, p.pqpkB.1)
  match P.aead.decrypt KA AD msg.ctxt with
  | some m =>
      return some { sk := SK, kb := KB, ad := AD, msg := m, km := (DH1, DH2, DH3, DH4, SS) }
  | none => return none

/-- Alice's confirmation procedure: Check if Bob's AEAD ciphertext decrypts
  with the correct message, AD, and KDF-derived key. Return the shared key, if
  so. -/
def confirm [DecidableEq Msg]
    (P : Parameters F G SS PQPK PQSK CT S C Msg K IdC IdK)
    (ctx : SessionContext G PQPK Msg K SS) (conf : C) : Option K :=
  if P.aead.decrypt ctx.kb ctx.ad conf = some ctx.msg then some ctx.sk
  else none

end Protocols.Models.PQXDH
