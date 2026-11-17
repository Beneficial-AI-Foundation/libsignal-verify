import Verso
import VersoManual
import VersoBlueprint
import LibsignalVerifyBlueprint.Code
import Protocols.Models.PQXDH.Basic
import Protocols.Models.PQXDH.UAKE.Defs
import Protocols.Models.PQXDH.UAKE.CorrectnessLemmas
import Protocols.Models.PQXDH.UAKE.Correctness
import Protocols.Models.PQXDH.UAKE.WellFormed
import Protocols.Models.PQXDH.UAKE.Security
import Protocols.Models.PQXDH.UAKE.SecurityLemmas.Games
import Protocols.Models.PQXDH.UAKE.SecurityLemmas.SharedHops
import Protocols.Models.PQXDH.UAKE.SecurityLemmas.DHHops
import Protocols.Models.PQXDH.UAKE.SecurityLemmas.PQHops
import Protocols.Models.PQXDH.UAKE.SecurityLemmas.SigReduction
import VCVio.CryptoFoundations.SignatureAlg

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "PQXDH" =>
%%%
tag := "pqxdh"
%%%

The previous chapter defined unilaterally authenticated key exchange (UAKE) and the
cryptographic notions that its security proofs use. This chapter models PQXDH as a UAKE. It
states the correctness of the model and two theorems that bound the advantage of an
adversary against it, one for classical adversaries and one for the post-quantum case, in
terms of the advantage against the primitives of PQXDH.

The model of this chapter is Galois's: the parameters, the five procedures, the two UAKE
schemes, the correctness and well-formedness theorems, the two security theorems and the
hops below them come from Galois's
[libsignal-docs-and-models](https://github.com/GaloisInc/libsignal-docs-and-models)
(Galois Inc., author Ben Hamlin), at commit `e82e566`. Galois documents its model at
[galoisinc.github.io/libsignal-docs-and-models](https://galoisinc.github.io/libsignal-docs-and-models/).
This repository changes the model in several places, which the text names where they arise.
Bob has one identity key, which signs and takes part in Diffie-Hellman. The signature
hypothesis of the security theorems is joint unforgeability. Hops 3 and 4 of the security
proof are proved here, with the reduction and the key-guessing lemmas that this repository
adds.

The chapter uses the sources of the previous chapter, DF and FG, and one more.

* E. Kret and R. Schmidt, [The PQXDH Key Agreement Protocol](https://signal.org/docs/specifications/pqxdh/),
  Signal, revision 3 (24 May 2023, updated 24 January 2024). We cite it as KS, with its
  printed page numbers.

The proofs are incomplete. Hops 1 to 4 of both security theorems are proved. Hops 5 and 6,
for the Diffie-Hellman theorem and for the post-quantum theorem, are four lemmas that the
Lean development admits with `sorry`. VersoBlueprint therefore marks both security theorems
as depending on `sorry`, and each of the four lemmas as containing `sorry`. All other
results of this chapter are proved. As in the previous chapter, the hypotheses of the
security theorems bound the advantage of every adversary, with no limit on its resources, so
the bounds that the theorems state are trivial for every instantiation
([issue #41](https://github.com/Beneficial-AI-Foundation/libsignal-verify/issues/41)).

The chapter follows the flow of the protocol. First come the types and the five procedures
of PQXDH. Then the two UAKE schemes, and the correctness and well-formedness theorems for
them. Then the statements of the two security theorems, the games and events of their
proofs, and the six hops. The last section lists the choices that make the model differ from
the protocol.

Throughout this chapter, the vector space $`G` over the field $`F` is written additively,
and the Diffie-Hellman value of a secret exponent $`y \in F` and a public key $`X \in G` is
$`y \cdot X`. Where a box compares two elements of a type for equality, we assume that the
type has a decidable equality. Classical logic gives this for every type, and Lean asks for
it as a typeclass argument.

# The PQXDH model

PQXDH lets Alice send a first message to Bob, who may be offline, and gives them a shared
key. In the protocol, Bob has published keys on a server. Alice fetches a bundle of them,
checks Bob's signatures on the prekeys, and sends Bob her keys, a KEM ciphertext, the
identifiers of the prekeys she used, and a first ciphertext under a key that she derives
from several Diffie-Hellman values and the KEM secret (KS, Section 3.1, p. 8; Sections 3.2
to 3.4, pp. 8 to 10). The model has no server: Bob sends the bundle himself, as a first
message, because a UAKE has two parties.

## Types and parameters

Bob signs two kinds of objects with his identity key: Diffie-Hellman public keys and KEM
public keys. The model gives them one type.

::::definition "pqxdh_signature_input" (lean := "Protocols.Models.PQXDH.SignatureInput")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.SignatureInput -docstrings -comments
Let $`G` and $`\mathrm{PQPK}` be types. We define the type of _signature inputs_ to be the
disjoint union $`G + \mathrm{PQPK}`.
:::
::::

KS signs the byte string that a function $`\mathrm{EncodeEC}` or $`\mathrm{EncodeKEM}`
returns for the key, and it requires that the ranges of all its encoding functions are
pairwise disjoint (KS, Section 2.1, p. 3, and Section 3.2, p. 8). The disjoint union takes
the place of the byte strings and of the encodings. We write $`\mathrm{Enc}_{\mathrm{EC}}(X)`
for the image of $`X \in G`, and $`\mathrm{Enc}_{\mathrm{KEM}}(Y)` for the image of
$`Y \in \mathrm{PQPK}`, in $`G + \mathrm{PQPK}`. In Lean, these are the two injections
`EncodeEC` and `EncodeKEM`.

The key derivation takes the Diffie-Hellman values and the KEM secret of a run.

::::definition "pqxdh_key_material" (lean := "Protocols.Models.PQXDH.KeyMaterial")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.KeyMaterial -docstrings -comments
Let $`G` and $`\mathrm{SS}` be types. We define the type of _key material_ to be
$$`\mathrm{KM}(G, \mathrm{SS}) := G \times G \times G \times (G + \{\ast\}) \times \mathrm{SS}.`
We write its elements as $`(\mathrm{DH}_1, \mathrm{DH}_2, \mathrm{DH}_3, \mathrm{DH}_4, \mathrm{ss})`.
The fourth component is $`\ast` if no one-time prekey is used.
:::
::::

In Lean, $`\ast` is `none`, and the type is `G × G × G × Option G × SS`. KS derives the key
from the byte string $`\mathrm{DH}_1 \,\|\, \mathrm{DH}_2 \,\|\, \mathrm{DH}_3 \,\|\, \mathrm{SS}`
and, when the bundle has a one-time prekey, from
$`\mathrm{DH}_1 \,\|\, \mathrm{DH}_2 \,\|\, \mathrm{DH}_3 \,\|\, \mathrm{DH}_4 \,\|\, \mathrm{SS}`
(KS, Section 3.3, p. 9). The model keeps the components apart, and the key derivation
reads them as a tuple.

Alice and Bob use the following parameters. The model leaves the KEM, the signature, the
AEAD and the key derivation abstract.

::::definition "pqxdh_parameters" (lean := "Protocols.Models.PQXDH.Parameters") (uses := "pqxdh_signature_input, pqxdh_key_material, kem_scheme, aead_scheme")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.Parameters -docstrings -comments
Let $`F`, $`G`, $`\mathrm{SS}`, $`\mathrm{PQPK}`, $`\mathrm{PQSK}`, $`\mathrm{CT}`, $`S`,
$`C`, $`\mathrm{Msg}`, $`K`, $`\mathrm{Id}_{\mathrm{EC}}` and $`\mathrm{Id}_{\mathrm{KEM}}`
be types. A set of _PQXDH parameters_ over these types consists of

* a generator $`g \in G`;
* a KEM $`\Lambda = (\mathrm{KeyGen}_\Lambda, \mathrm{Encaps}, \mathrm{Decaps})` over
  probabilistic computations, with key space $`\mathrm{SS}`, public keys in
  $`\mathrm{PQPK}`, secret keys in $`\mathrm{PQSK}` and ciphertexts in $`\mathrm{CT}`;
* a signing algorithm $`\mathrm{Sign}`, which gives for $`X \in G`, $`x \in F` and
  $`\mu \in G + \mathrm{PQPK}` a probabilistic computation $`\mathrm{Sign}(X, x, \mu)` with
  output in $`S`;
* a verification algorithm $`\mathrm{Verify}`, which gives for $`X \in G`,
  $`\mu \in G + \mathrm{PQPK}` and $`\sigma \in S` a probabilistic computation
  $`\mathrm{Verify}(X, \mu, \sigma)` with output in $`\{0, 1\}`;
* an AEAD scheme $`(E, D)` over probabilistic computations, with keys in $`K`, messages in
  $`\mathrm{Msg}`, associated data in $`G \times G \times \mathrm{PQPK}` and ciphertexts in
  $`C`;
* a key derivation function
  $`\mathrm{KDF} : \mathrm{KM}(G, \mathrm{SS}) \to K \times K \times K`;
* an identifier map $`\mathrm{id}_{\mathrm{EC}} : G \to \mathrm{Id}_{\mathrm{EC}}` for
  Diffie-Hellman public keys, and an identifier map
  $`\mathrm{id}_{\mathrm{KEM}} : \mathrm{PQPK} \to \mathrm{Id}_{\mathrm{KEM}}` for KEM
  public keys.
:::
::::

An application of PQXDH fixes a curve, a hash function, an application string, a KEM, an AEAD
scheme and encodings of keys (KS, Section 2.1, p. 3). The model abstracts them. The
signature of KS is XEdDSA, and its signing function uses 64 bytes of fresh randomness (KS,
Section 2.2, p. 4). In the model, signing and verification are probabilistic computations. In
Lean, the field `pqkem` is a `KEMScheme ProbComp`, the field `aead` is an `AEAD.Scheme ProbComp`,
and the fields `gen`, `sign`, `verify`, `kdf`, `idEC` and `idKEM` hold the rest. The
parameters put no algebraic structure on $`F` and $`G`. Each procedure assumes the structure
that it uses.

The model differs from KS in three places that the parameters show.

* The key derivation returns three keys, $`(\mathrm{sk}, k_A, k_B)`. KS derives one key,
  $`\mathrm{KDF}(\mathrm{KM})`, of 32 bytes (KS, Section 2.2, p. 4), and it keys the AEAD with
  that key or with the output of a PRF keyed by it (KS, Section 3.3, p. 10). The model uses
  $`k_A` to encrypt Alice's first message, and $`k_B` for the confirmation message that Bob
  adds. The section on modelling choices below gives the reasons.
* The associated data of the model always contains the KEM public key. KS puts the encoded
  identity keys of Alice and Bob in the associated data, and adds the KEM public key only if
  the KEM does not already bind it into the ciphertext (KS, Section 3.3, p. 10, and
  Section 4.12, pp. 16 and 17).
* The identifiers are elements of abstract types. In KS, an identifier names a key on Bob's
  device (KS, Section 2.4, p. 6). KS calls identifiers "not security critical" (Section 4.13,
  p. 17).

Diffie-Hellman agreement in the model is scalar multiplication, and every key pair comes
from one key generation.

::::definition "pqxdh_dh" (lean := "Protocols.Models.PQXDH.DH")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.DH -docstrings -comments
Let $`F` be a field and let $`G` be a vector space over $`F`. For $`y \in F` and
$`X \in G` we define $`\mathrm{DH}(y, X) := y \cdot X`.
:::
::::

KS writes $`\mathrm{DH}(\mathrm{PK}_1, \mathrm{PK}_2)` for the output of the X25519 or X448
function on the key pairs of the two keys (KS, Section 2.2, p. 4). The model takes the
secret exponent and the public key as separate arguments, and returns an element of $`G`,
not a byte string.

::::definition "pqxdh_dh_keygen" (lean := "Protocols.Models.PQXDH.dhKeygen") (uses := "prob_comp")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.dhKeygen -docstrings -comments
Let $`F` be a finite field, let $`G` be a vector space over $`F`, and let $`g \in G`. We
define $`\mathrm{KeyGen}_g` to be the probabilistic computation that draws $`x` uniformly
from $`F` and outputs $`(x \cdot g, x) \in G \times F`. We call $`x \cdot g` the _public
key_ and $`x` the _secret exponent_.
:::
::::

The class `SampleableType F` of Lean replaces "finite and nonempty" and gives the uniform
draw. Production X25519 clamps its scalars. The model draws a uniform exponent, and the
relation between the two is open
([issue #75](https://github.com/Beneficial-AI-Foundation/libsignal-verify/issues/75)).

The identity key of Bob signs and takes part in Diffie-Hellman. The signature scheme of the
model draws its keys with $`\mathrm{KeyGen}_g`.

::::definition "pqxdh_sig" (lean := "Protocols.Models.PQXDH.Parameters.sig") (uses := "pqxdh_parameters, pqxdh_dh_keygen, pqxdh_signature_input, sig_scheme")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.Parameters.sig -docstrings -comments
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field
and whose type $`G` is a vector space over $`F`. The _identity signature scheme_ of $`P` is
the signature scheme $`\Sigma_P = (\mathrm{KeyGen}_g, \mathrm{Sign}, \mathrm{Verify})` over
probabilistic computations, with messages in $`G + \mathrm{PQPK}`, public keys in $`G`,
secret keys in $`F` and signatures in $`S`, whose signing and verification algorithms are
those of $`P`.
:::
::::

The identity key pair of Bob, $`(X, x)` with $`X = x \cdot g`, signs his prekeys and also
computes $`\mathrm{DH}(x, \cdot)` in the key derivation. Earlier analyses avoid modelling this
reuse of $`\mathrm{IK}_B` for key agreement and signing (KS, Section 4, p. 11), and KS
says that a full proof under a joint assumption on X25519 and XEdDSA "is still needed" (KS,
Section 4, p. 11). The signature hypothesis of the security theorems below is the joint
unforgeability of the previous chapter, for $`\Sigma_P` and the agreement
$`\mathrm{DH}`.

::::definition "pqxdh_gen_opk" (lean := "Protocols.Models.PQXDH.genOPK") (uses := "pqxdh_dh_keygen")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.genOPK -docstrings -comments
Let $`F` be a finite field, let $`G` be a vector space over $`F`, let $`g \in G`, and let
$`h \in \{0, 1\}`. We define $`\mathrm{GenOPK}_g(h)` to be the probabilistic computation
with output in $`(G \times F) + \{\ast\}` that runs $`\mathrm{KeyGen}_g` and outputs its
result if $`h = 1`, and outputs $`\ast` if $`h = 0`.
:::
::::

The flag $`h` says whether Bob uses a one-time prekey. In KS, the server hands out one of
Bob's one-time curve prekeys if one exists, and the bundle has none if all are used (KS,
Section 3.3, p. 9). In the model, Bob draws a fresh one-time key pair in each session, or
draws none.

## Keys and messages

Each party holds the following data. Where the data of one party appears in the data of the
other, we name the components, so that the procedures below can refer to them.

::::definition "pqxdh_initiator_parameters" (lean := "Protocols.Models.PQXDH.InitiatorParameters")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.InitiatorParameters -docstrings -comments
Let $`F`, $`G` and $`\mathrm{Msg}` be types. We define the _initiator parameters_ to be the
triples
$$`((\mathrm{IK}_A, \mathrm{ik}_A), \mathrm{IK}_B, \mu) \in (G \times F) \times G \times \mathrm{Msg},`
where $`(\mathrm{IK}_A, \mathrm{ik}_A)` is the identity key pair of Alice, $`\mathrm{IK}_B` is
the identity public key of Bob, which Alice has pinned, and $`\mu` is the message that Alice
sends to Bob.
:::
::::

The pinned key models the comparison of identity keys through an authenticated channel that
KS mentions, for example by fingerprints or by scanning a QR code (KS, Section 4.1, p. 11).
KS leaves this out of the protocol.

::::definition "pqxdh_recipient_identity" (lean := "Protocols.Models.PQXDH.RecipientIdentity")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.RecipientIdentity -docstrings -comments
Let $`F`, $`G` and $`S` be types. We define the _long-term state of Bob_ to be the triples
$$`((\mathrm{IK}_B, \mathrm{ik}_B), (\mathrm{SPK}_B, \mathrm{spk}_B), \sigma_{\mathrm{SPK}}) \in (G \times F) \times (G \times F) \times S,`
where $`(\mathrm{IK}_B, \mathrm{ik}_B)` is the identity key pair of Bob,
$`(\mathrm{SPK}_B, \mathrm{spk}_B)` is his signed prekey pair, and $`\sigma_{\mathrm{SPK}}` is
the signature on the signed prekey.
:::
::::

::::definition "pqxdh_recipient_parameters" (lean := "Protocols.Models.PQXDH.RecipientParameters")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.RecipientParameters -docstrings -comments
Let $`F`, $`G`, $`\mathrm{PQPK}`, $`\mathrm{PQSK}` and $`S` be types. We define the _session
parameters of Bob_ to be the tuples
$$`((\mathrm{IK}_B, \mathrm{ik}_B), (\mathrm{SPK}_B, \mathrm{spk}_B), \sigma_{\mathrm{SPK}}, o, (\mathrm{PQPK}_B, \mathrm{pqsk}_B)),`
in $`(G \times F) \times (G \times F) \times S \times ((G \times F) + \{\ast\}) \times (\mathrm{PQPK} \times \mathrm{PQSK})`.
The first three components are the long-term state of Bob. The component $`o` is his
one-time prekey pair, if he has one, and $`(\mathrm{PQPK}_B, \mathrm{pqsk}_B)` is his KEM key
pair.
:::
::::

The model gives Bob a fresh one-time key pair and a fresh KEM key pair in every session. KS
has a one-time KEM prekey and, when none is left, a last-resort KEM prekey that Bob changes
periodically (KS, Section 2.5, p. 6, and Section 3.3, p. 9). The model has only the
one-time KEM key.

::::definition "pqxdh_prekey_bundle" (lean := "Protocols.Models.PQXDH.PreKeyBundle")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.PreKeyBundle -docstrings -comments
Let $`G`, $`\mathrm{PQPK}`, $`S`, $`\mathrm{Id}_{\mathrm{EC}}` and
$`\mathrm{Id}_{\mathrm{KEM}}` be types. A _prekey bundle_ is a tuple
$$`(\mathrm{IK}, (\mathrm{SPK}, i_{\mathrm{SPK}}), \sigma_{\mathrm{SPK}}, (\mathrm{PQPK}, i_{\mathrm{PQPK}}), \sigma_{\mathrm{PQPK}}, o)`
in $`G \times (G \times \mathrm{Id}_{\mathrm{EC}}) \times S \times (\mathrm{PQPK} \times \mathrm{Id}_{\mathrm{KEM}}) \times S \times ((G \times \mathrm{Id}_{\mathrm{EC}}) + \{\ast\})`.
It has an identity public key, a signed prekey with its identifier and its signature, a KEM
public key with its identifier and its signature, and an optional one-time prekey with its
identifier.
:::
::::

This is the bundle that KS lists in Section 3.3 (p. 9), with Bob's last-resort KEM prekey
removed. In the model, the identifiers and the one-time prekey are not signed, and the
signatures are on the keys only.
[Issue #35](https://github.com/Beneficial-AI-Foundation/libsignal-verify/issues/35) reports
that this breaks transcript matching, and the section on the security theorems returns to
it.

::::definition "pqxdh_initial_message" (lean := "Protocols.Models.PQXDH.InitialMessage")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.InitialMessage -docstrings -comments
Let $`G`, $`\mathrm{CT}`, $`C`, $`\mathrm{Id}_{\mathrm{EC}}` and $`\mathrm{Id}_{\mathrm{KEM}}`
be types. An _initial message_ is a tuple
$$`(\mathrm{IK}_A, \mathrm{EK}_A, \mathrm{ct}, i_{\mathrm{SPK}}, i_{\mathrm{PQPK}}, i_{\mathrm{OPK}}, c)`
in $`G \times G \times \mathrm{CT} \times \mathrm{Id}_{\mathrm{EC}} \times \mathrm{Id}_{\mathrm{KEM}} \times (\mathrm{Id}_{\mathrm{EC}} + \{\ast\}) \times C`.
It has the identity public key and the ephemeral public key of Alice, a KEM ciphertext, the
identifiers of the signed prekey, of the KEM prekey and of the one-time prekey, which may be
absent, and an AEAD ciphertext.
:::
::::

KS lists the same items for the initial message (KS, Section 3.3, p. 10).

::::definition "pqxdh_session_context" (lean := "Protocols.Models.PQXDH.SessionContext")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.SessionContext -docstrings -comments
Let $`G`, $`\mathrm{PQPK}`, $`\mathrm{Msg}` and $`K` be types. A _session context_ is a
tuple
$$`(\mathrm{sk}, k_B, \mathrm{AD}, \mu) \in K \times K \times (G \times G \times \mathrm{PQPK}) \times \mathrm{Msg},`
with a session key $`\mathrm{sk}`, an AEAD key $`k_B`, associated data $`\mathrm{AD}` and a
message $`\mu`.
:::
::::

Alice stores a session context when she sends her initial message, and Bob stores one when
he accepts it. The key $`k_B` and the message serve the confirmation message that Bob sends
in the model and not in the protocol.

## The procedures

The procedures of PQXDH are five computations. Bob creates his long-term keys in setup, and
his session keys and his bundle in publish. Alice builds her message in initiate, and Bob
processes it in accept. Alice processes Bob's confirmation in confirm.

::::definition "pqxdh_setup" (lean := "Protocols.Models.PQXDH.setup") (uses := "pqxdh_parameters, pqxdh_sig, pqxdh_dh_keygen, pqxdh_initiator_parameters, pqxdh_recipient_identity, pqxdh_signature_input")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.setup -docstrings -comments
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field
and whose type $`G` is a vector space over $`F`, and let $`\mu \in \mathrm{Msg}`. We define
$`\mathrm{Setup}_P(\mu)` to be the probabilistic computation with output in the initiator
parameters and the long-term states of Bob, given by the following steps.

1. Draw $`(\mathrm{IK}_A, \mathrm{ik}_A)`, $`(\mathrm{IK}_B, \mathrm{ik}_B)` and
   $`(\mathrm{SPK}_B, \mathrm{spk}_B)` from $`\mathrm{KeyGen}_g`, in this order.
2. Draw $`\sigma_{\mathrm{SPK}}` from
   $`\mathrm{Sign}(\mathrm{IK}_B, \mathrm{ik}_B, \mathrm{Enc}_{\mathrm{EC}}(\mathrm{SPK}_B))`.
3. Output the initiator parameters $`((\mathrm{IK}_A, \mathrm{ik}_A), \mathrm{IK}_B, \mu)` and
   the long-term state
   $`((\mathrm{IK}_B, \mathrm{ik}_B), (\mathrm{SPK}_B, \mathrm{spk}_B), \sigma_{\mathrm{SPK}})`
   of Bob.
:::
::::

Setup also creates the identity key of Alice, and it gives her the public key of Bob, which
she has pinned. In KS, Bob signs his signed prekey with his identity key, and he replaces
the signed prekey periodically (KS, Section 2.4, p. 6, and Section 3.2, p. 8). A UAKE has
long-term keys and per-session keys only, so in the model the signed prekey and its
signature are created once, here, and they do not change.

::::definition "pqxdh_publish" (lean := "Protocols.Models.PQXDH.publish") (uses := "pqxdh_parameters, pqxdh_recipient_parameters, pqxdh_prekey_bundle, pqxdh_signature_input")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.publish -docstrings -comments
Let $`P` be a set of PQXDH parameters, and let
$$`p = ((\mathrm{IK}_B, \mathrm{ik}_B), (\mathrm{SPK}_B, \mathrm{spk}_B), \sigma_{\mathrm{SPK}}, o, (\mathrm{PQPK}_B, \mathrm{pqsk}_B))`
be session parameters of Bob. We define $`\mathrm{Publish}_P(p)` to be the probabilistic
computation with output in the prekey bundles that draws $`\sigma_{\mathrm{PQPK}}` from
$`\mathrm{Sign}(\mathrm{IK}_B, \mathrm{ik}_B, \mathrm{Enc}_{\mathrm{KEM}}(\mathrm{PQPK}_B))` and
outputs the bundle
$$`(\mathrm{IK}_B, (\mathrm{SPK}_B, \mathrm{id}_{\mathrm{EC}}(\mathrm{SPK}_B)), \sigma_{\mathrm{SPK}}, (\mathrm{PQPK}_B, \mathrm{id}_{\mathrm{KEM}}(\mathrm{PQPK}_B)), \sigma_{\mathrm{PQPK}}, o'),`
where $`o' = (\mathrm{OPK}, \mathrm{id}_{\mathrm{EC}}(\mathrm{OPK}))` if
$`o = (\mathrm{OPK}, \mathrm{opk})`, and $`o' = \ast` if $`o = \ast`.
:::
::::

In KS, Bob uploads the bundle to a server, and Alice fetches it (KS, Section 3.2, p. 8, and
Section 3.3, p. 9). In the model Bob sends it to Alice as his first message. The signature on
the KEM key is made here, in each session, as the key is created in each session.

::::definition "pqxdh_initiate" (lean := "Protocols.Models.PQXDH.initiate") (uses := "pqxdh_parameters, pqxdh_sig, pqxdh_dh, pqxdh_dh_keygen, pqxdh_initiator_parameters, pqxdh_prekey_bundle, pqxdh_initial_message, pqxdh_session_context, pqxdh_signature_input")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.initiate -docstrings -comments
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field
and whose type $`G` is a vector space over $`F`. Let
$`p = ((\mathrm{IK}_A, \mathrm{ik}_A), \mathrm{IK}_B, \mu)` be initiator parameters, and let
$$`\beta = (\mathrm{IK}, (\mathrm{SPK}, i_{\mathrm{SPK}}), \sigma_{\mathrm{SPK}}, (\mathrm{PQPK}, i_{\mathrm{PQPK}}), \sigma_{\mathrm{PQPK}}, o)`
be a prekey bundle. We define $`\mathrm{Initiate}_P(p, \beta)` to be the probabilistic
computation with output in the initial messages paired with the session contexts, or
$`\bot`, given by the following steps.

1. If $`\mathrm{IK} \neq \mathrm{IK}_B`, output $`\bot`.
2. Run $`\mathrm{Verify}(\mathrm{IK}_B, \mathrm{Enc}_{\mathrm{EC}}(\mathrm{SPK}), \sigma_{\mathrm{SPK}})`
   to get $`v_1`, and then
   $`\mathrm{Verify}(\mathrm{IK}_B, \mathrm{Enc}_{\mathrm{KEM}}(\mathrm{PQPK}), \sigma_{\mathrm{PQPK}})`
   to get $`v_2`. If $`v_1 = 0` or $`v_2 = 0`, output $`\bot`.
3. Draw $`(\mathrm{EK}_A, \mathrm{ek}_A)` from $`\mathrm{KeyGen}_g`.
4. Run $`\mathrm{Encaps}(\mathrm{PQPK})` to get $`(\mathrm{ct}, \mathrm{ss})`.
5. Put $`\mathrm{DH}_1 = \mathrm{DH}(\mathrm{ik}_A, \mathrm{SPK})`,
   $`\mathrm{DH}_2 = \mathrm{DH}(\mathrm{ek}_A, \mathrm{IK})` and
   $`\mathrm{DH}_3 = \mathrm{DH}(\mathrm{ek}_A, \mathrm{SPK})`. Put
   $`\mathrm{DH}_4 = \mathrm{DH}(\mathrm{ek}_A, \mathrm{OPK})` if $`o = (\mathrm{OPK}, i_{\mathrm{OPK}})`,
   and $`\mathrm{DH}_4 = \ast` if $`o = \ast`.
6. Put $`(\mathrm{sk}, k_A, k_B) = \mathrm{KDF}(\mathrm{DH}_1, \mathrm{DH}_2, \mathrm{DH}_3, \mathrm{DH}_4, \mathrm{ss})`
   and $`\mathrm{AD} = (\mathrm{IK}_A, \mathrm{IK}, \mathrm{PQPK})`.
7. Run $`E(k_A, \mathrm{AD}, \mu)` to get $`c`.
8. Output the initial message
   $`(\mathrm{IK}_A, \mathrm{EK}_A, \mathrm{ct}, i_{\mathrm{SPK}}, i_{\mathrm{PQPK}}, i_{\mathrm{OPK}}, c)`,
   where $`i_{\mathrm{OPK}} = \ast` if $`o = \ast`, and the session context
   $`(\mathrm{sk}, k_B, \mathrm{AD}, \mu)`.
:::
::::

Steps 2 to 7 follow KS (Section 3.3, pp. 9 and 10): Alice verifies the signatures and aborts
if one fails, she generates an ephemeral key and encapsulates a secret to the KEM key, she
computes $`\mathrm{DH}_1` to $`\mathrm{DH}_4` and the key, and she encrypts. Step 1 is not
in KS. It checks the identity key of the bundle against the key that Alice has pinned. Both
verifications run, whatever the first returns, and the identifiers of the message are those
of the bundle. KS has Alice delete her ephemeral secret, the Diffie-Hellman values and the
KEM secret after the key derivation (KS, Section 3.3, pp. 9 and 10). The model has no
deletion.

::::definition "pqxdh_accept" (lean := "Protocols.Models.PQXDH.accept") (uses := "pqxdh_parameters, pqxdh_dh, pqxdh_recipient_parameters, pqxdh_initial_message, pqxdh_session_context")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.accept -docstrings -comments
Let $`P` be a set of PQXDH parameters whose type $`F` is a field and whose type $`G` is a
vector space over $`F`. Let
$$`p = ((\mathrm{IK}_B, \mathrm{ik}_B), (\mathrm{SPK}_B, \mathrm{spk}_B), \sigma_{\mathrm{SPK}}, o, (\mathrm{PQPK}_B, \mathrm{pqsk}_B))`
be session parameters of Bob, and let
$$`m = (\mathrm{IK}_A, \mathrm{EK}_A, \mathrm{ct}, i_{\mathrm{SPK}}, i_{\mathrm{PQPK}}, i_{\mathrm{OPK}}, c)`
be an initial message. We define $`\mathrm{Accept}_P(p, m)` to be the probabilistic
computation with output in the session contexts, or $`\bot`, given by the following steps.

1. Put $`i^*_{\mathrm{OPK}} = \mathrm{id}_{\mathrm{EC}}(\mathrm{OPK})` if
   $`o = (\mathrm{OPK}, \mathrm{opk})`, and $`i^*_{\mathrm{OPK}} = \ast` if $`o = \ast`. If
   $`i_{\mathrm{SPK}} \neq \mathrm{id}_{\mathrm{EC}}(\mathrm{SPK}_B)`, or
   $`i_{\mathrm{PQPK}} \neq \mathrm{id}_{\mathrm{KEM}}(\mathrm{PQPK}_B)`, or
   $`i_{\mathrm{OPK}} \neq i^*_{\mathrm{OPK}}`, output $`\bot`.
2. Run $`\mathrm{Decaps}(\mathrm{pqsk}_B, \mathrm{ct})`. If the result is $`\bot`, output
   $`\bot`. Otherwise let $`\mathrm{ss}` be the result.
3. Put $`\mathrm{DH}_1 = \mathrm{DH}(\mathrm{spk}_B, \mathrm{IK}_A)`,
   $`\mathrm{DH}_2 = \mathrm{DH}(\mathrm{ik}_B, \mathrm{EK}_A)` and
   $`\mathrm{DH}_3 = \mathrm{DH}(\mathrm{spk}_B, \mathrm{EK}_A)`. Put
   $`\mathrm{DH}_4 = \mathrm{DH}(\mathrm{opk}, \mathrm{EK}_A)` if
   $`o = (\mathrm{OPK}, \mathrm{opk})`, and $`\mathrm{DH}_4 = \ast` if $`o = \ast`.
4. Put $`(\mathrm{sk}, k_A, k_B) = \mathrm{KDF}(\mathrm{DH}_1, \mathrm{DH}_2, \mathrm{DH}_3, \mathrm{DH}_4, \mathrm{ss})`
   and $`\mathrm{AD} = (\mathrm{IK}_A, \mathrm{IK}_B, \mathrm{PQPK}_B)`.
5. If $`D(k_A, \mathrm{AD}, c) = \mathsf{rej}`, output $`\bot`. Otherwise let
   $`\mu = D(k_A, \mathrm{AD}, c)`, and output the session context
   $`(\mathrm{sk}, k_B, \mathrm{AD}, \mu)`.
:::
::::

KS describes these steps in Section 3.4 (p. 10): Bob uses the identifiers to find his keys,
decapsulates, repeats the key derivation, rebuilds the associated data and decrypts. If the
ciphertext does not decrypt, he aborts. The identifier test of step 1 is the model's reading
of "uses the key identifiers to load the private key(s)". KS calls the identifiers "not
security critical" because the keys are signed or in the associated data (KS, Section 4.13,
p. 17). In the model, the identifiers are neither signed nor in the associated data.

::::definition "pqxdh_confirm" (lean := "Protocols.Models.PQXDH.confirm") (uses := "pqxdh_parameters, pqxdh_session_context")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.confirm -docstrings -comments
Let $`P` be a set of PQXDH parameters, let $`(\mathrm{sk}, k_B, \mathrm{AD}, \mu)` be a
session context, and let $`c \in C`. We define
$`\mathrm{Confirm}_P((\mathrm{sk}, k_B, \mathrm{AD}, \mu), c)` to be $`\mathrm{sk}` if
$`D(k_B, \mathrm{AD}, c) = \mu`, and $`\bot` otherwise.
:::
::::

Confirm is a function: unlike the other procedures it is not a computation in the monad of
probabilistic computations. KS has no confirmation. Its exchange ends when Bob decrypts the
first ciphertext of Alice (KS, Section 3.4, pp. 10 and 11). The model adds the confirmation,
because a UAKE asks that the party T, here Bob, speaks last.

# PQXDH as a UAKE

The two UAKE schemes of this section are Galois's formulation of PQXDH as a UAKE. Galois
documents it at
[galoisinc.github.io/libsignal-docs-and-models](https://galoisinc.github.io/libsignal-docs-and-models/).

A UAKE has the party $`T`, which holds a long-term key pair and is authenticated, and the
party $`U`, which is not. In PQXDH, Alice checks the signatures of Bob, and Bob does not
authenticate Alice. The natural choice is $`T = \mathrm{Bob}` and $`U = \mathrm{Alice}`. DF
assume that $`T` speaks last (DF, Section 3, pp. 7 and 8). In PQXDH, Bob speaks first, with
his bundle, and Alice answers. The scheme with $`T = \mathrm{Bob}` therefore adds a third
message, the confirmation of Bob. The model has a second scheme, with $`T = \mathrm{Alice}`,
which needs no third message. The security theorems are about the first scheme. The second
scheme is used for correctness only.

## Messages

The parties exchange three kinds of message: the bundle of Bob, the initial message of
Alice, and the confirmation of Bob.

::::definition "pqxdh_message" (lean := "Protocols.Models.PQXDH.Message") (uses := "pqxdh_prekey_bundle, pqxdh_initial_message")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.Message -docstrings -comments
Let $`G`, $`\mathrm{PQPK}`, $`\mathrm{CT}`, $`S`, $`C`, $`\mathrm{Id}_{\mathrm{EC}}` and
$`\mathrm{Id}_{\mathrm{KEM}}` be types. We define the type $`W` of _messages_ to be the
disjoint union of the prekey bundles, the initial messages and the type $`C`. We write
$`\mathsf{bundle}(\beta)`, $`\mathsf{initial}(m)` and $`\mathsf{confirmation}(c)` for the
elements of the three parts.
:::
::::

The confirmation is a bare AEAD ciphertext. KS has no such message, as the remark after the
definition of Confirm says.

## Bob as the authenticated party

Alice waits for the bundle. She answers it with her initial message, and she completes when
the confirmation of Bob decrypts to her message.

::::definition "pqxdh_initiator" (lean := "Protocols.Models.PQXDH.initiator") (uses := "uake_party, pqxdh_message, pqxdh_initiate, pqxdh_confirm, pqxdh_initiator_parameters, pqxdh_session_context")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.initiator -docstrings -comments
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field
and whose type $`G` is a vector space over $`F`. We define the party $`\mathrm{Alice}_P`
over probabilistic computations, with inputs in the initiator parameters, messages in $`W`
and outputs in $`K + \{\bot\}`, as follows. Its states are the initiator parameters, the
session contexts and the elements of $`K`.

* $`\mathrm{init}(p) = (p, \ast)`: Alice starts in the state $`p` and waits for Bob to
  speak first.
* In a state $`p` that is an initiator parameter, on a message $`\mathsf{bundle}(\beta)`,
  Alice runs $`\mathrm{Initiate}_P(p, \beta)`. If the result is $`\bot`, she rejects. If it
  is $`(m, \kappa)`, she accepts, replies $`\mathsf{initial}(m)` with flag $`0`, and moves to
  the state $`\kappa`.
* In a state $`\kappa` that is a session context, on a message
  $`\mathsf{confirmation}(c)`, Alice computes $`\mathrm{Confirm}_P(\kappa, c)`. If the
  result is $`\bot`, she rejects. If it is $`\mathrm{sk}`, she completes in the state
  $`\mathrm{sk}`.
* In every other case she rejects.
* $`\mathrm{output}(s) = \mathrm{sk}` if $`s = \mathrm{sk} \in K`, and $`\mathrm{output}(s) = \ast`
  for every other state $`s`.
:::
::::

Bob speaks first, so his party starts with a first message.

::::definition "pqxdh_recipient" (lean := "Protocols.Models.PQXDH.recipient") (uses := "uake_party, pqxdh_message, pqxdh_gen_opk, pqxdh_publish, pqxdh_accept, pqxdh_recipient_identity, pqxdh_recipient_parameters")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.recipient -docstrings -comments
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field
and whose type $`G` is a vector space over $`F`, and let $`h \in \{0, 1\}`. We define the
party $`\mathrm{Bob}_{P,h}` over probabilistic computations, with inputs in the long-term
states of Bob, messages in $`W` and outputs in $`K + \{\bot\}`, as follows. Its states are
the session parameters of Bob and the elements of $`K`.

* For the input $`((\mathrm{IK}_B, \mathrm{ik}_B), (\mathrm{SPK}_B, \mathrm{spk}_B), \sigma_{\mathrm{SPK}})`,
  $`\mathrm{init}` draws $`o` from $`\mathrm{GenOPK}_g(h)` and $`(\mathrm{PQPK}_B, \mathrm{pqsk}_B)`
  from $`\mathrm{KeyGen}_\Lambda`, puts
  $`p = ((\mathrm{IK}_B, \mathrm{ik}_B), (\mathrm{SPK}_B, \mathrm{spk}_B), \sigma_{\mathrm{SPK}}, o, (\mathrm{PQPK}_B, \mathrm{pqsk}_B))`,
  and draws $`\beta` from $`\mathrm{Publish}_P(p)`. The result is the state $`p` with the
  first message $`\mathsf{bundle}(\beta)`.
* In a state $`p` that is a session parameter, on a message $`\mathsf{initial}(m)`, Bob runs
  $`\mathrm{Accept}_P(p, m)`. If the result is $`\bot`, he rejects. If it is
  $`\kappa = (\mathrm{sk}, k_B, \mathrm{AD}, \mu)`, he draws $`c` from
  $`E(k_B, \mathrm{AD}, \mu)`, accepts, replies $`\mathsf{confirmation}(c)` with flag $`1`,
  and moves to the state $`\mathrm{sk}`.
* In every other case he rejects.
* $`\mathrm{output}(s) = \mathrm{sk}` if $`s = \mathrm{sk} \in K`, and $`\mathrm{output}(s) = \ast`
  for every other state $`s`.
:::
::::

Both parties output a key or $`\ast`. Neither outputs $`\bot`, because a message that
a party cannot process is rejected and the state does not change. Bob outputs $`\mathrm{sk}`
as soon as he sends the confirmation. He does not wait to learn whether Alice accepts it.
Bob draws a fresh one-time key pair, if $`h = 1`, and a fresh KEM key pair when the exchange
starts, so every session of Bob has its own one-time key and KEM key.

::::definition "pqxdh_uake_initiator" (lean := "Protocols.Models.PQXDH.uakeInitiator") (uses := "uake_scheme, pqxdh_setup, pqxdh_initiator, pqxdh_recipient, pqxdh_initiator_parameters, pqxdh_recipient_identity, pqxdh_message")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.uakeInitiator -docstrings -comments
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field
and whose type $`G` is a vector space over $`F`, let $`\mu \in \mathrm{Msg}`, and let
$`h \in \{0, 1\}`. We define $`\Pi_B(P, \mu, h)` to be the UAKE scheme over probabilistic
computations with key space $`K`, with key inputs in the initiator parameters for $`U` and in
the long-term states of Bob for $`T`, and with messages in $`W`, given by
$`r = 3`, $`\mathrm{Setup} = \mathrm{Setup}_P(\mu)`,
$`U = \mathrm{Alice}_P` and $`T = \mathrm{Bob}_{P,h}`.
:::
::::

An honest run of $`\Pi_B` sends three messages: the bundle, the initial message and the
confirmation. The party $`T` speaks last, as DF assume.

## Alice as the authenticated party

The second scheme makes Alice the party $`T`. She then speaks last with her initial message,
and Bob needs no confirmation. Both parties have a variant without it.

::::definition "pqxdh_initiator_no_confirm" (lean := "Protocols.Models.PQXDH.initiatorNoConfirm") (uses := "uake_party, pqxdh_message, pqxdh_initiate, pqxdh_initiator_parameters")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.initiatorNoConfirm -docstrings -comments
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field
and whose type $`G` is a vector space over $`F`. We define the party
$`\mathrm{Alice}^-_P` over probabilistic computations, with inputs in the initiator
parameters, messages in $`W` and outputs in $`K + \{\bot\}`, as follows. Its states are the
initiator parameters and the elements of $`K`.

* $`\mathrm{init}(p) = (p, \ast)`.
* In a state $`p`, on a message $`\mathsf{bundle}(\beta)`, Alice runs
  $`\mathrm{Initiate}_P(p, \beta)`. If the result is $`\bot`, she rejects. If it is
  $`(m, (\mathrm{sk}, k_B, \mathrm{AD}, \mu))`, she accepts, replies $`\mathsf{initial}(m)`
  with flag $`1`, and moves to the state $`\mathrm{sk}`.
* In every other case she rejects.
* $`\mathrm{output}(s) = \mathrm{sk}` if $`s = \mathrm{sk} \in K`, and $`\mathrm{output}(s) = \ast`
  for every other state $`s`.
:::
::::

::::definition "pqxdh_recipient_no_confirm" (lean := "Protocols.Models.PQXDH.recipientNoConfirm") (uses := "uake_party, pqxdh_message, pqxdh_gen_opk, pqxdh_publish, pqxdh_accept, pqxdh_recipient_identity, pqxdh_recipient_parameters")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.recipientNoConfirm -docstrings -comments
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field
and whose type $`G` is a vector space over $`F`, and let $`h \in \{0, 1\}`. We define the
party $`\mathrm{Bob}^-_{P,h}` over probabilistic computations, with inputs in the long-term
states of Bob, messages in $`W` and outputs in $`K + \{\bot\}`, to be the party
$`\mathrm{Bob}_{P,h}` with the following change. In a state $`p`, on a message
$`\mathsf{initial}(m)`, Bob runs $`\mathrm{Accept}_P(p, m)`. If the result is $`\bot`, he
rejects. If it is $`(\mathrm{sk}, k_B, \mathrm{AD}, \mu)`, he completes in the state
$`\mathrm{sk}`, with no reply.
:::
::::

::::definition "pqxdh_uake_recipient" (lean := "Protocols.Models.PQXDH.uakeRecipient") (uses := "uake_scheme, pqxdh_setup, pqxdh_initiator_no_confirm, pqxdh_recipient_no_confirm, pqxdh_initiator_parameters, pqxdh_recipient_identity, pqxdh_message")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.uakeRecipient -docstrings -comments
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field
and whose type $`G` is a vector space over $`F`, let $`\mu \in \mathrm{Msg}`, and let
$`h \in \{0, 1\}`. We define $`\Pi_A(P, \mu, h)` to be the UAKE scheme over probabilistic
computations with key space $`K`, with key inputs in the long-term states of Bob for $`U` and
in the initiator parameters for $`T`, and with messages in $`W`, given by $`r = 2`,
$`\mathrm{Setup} = \mathrm{swap}(\mathrm{Setup}_P(\mu))`, $`U = \mathrm{Bob}^-_{P,h}` and
$`T = \mathrm{Alice}^-_P`, where $`\mathrm{swap}` exchanges the two components of the output.
:::
::::

An honest run of $`\Pi_A` sends two messages: the bundle and the initial message.

This scheme does not model what UAKE asks of it, and the security theorems do not cover it.
The party $`U` is Bob, and his input is his long-term state, with his secret keys. In DF, the
party $`U` holds only the public key of $`T`, so a security experiment for $`\Pi_A` would hand
the secrets of Bob to the adversary. Also, Alice signs nothing in the model, and KS leaves the
authentication of identity keys to a comparison through an authenticated channel (KS,
Section 4.1, p. 11), so nothing in the exchange authenticates the party
$`T = \mathrm{Alice}^-_P`. We
use $`\Pi_A` for correctness and well-formedness only. The Lean definitions of the security
experiments accept every UAKE scheme, so the restriction rests on this text and on the
documentation of the Lean module
([issue #36](https://github.com/Beneficial-AI-Foundation/libsignal-verify/issues/36)).

# Correctness and well-formedness

Chapter 2 defines perfect correctness and well-formedness of a UAKE scheme. Both schemes of
the model have both properties, if the signature scheme, the KEM and the AEAD scheme are
perfectly correct. The first lemma says what perfect completeness of the signature scheme
means for the identity signature scheme of the model.

::::theorem "pqxdh_sig_perfectly_complete_iff" (lean := "Protocols.Models.PQXDH.sig_perfectlyComplete_iff") (uses := "pqxdh_sig, pqxdh_dh_keygen, sig_perfectly_complete")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.sig_perfectlyComplete_iff -docstrings -comments
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field
and whose type $`G` is a vector space over $`F`. The identity signature scheme $`\Sigma_P` is
perfectly complete under the runtime of probabilistic computations if and only if for every
$`\mu \in G + \mathrm{PQPK}`,
$$`\Pr\big[(X, x) \leftarrow \mathrm{KeyGen}_g;\ \sigma \leftarrow \mathrm{Sign}(X, x, \mu) : \mathrm{Verify}(X, \mu, \sigma) = 1\big] = 1.`
:::
::::

The two sides differ only in how Lean states them: the second is the first, with the key
generation of the model written out.

::::theorem "pqxdh_uake_initiator_perfectly_correct" (lean := "Protocols.Models.PQXDH.uakeInitiator_perfectlyCorrect") (uses := "pqxdh_uake_initiator, pqxdh_parameters, pqxdh_sig, uake_perfectly_correct, kem_perfectly_correct, aead_perfectly_correct, sig_perfectly_complete")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.uakeInitiator_perfectlyCorrect -docstrings -comments
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field
and whose type $`G` is a vector space over $`F`, let $`\mu \in \mathrm{Msg}`, and let
$`h \in \{0, 1\}`. Suppose that, under the runtime of probabilistic computations, the
identity signature scheme $`\Sigma_P` is perfectly complete and the KEM of $`P` is perfectly
correct, and suppose that the AEAD scheme of $`P` is perfectly correct. Then
$`\Pi_B(P, \mu, h)` is perfectly correct under the runtime of probabilistic computations.
:::
::::

::::theorem "pqxdh_uake_recipient_perfectly_correct" (lean := "Protocols.Models.PQXDH.uakeRecipient_perfectlyCorrect") (uses := "pqxdh_uake_recipient, pqxdh_parameters, pqxdh_sig, uake_perfectly_correct, kem_perfectly_correct, aead_perfectly_correct, sig_perfectly_complete")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.uakeRecipient_perfectlyCorrect -docstrings -comments
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field
and whose type $`G` is a vector space over $`F`, let $`\mu \in \mathrm{Msg}`, and let
$`h \in \{0, 1\}`. Suppose that, under the runtime of probabilistic computations, the
identity signature scheme $`\Sigma_P` is perfectly complete and the KEM of $`P` is perfectly
correct, and suppose that the AEAD scheme of $`P` is perfectly correct. Then
$`\Pi_A(P, \mu, h)` is perfectly correct under the runtime of probabilistic computations.
:::
::::

Perfect correctness in the sense of chapter 2 counts a run with output $`\ast` or $`\bot`
as correct, so these theorems alone do not say that the parties finish. The lemmas in their
proofs say more. For $`\Pi_B`, every honest run sends three messages, and both parties output
the same key. The theorems do not state this. Stating it is
[issue #78](https://github.com/Beneficial-AI-Foundation/libsignal-verify/issues/78). The
correctness of the production handshake is a separate question
([issue #72](https://github.com/Beneficial-AI-Foundation/libsignal-verify/issues/72)). The
theorems above concern the abstract model.

The hypothesis on the KEM is an idealisation: the Lean module note says that the KEM of
production decapsulates wrongly with a small probability. Chapter 2 gives the notion of
$`\delta`-correctness, which the theorems do not use.

::::theorem "pqxdh_uake_initiator_well_formed" (lean := "Protocols.Models.PQXDH.uakeInitiator_wellFormed") (uses := "pqxdh_uake_initiator, uake_well_formed, kem_perfectly_correct, aead_perfectly_correct, sig_perfectly_complete")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.uakeInitiator_wellFormed -docstrings -comments
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field
and whose type $`G` is a vector space over $`F`, let $`\mu \in \mathrm{Msg}`, and let
$`h \in \{0, 1\}`. Suppose that, under the runtime of probabilistic computations, the
identity signature scheme $`\Sigma_P` is perfectly complete and the KEM of $`P` is perfectly
correct, and suppose that the AEAD scheme of $`P` is perfectly correct. Then
$`\Pi_B(P, \mu, h)` is well formed.
:::
::::

::::theorem "pqxdh_uake_recipient_well_formed" (lean := "Protocols.Models.PQXDH.uakeRecipient_wellFormed") (uses := "pqxdh_uake_recipient, uake_well_formed, kem_perfectly_correct, aead_perfectly_correct, sig_perfectly_complete")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.uakeRecipient_wellFormed -docstrings -comments
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field
and whose type $`G` is a vector space over $`F`, let $`\mu \in \mathrm{Msg}`, and let
$`h \in \{0, 1\}`. Suppose that, under the runtime of probabilistic computations, the
identity signature scheme $`\Sigma_P` is perfectly complete and the KEM of $`P` is perfectly
correct, and suppose that the AEAD scheme of $`P` is perfectly correct. Then
$`\Pi_A(P, \mu, h)` is well formed.
:::
::::

Well-formedness has three parts: both parties output only at completion, both have pure
output, and an honest run sends exactly $`r` messages. Only the third part uses the three
hypotheses.

# The security theorems

Both theorems bound the advantage $`\mathrm{Adv}_R(\mathcal{A})` of chapter 1, for the
runtime $`R` of probabilistic computations, of an adversary $`\mathcal{A}` against
$`\Pi_B(P, \mu, h)`. The bound is a sum of bounds on the advantage against the primitives of
$`P`, with a factor that counts the sessions that $`\mathcal{A}` opens with $`T`.

::::definition "pqxdh_opens_at_most" (lean := "AKE.UAKE.Adversary.OpensAtMost") (uses := "uake_adversary, uake_oracle_spec, oracle_comp")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.Adversary.OpensAtMost -docstrings -comments
Let $`\Pi` be a UAKE scheme over probabilistic computations, let
$`\mathcal{A} = (\mathcal{A}_1, \mathcal{A}_2)` be an adversary against $`\Pi`, and let
$`q \in \mathbb{N}`. We say that $`\mathcal{A}` _opens at most $`q` sessions_ if the following
two conditions hold.

1. For every key input $`\mathrm{uk}` and every $`w_0`, every execution path of
   $`\mathcal{A}_1(\mathrm{uk}, w_0)` makes at most $`q` queries to the oracle
   $`\mathrm{openT}`.
2. For every state $`s` and every key $`\kappa`, every execution path of
   $`\mathcal{A}_2(s, \kappa)` makes at most $`q` queries to the oracle $`\mathrm{openT}`.
:::
::::

The bound holds for each stage of $`\mathcal{A}`, so the two stages together may open up to
$`2q` sessions. It counts the queries to $`\mathrm{openT}` only, and it puts no limit on the
other queries or on the running time. In Lean, the bound is `IsQueryBoundP` for the queries
that match `openT`, and it holds structurally, on every path of the computation.

The two theorems view the key derivation as a PRF in two ways. In the first, the key is the
KEM secret.

::::definition "pqxdh_kdf_prf" (lean := "Protocols.Models.PQXDH.kdfPRF") (uses := "pqxdh_parameters, prf_scheme, pqxdh_key_material")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.kdfPRF -docstrings -comments
Let $`P` be a set of PQXDH parameters whose type $`\mathrm{SS}` is finite and nonempty. We
define the PRF scheme $`\mathrm{KDF}_{\mathrm{SS}}(P) = (\mathrm{KeyGen}, F)` with key space
$`\mathrm{SS}`, domain $`G \times G \times G \times (G + \{\ast\})` and range
$`K \times K \times K` as follows. The computation $`\mathrm{KeyGen}` draws a key uniformly
from $`\mathrm{SS}`, and
$$`F(\mathrm{ss}, (X_1, X_2, X_3, X_4)) := \mathrm{KDF}(X_1, X_2, X_3, X_4, \mathrm{ss}).`
:::
::::

In the second, the key is the exponent of the third Diffie-Hellman value.

::::definition "pqxdh_kdf_prf_dh" (lean := "Protocols.Models.PQXDH.kdfPRFDH") (uses := "pqxdh_parameters, prf_scheme, pqxdh_key_material")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.kdfPRFDH -docstrings -comments
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field
and whose type $`G` is a vector space over $`F`. We define the PRF scheme
$`\mathrm{KDF}_{\mathrm{DH}}(P) = (\mathrm{KeyGen}, F')` with key space $`F`, domain
$`G \times G \times (G + \{\ast\}) \times \mathrm{SS}` and range $`K \times K \times K` as
follows. The computation $`\mathrm{KeyGen}` draws a key uniformly from $`F`, and
$$`F'(c, (X_1, X_2, X_4, \mathrm{ss})) := \mathrm{KDF}(X_1, X_2, c \cdot g, X_4, \mathrm{ss}).`
:::
::::

In the run of PQXDH, $`\mathrm{DH}_3 = \mathrm{ek}_A \cdot \mathrm{spk}_B \cdot g`, so the key
$`c` of $`\mathrm{KDF}_{\mathrm{DH}}` stands for the product of the two secret exponents of
$`\mathrm{DH}_3`. The adversary of the PRF game chooses the other four arguments.

::::theorem "pqxdh_secure_dh" (lean := "Protocols.Models.PQXDH.uakeInitiator_secure_dh") (uses := "pqxdh_uake_initiator, pqxdh_opens_at_most, pqxdh_kdf_prf_dh, uake_advantage, sig_joint_advantage, dh_gap_advantage, aead_int_ctxt_d_advantage, prf_advantage")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.uakeInitiator_secure_dh -docstrings -comments
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field,
whose type $`G` is a vector space over $`F`, whose type $`K` is finite and nonempty, and whose
type $`S` is nonempty. Let $`\mu \in \mathrm{Msg}`, let $`h \in \{0, 1\}`, let
$`\varepsilon_{\mathrm{sig}}`, $`\varepsilon_{\mathrm{gap}}`, $`\varepsilon_{\mathrm{aead}}`,
$`\varepsilon_{\mathrm{kdf}}` and $`\varepsilon_{\mathrm{pk}}` be real numbers, let
$`q \in \mathbb{N}`, let $`R` be the runtime of probabilistic computations, and let
$`\mathcal{A}` be an adversary against $`\Pi_B(P, \mu, h)` that opens at most $`q` sessions.
Suppose that

1. the map $`\mathrm{id}_{\mathrm{KEM}}` is injective;
2. the verification algorithm is deterministic: for all $`X \in G`,
   $`\nu \in G + \mathrm{PQPK}` and $`\sigma \in S`, there is $`b` such that
   $`\mathrm{Verify}(X, \nu, \sigma)` always outputs $`b`;
3. every joint adversary against $`(\Sigma_P, \mathrm{DH})` has advantage at most
   $`\varepsilon_{\mathrm{sig}}`;
4. every Gap-DH adversary against $`(F, G, g)` has advantage at most
   $`\varepsilon_{\mathrm{gap}}`;
5. every INT-CTXT-D adversary against the AEAD scheme of $`P` has advantage at most
   $`\varepsilon_{\mathrm{aead}}`;
6. every PRF adversary against $`\mathrm{KDF}_{\mathrm{DH}}(P)` has advantage at most
   $`\varepsilon_{\mathrm{kdf}}`;
7. for every $`Y \in \mathrm{PQPK}`, the probability that $`\mathrm{KeyGen}_\Lambda` outputs
   a public key equal to $`Y` is at most $`\varepsilon_{\mathrm{pk}}`.

Then
$$`\mathrm{Adv}_R(\mathcal{A}) \le \varepsilon_{\mathrm{sig}} + 2q\,(\varepsilon_{\mathrm{gap}} + 2\varepsilon_{\mathrm{aead}} + \varepsilon_{\mathrm{kdf}}) + 3q^2\,\varepsilon_{\mathrm{pk}}.`
:::
::::

The third and the fourth hypotheses are the joint unforgeability of the identity signature
scheme and the Gap-DH problem of chapter 2. The fifth is INT-CTXT-D of the AEAD scheme. The
second hypothesis is the Lean statement that verification is deterministic. A comment in the
Lean file calls this a gap in the model, because VCV-io leaves verification probabilistic
although it is deterministic for signature schemes in general.

The theorem for the post-quantum case has no Diffie-Hellman hypothesis. It assumes that the KEM
is perfectly correct and IND-CCA secure, and that the key derivation is a PRF with the KEM
secret as its key.

::::theorem "pqxdh_secure_pq" (lean := "Protocols.Models.PQXDH.uakeInitiator_secure_pq") (uses := "pqxdh_uake_initiator, pqxdh_opens_at_most, pqxdh_kdf_prf, uake_advantage, sig_joint_advantage, kem_perfectly_correct, kem_ind_cca_advantage, aead_int_ctxt_d_advantage, prf_advantage")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.uakeInitiator_secure_pq -docstrings -comments
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field,
whose type $`G` is a vector space over $`F`, whose types $`K` and $`\mathrm{SS}` are finite and
nonempty, and whose types $`S` and $`\mathrm{PQSK}` are nonempty. Let $`\mu \in \mathrm{Msg}`,
let $`h \in \{0, 1\}`, let $`\varepsilon_{\mathrm{sig}}`, $`\varepsilon_{\mathrm{kem}}`,
$`\varepsilon_{\mathrm{aead}}`, $`\varepsilon_{\mathrm{kdf}}` and $`\varepsilon_{\mathrm{pk}}`
be real numbers, let $`q \in \mathbb{N}`, let $`R` be the runtime of probabilistic
computations, and let $`\mathcal{A}` be an adversary against $`\Pi_B(P, \mu, h)` that opens at
most $`q` sessions. Suppose that

1. the map $`\mathrm{id}_{\mathrm{KEM}}` is injective;
2. the verification algorithm is deterministic: for all $`X \in G`,
   $`\nu \in G + \mathrm{PQPK}` and $`\sigma \in S`, there is $`b` such that
   $`\mathrm{Verify}(X, \nu, \sigma)` always outputs $`b`;
3. the KEM $`\Lambda` is perfectly correct under the runtime of probabilistic computations;
4. every joint adversary against $`(\Sigma_P, \mathrm{DH})` has advantage at most
   $`\varepsilon_{\mathrm{sig}}`;
5. every IND-CCA adversary against $`\Lambda` has advantage at most
   $`\varepsilon_{\mathrm{kem}}`;
6. every INT-CTXT-D adversary against the AEAD scheme of $`P` has advantage at most
   $`\varepsilon_{\mathrm{aead}}`;
7. every PRF adversary against $`\mathrm{KDF}_{\mathrm{SS}}(P)` has advantage at most
   $`\varepsilon_{\mathrm{kdf}}`;
8. for every $`Y \in \mathrm{PQPK}`, the probability that $`\mathrm{KeyGen}_\Lambda` outputs
   a public key equal to $`Y` is at most $`\varepsilon_{\mathrm{pk}}`.

Then
$$`\mathrm{Adv}_R(\mathcal{A}) \le \varepsilon_{\mathrm{sig}} + 2q\,(\varepsilon_{\mathrm{kem}} + \varepsilon_{\mathrm{aead}} + \varepsilon_{\mathrm{kdf}}) + 3q^2\,\varepsilon_{\mathrm{pk}}.`
:::
::::

The proofs of both theorems are incomplete. Each adds the bounds of six hops, which the next
section states. Hops 1 to 4 are proved. In each theorem, hops 5 and 6 are lemmas that the Lean
development admits with `sorry`. For the first theorem these are `forgeHonestGoodProb_le_gap`
and `indistAdvantage_le_gap`, and for the second `forgeHonestGoodProb_le_pq` and
`indistAdvantage_le_pq`. VersoBlueprint therefore marks both theorems as depending on `sorry`.
[Issue #81](https://github.com/Beneficial-AI-Foundation/libsignal-verify/issues/81) tracks
the first pair and
[issue #82](https://github.com/Beneficial-AI-Foundation/libsignal-verify/issues/82) the
second. The two bounds are the sums of the hop bounds, with one difference. The six hops of the first
theorem add up to
$`\varepsilon_{\mathrm{sig}} + q\,(2\varepsilon_{\mathrm{gap}} + 3\varepsilon_{\mathrm{aead}} + 2\varepsilon_{\mathrm{kdf}}) + 3q^2\varepsilon_{\mathrm{pk}}`,
and the theorem states $`q\,\varepsilon_{\mathrm{aead}}` more. The second theorem states the
exact sum.

Every hypothesis on a primitive bounds the advantage of every adversary of the primitive,
with no limit on its running time, so the bounds are trivial for every instantiation of
the primitives
([issue #41](https://github.com/Beneficial-AI-Foundation/libsignal-verify/issues/41)).
Two further matters concern the statements. The experiment of chapter 2 counts a session of
$`T` as a partner of the challenge session by the match of the transcripts. The open
[pull request #71](https://github.com/Beneficial-AI-Foundation/libsignal-verify/pull/71)
replaces this by a partnering in which two sessions are partners if they hold the same
associated data and the same key material. It also drops the first hypothesis of both
theorems. The reason is
[issue #35](https://github.com/Beneficial-AI-Foundation/libsignal-verify/issues/35): the
identifiers and the one-time prekey in the bundle are not signed, so an adversary that changes
them gives Alice and Bob the same keys, but the transcripts do not match. The section on
modelling choices below explains the first hypothesis.

# The structure of the proof

The proof of each theorem follows the games of this section. All of them start from the
challenge stage of the experiment of chapter 2. The next definition names the output of this
stage.

::::definition "pqxdh_challenge_result" (lean := "AKE.UAKE.ChallengeResult") (uses := "uake_exp, uake_oracle_spec")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.ChallengeResult -docstrings -comments
Let $`\Pi` be a UAKE scheme with key space $`K`. A _challenge result_ of $`\Pi` is a triple
$`\mathrm{cr} = (K_0, \tau^*, (\tau_1, \dots, \tau_n))`, where $`K_0 \in K + \{\bot\}`, $`\tau^*`
is a transcript and $`\tau_1, \dots, \tau_n` are transcripts. It records the output $`K_0` of
$`U`, with $`\ast` read as $`\bot`, the transcript $`\tau^*` of the challenge session, and the
transcripts $`\tau_1, \dots, \tau_n` of the sessions that the adversary opened with $`T`, in the
order of opening.
:::
::::

In a transcript of $`\Pi_B`, the first message of a session of $`T` is its bundle, and the
first message of the challenge session is the bundle that Alice accepted.

## Events

::::definition "pqxdh_transcript_bundle" (lean := "Protocols.Models.PQXDH.transcriptBundle, Protocols.Models.PQXDH.transcriptStart") (uses := "uake_transcript, pqxdh_message")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.transcriptBundle -docstrings -comments
Let $`\tau` be a transcript with messages in $`W`. We define $`\mathrm{bun}(\tau)` to be
the prekey bundle $`\beta` if the first entry of $`\tau` is a pair $`(\mathsf{bundle}(\beta), t)`,
and $`\ast` if $`\tau` is empty or its first message is not a bundle.
:::
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.transcriptStart -docstrings -comments
Let $`\tau` be a transcript with messages in $`W`. We define $`\mathrm{start}(\tau)` to be
the timestamp of the first entry of $`\tau`, and $`\ast` if $`\tau` is empty.
:::
::::

::::definition "pqxdh_bundles" (lean := "Protocols.Models.PQXDH.oracleBundles, Protocols.Models.PQXDH.challengeBundle") (uses := "pqxdh_challenge_result, pqxdh_transcript_bundle, pqxdh_uake_initiator")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.oracleBundles -docstrings -comments
Let $`\mathrm{cr} = (K_0, \tau^*, (\tau_1, \dots, \tau_n))` be a challenge result. We define
the list $`\mathrm{Bun}_T(\mathrm{cr})` of the _bundles of $`T`_ to be the list of those
$`\mathrm{bun}(\tau_i)` that differ from $`\ast`, in the order of $`i`.
:::
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.challengeBundle -docstrings -comments
Let $`\mathrm{cr} = (K_0, \tau^*, (\tau_1, \dots, \tau_n))` be a challenge result. We define
the _bundle of $`U`_ to be $`\mathrm{Bun}_U(\mathrm{cr}) := \mathrm{bun}(\tau^*)`, which is
$`\ast` if the challenge session has accepted no bundle.
:::
::::

::::definition "pqxdh_honest_bundle" (lean := "Protocols.Models.PQXDH.honestBundle") (uses := "pqxdh_bundles, pqxdh_prekey_bundle, pqxdh_recipient_identity")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.honestBundle -docstrings -comments
Let $`\mathrm{tk}` be the long-term state of Bob, with signed prekey $`\mathrm{SPK}_B`, let
$`\mathrm{cr}` be a challenge result, and let
$$`\beta = (\mathrm{IK}, (\mathrm{SPK}, i_{\mathrm{SPK}}), \sigma_{\mathrm{SPK}}, (\mathrm{PQPK}, i_{\mathrm{PQPK}}), \sigma_{\mathrm{PQPK}}, o)`
be a prekey bundle. We say that $`\beta` is _honest_ for $`\mathrm{tk}` and $`\mathrm{cr}` if
$`\mathrm{SPK} = \mathrm{SPK}_B`, and if the KEM public key $`\mathrm{PQPK}` of $`\beta` is
the KEM public key of some bundle in $`\mathrm{Bun}_T(\mathrm{cr})`.
:::
::::

An honest bundle contains only keys that the challenger produced: the signed prekey of Bob
and a KEM key that a session of $`T` published. The signatures, the identifiers and the
one-time prekey of the bundle are not compared.

::::definition "pqxdh_pqpk_guessed" (lean := "Protocols.Models.PQXDH.pqpkGuessed") (uses := "pqxdh_bundles, pqxdh_transcript_bundle")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.pqpkGuessed -docstrings -comments
Let $`\mathrm{cr} = (K_0, \tau^*, (\tau_1, \dots, \tau_n))` be a challenge result. We say that
the _KEM-key event_ $`\mathrm{Guess}(\mathrm{cr})` holds if one of the following holds.

1. Two bundles in $`\mathrm{Bun}_T(\mathrm{cr})` have the same KEM public key.
2. The bundle $`\mathrm{Bun}_U(\mathrm{cr})` and $`\mathrm{bun}(\tau_i)` have the same KEM
   public key for some $`i`, and $`\mathrm{start}(\tau^*)` and $`\mathrm{start}(\tau_i)` both
   differ from $`\ast` and $`\mathrm{start}(\tau^*) < \mathrm{start}(\tau_i)`.
:::
::::

The first case is a collision of the KEM keys that sessions of $`T` draw. In the second case,
the challenge session accepted a bundle before a session of $`T` carrying the same KEM key was
opened, so the adversary predicted a key that was not yet drawn. A KEM with colliding or
predictable public keys breaks UAKE security. A second session that holds the same KEM key,
and the same one-time prekey when one is in use, accepts a replay of the initial message of the
challenge session and derives the same session key. The adversary can reveal that key without
matching the challenge transcript. No assumption on a primitive excludes the event. Hop 4
below bounds its probability by the bound on the KEM public keys.

## Experiments

The experiments below are defined for a set $`P` of PQXDH parameters, a message $`\mu`, a bit
$`h` and an adversary $`\mathcal{A}` against $`\Pi_B(P, \mu, h)`. Each box states the types
that it needs.

::::definition "pqxdh_challenge_phase" (lean := "Protocols.Models.PQXDH.challengePhase") (uses := "pqxdh_challenge_result, pqxdh_uake_initiator, uake_exp, pqxdh_setup")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.challengePhase -docstrings -comments
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field
and whose type $`G` is a vector space over $`F`, let $`\mu \in \mathrm{Msg}`, let
$`h \in \{0, 1\}`, and let $`\mathcal{A}` be an adversary against $`\Pi_B(P, \mu, h)`. We
define the _challenge phase_ $`\mathrm{Chal}(\mathcal{A})` to be the following computation.
Run $`\mathrm{Setup}_P(\mu)` to get $`(\mathrm{uk}, \mathrm{tk})`, and run step 2 of the
experiment $`\mathsf{Exp}(\mathcal{A})` of chapter 2 with these keys. Output the challenge
result $`\mathrm{cr}` of this step, with the state of $`\mathcal{A}`, the state of the
sessions of $`T`, and $`\mathrm{tk}`.
:::
::::

The challenge bit of the experiment of chapter 2 does not enter the challenge phase. The
experiments below draw it where they need it. This is the first part of
$`\mathsf{Exp}(\mathcal{A})` up to the order of independent draws.

::::definition "pqxdh_forge" (lean := "Protocols.Models.PQXDH.forgeExp, Protocols.Models.PQXDH.forgeProb") (uses := "pqxdh_challenge_phase, uake_ping_pong")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.forgeExp -docstrings -comments
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field
and whose type $`G` is a vector space over $`F`, let $`\mu \in \mathrm{Msg}`, let
$`h \in \{0, 1\}`, and let $`\mathcal{A}` be an adversary against $`\Pi_B(P, \mu, h)`. We
define the _forgery experiment_ $`\mathrm{Forge}(\mathcal{A})` to be the following
computation with output in $`\{0, 1\}`. Run $`\mathrm{Chal}(\mathcal{A})` to get
$`\mathrm{cr} = (K_0, \tau^*, (\tau_1, \dots, \tau_n))`, and output $`1` if $`K_0 \neq \bot`
and $`\mathrm{pingPong}_1(\tau_1, \dots, \tau_n; \tau^*) = 0`, and $`0` otherwise.
:::
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.forgeProb -docstrings -comments
We write $`\mathrm{forge}(\mathcal{A}) := \Pr[\mathrm{Forge}(\mathcal{A}) = 1]` as a real
number.
:::
::::

The first-speaker bit is $`1`, because $`\Pi_B` has $`r = 3` rounds. In a forgery, the
challenge session has completed, and no session of $`T` matches it, so the adversary has
spoofed a message of $`T`.

::::definition "pqxdh_sig_forge" (lean := "Protocols.Models.PQXDH.sigForgeExp, Protocols.Models.PQXDH.sigForgeProb") (uses := "pqxdh_challenge_phase, pqxdh_honest_bundle")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.sigForgeExp -docstrings -comments
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field
and whose type $`G` is a vector space over $`F`, let $`\mu \in \mathrm{Msg}`, let
$`h \in \{0, 1\}`, and let $`\mathcal{A}` be an adversary against $`\Pi_B(P, \mu, h)`. We
define the _signature-forgery experiment_ $`\mathrm{SigForge}(\mathcal{A})` to be the
following computation with output in $`\{0, 1\}`. Run $`\mathrm{Chal}(\mathcal{A})` to get
$`\mathrm{cr} = (K_0, \tau^*, (\tau_1, \dots, \tau_n))` and the long-term state
$`\mathrm{tk}` of Bob. Output $`1` if $`K_0 \neq \bot`, the bundle
$`\mathrm{Bun}_U(\mathrm{cr})` differs from $`\ast`, and it is not honest for $`\mathrm{tk}`
and $`\mathrm{cr}`. Otherwise output $`0`.
:::
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.sigForgeProb -docstrings -comments
We write $`\mathrm{sigForge}(\mathcal{A}) := \Pr[\mathrm{SigForge}(\mathcal{A}) = 1]` as a
real number.
:::
::::

::::definition "pqxdh_guess" (lean := "Protocols.Models.PQXDH.pqpkGuessedExp, Protocols.Models.PQXDH.pqpkGuessedProb") (uses := "pqxdh_challenge_phase, pqxdh_pqpk_guessed")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.pqpkGuessedExp -docstrings -comments
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field
and whose type $`G` is a vector space over $`F`, let $`\mu \in \mathrm{Msg}`, let
$`h \in \{0, 1\}`, and let $`\mathcal{A}` be an adversary against $`\Pi_B(P, \mu, h)`. We
define the _KEM-key experiment_ $`\mathrm{GuessExp}(\mathcal{A})` to be the following
computation with output in $`\{0, 1\}`. Run $`\mathrm{Chal}(\mathcal{A})` to get
$`\mathrm{cr}`, and output $`1` if $`\mathrm{Guess}(\mathrm{cr})` holds, and $`0`
otherwise.
:::
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.pqpkGuessedProb -docstrings -comments
We write $`\mathrm{guess}(\mathcal{A}) := \Pr[\mathrm{GuessExp}(\mathcal{A}) = 1]` as a real
number.
:::
::::

::::definition "pqxdh_forge_honest_good" (lean := "Protocols.Models.PQXDH.forgeHonestGoodExp, Protocols.Models.PQXDH.forgeHonestGoodProb") (uses := "pqxdh_challenge_phase, pqxdh_honest_bundle, pqxdh_pqpk_guessed, uake_ping_pong")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.forgeHonestGoodExp -docstrings -comments
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field
and whose type $`G` is a vector space over $`F`, let $`\mu \in \mathrm{Msg}`, let
$`h \in \{0, 1\}`, and let $`\mathcal{A}` be an adversary against $`\Pi_B(P, \mu, h)`. We
define the _residual forgery experiment_ $`\mathrm{Good}(\mathcal{A})` to be the following
computation with output in $`\{0, 1\}`. Run $`\mathrm{Chal}(\mathcal{A})` to get
$`\mathrm{cr} = (K_0, \tau^*, (\tau_1, \dots, \tau_n))` and the long-term state
$`\mathrm{tk}` of Bob. Output $`1` if $`K_0 \neq \bot`,
$`\mathrm{pingPong}_1(\tau_1, \dots, \tau_n; \tau^*) = 0`, the bundle
$`\mathrm{Bun}_U(\mathrm{cr})` is $`\ast` or honest for $`\mathrm{tk}` and $`\mathrm{cr}`,
and $`\mathrm{Guess}(\mathrm{cr})` does not hold. Otherwise output $`0`.
:::
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.forgeHonestGoodProb -docstrings -comments
We write $`\mathrm{good}(\mathcal{A}) := \Pr[\mathrm{Good}(\mathcal{A}) = 1]` as a real
number.
:::
::::

::::definition "pqxdh_indist" (lean := "Protocols.Models.PQXDH.indistExp, Protocols.Models.PQXDH.indistAdvantage") (uses := "pqxdh_challenge_phase, uake_exp")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.indistExp -docstrings -comments
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field,
whose type $`G` is a vector space over $`F`, and whose type $`K` is finite and nonempty, let
$`\mu \in \mathrm{Msg}`, let $`h \in \{0, 1\}`, and let $`\mathcal{A}` be an adversary against
$`\Pi_B(P, \mu, h)`. We define the _coin-flipped experiment_ $`\mathrm{Ind}(\mathcal{A})` to
be the following computation with output in $`\{0, 1\}`. Run $`\mathrm{Setup}_P(\mu)` to get
$`(\mathrm{uk}, \mathrm{tk})`, draw a uniform bit $`b`, and run step 2 of
$`\mathsf{Exp}(\mathcal{A})` with these keys, to get
$`\mathrm{cr} = (K_0, \tau^*, (\tau_1, \dots, \tau_n))` and a state. Then do the following.

1. If $`K_0 = \bot`, run steps 6 and 7 of $`\mathsf{Exp}(\mathcal{A})` with $`K_b = \bot`,
   and output the result.
2. Otherwise, if $`\mathrm{pingPong}_1(\tau_1, \dots, \tau_n; \tau^*) = 0`, output a uniform
   bit.
3. Otherwise, draw $`K_1` uniformly from $`K`, run steps 6 and 7 of
   $`\mathsf{Exp}(\mathcal{A})` with this $`K_1` and the bit $`b`, and output the result.
:::
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.indistAdvantage -docstrings -comments
We write
$`\mathrm{ind}(\mathcal{A}) := \big|\Pr[\mathrm{Ind}(\mathcal{A}) = 1] - \tfrac{1}{2}\big|` as a
real number.
:::
::::

The experiment is $`\mathsf{Exp}(\mathcal{A})` with one change: where
$`\mathsf{Exp}(\mathcal{A})` outputs $`1` because the challenge session accepted with no
matching session, this experiment outputs a uniform bit.

## The six hops

Hops 1 and 2 use no hypothesis on the primitives. Hop 3 uses the joint unforgeability of the
identity signature scheme, and hop 4 uses the bound on the KEM public keys. Hops 5 and 6 use
the remaining hypotheses of the theorems.

::::theorem "pqxdh_hop1" (lean := "Protocols.Models.PQXDH.advantage_le_forgeProb_add_indistAdvantage") (uses := "pqxdh_forge, pqxdh_indist, uake_advantage")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.advantage_le_forgeProb_add_indistAdvantage (part := "signature") -docstrings -comments
*Hop 1.* Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a
finite field, whose type $`G` is a vector space over $`F`, and whose type $`K` is finite and
nonempty, let $`\mu \in \mathrm{Msg}`, let $`h \in \{0, 1\}`, let $`R` be the runtime of
probabilistic computations, and let $`\mathcal{A}` be an adversary against
$`\Pi_B(P, \mu, h)`. Then
$$`\mathrm{Adv}_R(\mathcal{A}) \le \mathrm{forge}(\mathcal{A}) + \mathrm{ind}(\mathcal{A}).`
:::
::::

::::theorem "pqxdh_hop2" (lean := "Protocols.Models.PQXDH.forgeProb_le_sigForge_add_pqpkGuessed_add_forgeHonestGood") (uses := "pqxdh_forge, pqxdh_sig_forge, pqxdh_guess, pqxdh_forge_honest_good")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.forgeProb_le_sigForge_add_pqpkGuessed_add_forgeHonestGood (part := "signature") -docstrings -comments
*Hop 2.* Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a
finite field and whose type $`G` is a vector space over $`F`, let $`\mu \in \mathrm{Msg}`, let
$`h \in \{0, 1\}`, and let $`\mathcal{A}` be an adversary against $`\Pi_B(P, \mu, h)`. Then
$$`\mathrm{forge}(\mathcal{A}) \le \mathrm{sigForge}(\mathcal{A}) + \mathrm{guess}(\mathcal{A}) + \mathrm{good}(\mathcal{A}).`
:::
::::

Hop 2 is a union bound. In a forgery, the accepted bundle contains a signed key that the
challenger never produced, or the KEM-key event holds, or the forgery has an honest bundle and
no KEM-key event.

Hop 3 reduces a signature forgery to the joint unforgeability game of the identity key.
The reduction runs the challenge phase against a copy of $`\Pi_B` that never reads the secret
$`\mathrm{ik}_B`. It answers the signatures that Bob makes, and the Diffie-Hellman value
$`\mathrm{DH}(\mathrm{ik}_B, \mathrm{EK}_A)` of the procedure Accept, with queries to the
signing oracle and the agreement oracle of the game.

::::definition "pqxdh_sig_adversary" (lean := "Protocols.Models.PQXDH.SigReduction.forgery, Protocols.Models.PQXDH.SigReduction.sigAdversary") (uses := "pqxdh_uake_initiator, pqxdh_challenge_phase, pqxdh_transcript_bundle, pqxdh_setup, pqxdh_publish, pqxdh_accept, sig_joint_adversary")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.SigReduction.forgery -docstrings -comments
Let $`\mathrm{tk}` be the long-term state of Bob, with signed prekey $`\mathrm{SPK}_B` and
signature $`\sigma_B` on it, and let $`\tau` be a transcript. We define the pair
$`\mathrm{forgery}(\mathrm{tk}, \tau) \in (G + \mathrm{PQPK}) \times S` as follows. If
$`\mathrm{bun}(\tau) = \ast`, the pair is $`(\mathrm{Enc}_{\mathrm{EC}}(\mathrm{SPK}_B), \sigma_B)`.
Otherwise write
$$`\mathrm{bun}(\tau) = (\mathrm{IK}, (\mathrm{SPK}, i_{\mathrm{SPK}}), \sigma_{\mathrm{SPK}}, (\mathrm{PQPK}, i_{\mathrm{PQPK}}), \sigma_{\mathrm{PQPK}}, o).`
If $`\mathrm{SPK} = \mathrm{SPK}_B`, the pair is
$`(\mathrm{Enc}_{\mathrm{KEM}}(\mathrm{PQPK}), \sigma_{\mathrm{PQPK}})`. If
$`\mathrm{SPK} \neq \mathrm{SPK}_B`, it is $`(\mathrm{Enc}_{\mathrm{EC}}(\mathrm{SPK}), \sigma_{\mathrm{SPK}})`.
:::
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.SigReduction.sigAdversary -docstrings -comments
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field
and whose type $`G` is a vector space over $`F`, let $`\mu \in \mathrm{Msg}`, let
$`h \in \{0, 1\}`, and let $`\mathcal{A}` be an adversary against $`\Pi_B(P, \mu, h)`. We
define the joint adversary $`B_{\mathcal{A}}` against $`(\Sigma_P, \mathrm{DH})` as follows.
On the public key $`X`, it does these steps.

1. Draw $`(\mathrm{IK}_A, \mathrm{ik}_A)` and $`(\mathrm{SPK}_B, \mathrm{spk}_B)` from
   $`\mathrm{KeyGen}_g`, and obtain $`\sigma_{\mathrm{SPK}}` from a signing query on
   $`\mathrm{Enc}_{\mathrm{EC}}(\mathrm{SPK}_B)`.
2. Fix an element $`x_0 \in F`. Give Alice the initiator parameters
   $`((\mathrm{IK}_A, \mathrm{ik}_A), X, \mu)`, and give Bob the long-term state
   $`((X, x_0), (\mathrm{SPK}_B, \mathrm{spk}_B), \sigma_{\mathrm{SPK}})`.
3. Run the challenge stage of $`\mathsf{Exp}(\mathcal{A})` against $`\Pi_B(P, \mu, h)`, with
   two changes to the procedures of Bob. In $`\mathrm{Publish}_P`, obtain
   $`\sigma_{\mathrm{PQPK}}` from a signing query on $`\mathrm{Enc}_{\mathrm{KEM}}(\mathrm{PQPK}_B)`.
   In $`\mathrm{Accept}_P`, obtain $`\mathrm{DH}_2` from an agreement query on
   $`\mathrm{EK}_A`.
4. Let $`\tau^*` be the transcript of the challenge session and $`\mathrm{tk}` the long-term
   state of Bob, and output $`\mathrm{forgery}(\mathrm{tk}, \tau^*)`.
:::
::::

The pair $`\mathrm{forgery}(\mathrm{tk}, \tau^*)` is a forgery of the joint game when the
accepted bundle contains a signed key that the reduction never had signed. If the challenge
session has accepted no bundle, the pair is the signed prekey of the setup with the signature
that the signing oracle gave, so it is no forgery.

The reduction makes one signing query for the setup and one for each query to
$`\mathrm{openT}`. It makes one agreement query for each query to $`\mathrm{stepT}` that
reaches the computation of $`\mathrm{DH}_2` in Accept. A query that Bob rejects leaves the
session open, so the number of agreement queries is not bounded by the number of sessions. The
Lean development proves no resource bound for the reduction
([issue #41](https://github.com/Beneficial-AI-Foundation/libsignal-verify/issues/41)).

::::theorem "pqxdh_sig_reduction" (lean := "Protocols.Models.PQXDH.SigReduction.sigForgeProb_le_advantage_sigAdversary") (uses := "pqxdh_sig_adversary, pqxdh_sig_forge, sig_joint_advantage")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.SigReduction.sigForgeProb_le_advantage_sigAdversary (part := "signature") -docstrings -comments
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field
and whose type $`G` is a vector space over $`F`, let $`\mu \in \mathrm{Msg}`, let
$`h \in \{0, 1\}`, and let $`\mathcal{A}` be an adversary against $`\Pi_B(P, \mu, h)`. Suppose
that the verification algorithm is deterministic: for all $`X \in G`,
$`\nu \in G + \mathrm{PQPK}` and $`\sigma \in S`, there is $`b` such that
$`\mathrm{Verify}(X, \nu, \sigma)` always outputs $`b`. Then
$$`\mathrm{sigForge}(\mathcal{A}) \le \mathrm{Adv}(B_{\mathcal{A}}),`
where $`\mathrm{Adv}(B_{\mathcal{A}}) = \Pr[\mathsf{JUF}(B_{\mathcal{A}}) = 1]` is the
advantage of $`B_{\mathcal{A}}` against $`(\Sigma_P, \mathrm{DH})` in the joint unforgeability
game of chapter 2, taken as a real number.
:::
::::

The event of $`\mathrm{SigForge}` compares the signed keys, so a different valid signature on
a signed key is no forgery.

::::theorem "pqxdh_hop3" (lean := "Protocols.Models.PQXDH.sigForgeProb_le_sig") (uses := "pqxdh_sig_reduction, pqxdh_sig_forge, sig_joint_advantage")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.sigForgeProb_le_sig -docstrings -comments
*Hop 3.* Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a
finite field and whose type $`G` is a vector space over $`F`, let $`\mu \in \mathrm{Msg}`, let
$`h \in \{0, 1\}`, let $`\varepsilon_{\mathrm{sig}} \in \mathbb{R}`, and let $`\mathcal{A}` be
an adversary against $`\Pi_B(P, \mu, h)`. Suppose that the verification algorithm is
deterministic: for all $`X \in G`, $`\nu \in G + \mathrm{PQPK}` and $`\sigma \in S`, there is
$`b` such that $`\mathrm{Verify}(X, \nu, \sigma)` always outputs $`b`. Suppose also that every
joint adversary against $`(\Sigma_P, \mathrm{DH})` has advantage at most
$`\varepsilon_{\mathrm{sig}}`. Then
$$`\mathrm{sigForge}(\mathcal{A}) \le \varepsilon_{\mathrm{sig}}.`
:::
::::

Hop 3 is proved, and it uses no admitted lemma.

::::theorem "pqxdh_hop4" (lean := "Protocols.Models.PQXDH.pqpkGuessedProb_le") (uses := "pqxdh_guess, pqxdh_opens_at_most")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.pqpkGuessedProb_le (part := "signature") -docstrings -comments
*Hop 4.* Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a
finite field and whose type $`G` is a vector space over $`F`, let $`\mu \in \mathrm{Msg}`, let
$`h \in \{0, 1\}`, let $`q \in \mathbb{N}` and $`\varepsilon_{\mathrm{pk}} \in \mathbb{R}`, and
let $`\mathcal{A}` be an adversary against $`\Pi_B(P, \mu, h)` that opens at most $`q`
sessions. Suppose that for every $`Y \in \mathrm{PQPK}` the probability that
$`\mathrm{KeyGen}_\Lambda` outputs a public key equal to $`Y` is at most
$`\varepsilon_{\mathrm{pk}}`. Then
$$`\mathrm{guess}(\mathcal{A}) \le q^2\,\varepsilon_{\mathrm{pk}}.`
:::
::::

Each session of $`T` draws its KEM public key afresh. The $`j`-th draw hits one of at most $`j`
known keys with probability at most $`j\,\varepsilon_{\mathrm{pk}}`. Only the first condition
of the bound on the sessions is used, the one on the challenge stage. Hop 4 is proved.

The remaining four hops are admitted. Each states the bound that the proof plan in its
docstring is meant to give.

::::theorem "pqxdh_hop5_dh" (lean := "Protocols.Models.PQXDH.forgeHonestGoodProb_le_gap") (uses := "pqxdh_forge_honest_good, pqxdh_opens_at_most, pqxdh_kdf_prf_dh, dh_gap_advantage, aead_int_ctxt_d_advantage, prf_advantage")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.forgeHonestGoodProb_le_gap -docstrings -comments
*Hop 5, Diffie-Hellman case.* Let $`P` be a set of PQXDH parameters with generator $`g`,
whose type $`F` is a finite field, whose type $`G` is a vector space over $`F`, and whose
type $`K` is finite and nonempty. Let $`\mu \in \mathrm{Msg}`, let $`h \in \{0, 1\}`, let
$`q \in \mathbb{N}`, let $`\varepsilon_{\mathrm{gap}}`, $`\varepsilon_{\mathrm{aead}}` and
$`\varepsilon_{\mathrm{kdf}}` be real numbers, and let $`\mathcal{A}` be an adversary against
$`\Pi_B(P, \mu, h)` that opens at most $`q` sessions. Suppose that
$`\mathrm{id}_{\mathrm{KEM}}` is injective, that every Gap-DH adversary has advantage at most
$`\varepsilon_{\mathrm{gap}}`, that every INT-CTXT-D adversary against the AEAD scheme has
advantage at most $`\varepsilon_{\mathrm{aead}}`, and that every PRF adversary against
$`\mathrm{KDF}_{\mathrm{DH}}(P)` has advantage at most $`\varepsilon_{\mathrm{kdf}}`. Then
$$`\mathrm{good}(\mathcal{A}) \le q\,(\varepsilon_{\mathrm{gap}} + 2\varepsilon_{\mathrm{aead}} + \varepsilon_{\mathrm{kdf}}).`
:::
::::

The proof plan in the docstring has four steps. It first finds the unique session of $`T` that
can share the key material of the challenge session. The accepted bundle fixes the identity key,
the signed prekey and the KEM key. The KEM key belongs to one session, by the injectivity of
$`\mathrm{id}_{\mathrm{KEM}}` and the absence of the KEM-key event. The plan then replaces the
output of the key derivation on that key material by a uniform triple, at the cost of a
Gap-DH adversary and a PRF adversary. With the first key uniform, an initial message with a
changed ciphertext is a forgery against the AEAD scheme. With the second key uniform, the
confirmation that Alice accepts was produced by the paired session, again at the cost of an
AEAD adversary, so the transcripts match. The docstring says that the last step does not hold
as stated. The unsigned fields of the bundle and the signatures on honestly signed keys can
change without changing the derived keys. Then the transcripts differ without a forgery
([issue #35](https://github.com/Beneficial-AI-Foundation/libsignal-verify/issues/35)).
[Pull request #71](https://github.com/Beneficial-AI-Foundation/libsignal-verify/pull/71)
changes the experiment for this reason. The factor $`q` is generous. It makes the bound of the
theorem equal to $`\varepsilon_{\mathrm{sig}}` when $`\mathcal{A}` opens no session, because
then completing the challenge session already needs a signature forgery. The statement is
admitted, and VersoBlueprint marks it as containing `sorry`.

::::theorem "pqxdh_hop6_dh" (lean := "Protocols.Models.PQXDH.indistAdvantage_le_gap") (uses := "pqxdh_indist, pqxdh_opens_at_most, pqxdh_kdf_prf_dh, dh_gap_advantage, aead_int_ctxt_d_advantage, prf_advantage")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.indistAdvantage_le_gap -docstrings -comments
*Hop 6, Diffie-Hellman case.* Let $`P` be a set of PQXDH parameters with generator $`g`,
whose type $`F` is a finite field, whose type $`G` is a vector space over $`F`, and whose
type $`K` is finite and nonempty. Let $`\mu \in \mathrm{Msg}`, let $`h \in \{0, 1\}`, let
$`q \in \mathbb{N}`, let $`\varepsilon_{\mathrm{gap}}`, $`\varepsilon_{\mathrm{aead}}`,
$`\varepsilon_{\mathrm{kdf}}` and $`\varepsilon_{\mathrm{pk}}` be real numbers, and let
$`\mathcal{A}` be an adversary against $`\Pi_B(P, \mu, h)` that opens at most $`q` sessions.
Suppose that $`\mathrm{id}_{\mathrm{KEM}}` is injective, that every Gap-DH adversary has
advantage at most $`\varepsilon_{\mathrm{gap}}`, that every INT-CTXT-D adversary against the
AEAD scheme has advantage at most $`\varepsilon_{\mathrm{aead}}`, that every PRF adversary
against $`\mathrm{KDF}_{\mathrm{DH}}(P)` has advantage at most
$`\varepsilon_{\mathrm{kdf}}`, and that for every $`Y \in \mathrm{PQPK}` the probability that
$`\mathrm{KeyGen}_\Lambda` outputs a public key equal to $`Y` is at most
$`\varepsilon_{\mathrm{pk}}`. Then
$$`\mathrm{ind}(\mathcal{A}) \le q\,(\varepsilon_{\mathrm{gap}} + \varepsilon_{\mathrm{aead}} + \varepsilon_{\mathrm{kdf}}) + 2q^2\,\varepsilon_{\mathrm{pk}}.`
:::
::::

In the plan for hop 6, a challenge session with no output, or one in the coin-flipped branch,
gives the adversary no advantage. In the remaining branch the accepted bundle is the bundle of a
session of $`T`, and the same replacement of the key derivation makes the challenge key
uniform. The two stages of $`\mathcal{A}` together open at most $`2q` sessions, which gives at
most $`2q^2` pairs of sessions and the term $`2q^2\,\varepsilon_{\mathrm{pk}}`. The statement is
admitted.

::::theorem "pqxdh_hop5_pq" (lean := "Protocols.Models.PQXDH.forgeHonestGoodProb_le_pq") (uses := "pqxdh_forge_honest_good, pqxdh_opens_at_most, pqxdh_kdf_prf, kem_perfectly_correct, kem_ind_cca_advantage, aead_int_ctxt_d_advantage, prf_advantage")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.forgeHonestGoodProb_le_pq -docstrings -comments
*Hop 5, post-quantum case.* Let $`P` be a set of PQXDH parameters with generator $`g`,
whose type $`F` is a finite field, whose type $`G` is a vector space over $`F`, and whose
types $`K` and $`\mathrm{SS}` are finite and nonempty. Let $`\mu \in \mathrm{Msg}`, let
$`h \in \{0, 1\}`, let $`q \in \mathbb{N}`, let $`\varepsilon_{\mathrm{kem}}`,
$`\varepsilon_{\mathrm{aead}}` and $`\varepsilon_{\mathrm{kdf}}` be real numbers, and let
$`\mathcal{A}` be an adversary against $`\Pi_B(P, \mu, h)` that opens at most $`q` sessions.
Suppose that $`\mathrm{id}_{\mathrm{KEM}}` is injective, that $`\Lambda` is perfectly correct
under the runtime of probabilistic computations, that every IND-CCA adversary against
$`\Lambda` has advantage at most $`\varepsilon_{\mathrm{kem}}`, that every INT-CTXT-D
adversary against the AEAD scheme has advantage at most $`\varepsilon_{\mathrm{aead}}`, and
that every PRF adversary against $`\mathrm{KDF}_{\mathrm{SS}}(P)` has advantage at most
$`\varepsilon_{\mathrm{kdf}}`. Then
$$`\mathrm{good}(\mathcal{A}) \le q\,(\varepsilon_{\mathrm{kem}} + 2\varepsilon_{\mathrm{aead}} + \varepsilon_{\mathrm{kdf}}).`
:::
::::

::::theorem "pqxdh_hop6_pq" (lean := "Protocols.Models.PQXDH.indistAdvantage_le_pq") (uses := "pqxdh_indist, pqxdh_opens_at_most, pqxdh_kdf_prf, kem_perfectly_correct, kem_ind_cca_advantage, prf_advantage")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.indistAdvantage_le_pq -docstrings -comments
*Hop 6, post-quantum case.* Let $`P` be a set of PQXDH parameters with generator $`g`,
whose type $`F` is a finite field, whose type $`G` is a vector space over $`F`, and whose
types $`K` and $`\mathrm{SS}` are finite and nonempty. Let $`\mu \in \mathrm{Msg}`, let
$`h \in \{0, 1\}`, let $`q \in \mathbb{N}`, let $`\varepsilon_{\mathrm{kem}}`,
$`\varepsilon_{\mathrm{kdf}}` and $`\varepsilon_{\mathrm{pk}}` be real numbers, and let
$`\mathcal{A}` be an adversary against $`\Pi_B(P, \mu, h)` that opens at most $`q` sessions.
Suppose that $`\mathrm{id}_{\mathrm{KEM}}` is injective, that $`\Lambda` is perfectly correct
under the runtime of probabilistic computations, that every IND-CCA adversary against
$`\Lambda` has advantage at most $`\varepsilon_{\mathrm{kem}}`, that every PRF adversary
against $`\mathrm{KDF}_{\mathrm{SS}}(P)` has advantage at most $`\varepsilon_{\mathrm{kdf}}`,
and that for every $`Y \in \mathrm{PQPK}` the probability that $`\mathrm{KeyGen}_\Lambda`
outputs a public key equal to $`Y` is at most $`\varepsilon_{\mathrm{pk}}`. Then
$$`\mathrm{ind}(\mathcal{A}) \le q\,(\varepsilon_{\mathrm{kem}} + \varepsilon_{\mathrm{kdf}}) + 2q^2\,\varepsilon_{\mathrm{pk}}.`
:::
::::

The plans of the two post-quantum hops use the IND-CCA security of the KEM in place of the
Gap-DH problem. The plan of hop 5 guesses the session of $`T` that can share the key material,
among the at most $`q` that are opened, and embeds the IND-CCA challenge in it. This replaces
the KEM secret of the challenge session by a uniform one. The key derivation is then a PRF under
a hidden uniform key, and the AEAD step is as in the Diffie-Hellman case. In hop 6, perfect
correctness shows that the paired session decapsulates the relayed ciphertext to the same
secret, so the hop has no AEAD term. Both hops are admitted. The hypothesis of perfect
correctness is an idealisation, as the section on modelling choices says. The plans of the two
Diffie-Hellman hops are stated for the key derivation as a random oracle. The plans of the
post-quantum hops use the PRF model as it stands. The last step of the plan of hop 5 has the
same defect in both cases.

# Modelling choices

This section lists where the model differs from PQXDH as KS state it. It also lists the
assumptions of the two security theorems that are not bounds on a primitive. The module notes
and the docstrings of the Lean files mark most of these points.

## The messages

*The bundle.* In KS, Alice gets the prekey bundle from a server. A UAKE has two parties, so
Bob sends the bundle as his first message.

*The confirmation.* In KS the exchange ends with the initial message of Alice, and only Alice
sends an AEAD ciphertext. DF assume that $`T` speaks last. Chapter 2 notes that a well-formed
scheme in which $`T` does not speak last is trivially insecure as soon as $`U` accepts in an
honest run. In the scheme with $`T = \mathrm{Bob}`, Bob therefore sends a third message. It is
an AEAD ciphertext of the message $`\mu` of Alice under the key $`k_B`, and Alice completes
only if it decrypts to $`\mu`. The confirmation is not part of PQXDH and exists only in the
model.

The initial ciphertext of Alice stands for the initial ciphertext of KS. The Lean module note
says that production sends it as the first message of the Double Ratchet, under keys that the
ratchet derives. So it does not correspond to the code that this repository extracts from
libsignal.

*The direction.* A UAKE authenticates $`T` to $`U`, and the security theorems have
$`T = \mathrm{Bob}`. In PQXDH, Alice signs nothing. The Lean module note says that her
authentication to Bob is implicit, because an adversary cannot compute the Diffie-Hellman
output, and that UAKE security needs explicit authentication. The model therefore states no
security for $`T = \mathrm{Alice}`. The scheme $`\Pi_A` follows the message flow of PQXDH
without the confirmation, and it serves for correctness only. Its roles come from the
definition of a UAKE and carry no claim of security.

## The keys

*One identity key.* Bob has one identity key pair $`(\mathrm{IK}_B, \mathrm{ik}_B)`. It signs
his prekeys and takes part in Diffie-Hellman. The Lean module note says that production does
the same, with XEdDSA and X25519 on one key. The source model of Galois gives Bob a separate
signature key pair. KS says that the earlier analyses avoid modelling the reuse of
$`\mathrm{IK}_B` for both agreement and signing, and that a proof under a joint assumption on
X25519 and XEdDSA "is still needed" (KS, Section 4, p. 11). The signature assumption of the
theorems is such a joint assumption, in the form of chapter 2.

The model draws the secret exponent of a key pair uniformly. The Lean module note says that
production clamps its scalars. How the two key generations relate is open
([issue #75](https://github.com/Beneficial-AI-Foundation/libsignal-verify/issues/75)).

*The signed prekey.* The model treats the signed prekey of Bob and its signature as
permanent, and it creates them in the setup. KS changes the signed prekey periodically (KS,
Section 2.4, p. 6, and Section 3.2, p. 8). The security experiment of a UAKE has only
permanent keys, from the setup, and per-session keys.

*No last-resort KEM key.* Bob has no last-resort KEM key, and the model draws a fresh KEM key
in every session. KS adds a last-resort KEM key when no one-time KEM key is left (KS,
Section 2.5, p. 6, and Section 3.3, p. 9). The model leaves this branch out. A model of it
would be harder to analyse, because the last-resort key is weaker. If no post-quantum one-time
prekey is used in a run, access to a quantum computer and the private key of the last-resort
KEM prekey compromises the earlier session key (KS, Section 4.7, p. 14). A replay is possible
if no one-time curve prekey is used (KS, Sections 4.2 and 4.3).

*Associated data.* The associated data of the model always contains the KEM public key. KS
adds it only if the KEM does not bind it into the ciphertext (KS, Section 3.3, p. 10, and
Section 4.12, pp. 16 and 17). The model needs no assumption on the KEM for this.

## The key derivation

The derivation of the model returns three keys, $`\mathrm{sk}`, $`k_A` and $`k_B`. Alice
encrypts her message under $`k_A`, and Bob encrypts the same message under $`k_B` in the
confirmation. KS lets the AEAD key of Alice be $`\mathrm{SK}` or the output of a PRF keyed by
$`\mathrm{SK}` (KS, Section 3.3, p. 10). The Lean module note says that both options break key
indistinguishability, because an adversary can try a candidate key on the initial ciphertext.
Decryption fails for a random key with high probability, and it succeeds for the real key. The
note adds that KS describes only a PRF-derived AEAD key, which does not suffice. The model
takes the three keys as separate outputs of the derivation. This departs from KS, and the book
does not prove the claim of the note.

The model treats the derivation as a PRF. In the Diffie-Hellman theorem the key of the PRF is a
group element: $`\mathrm{KDF}_{\mathrm{DH}}` replaces $`\mathrm{DH}_3` by $`c \cdot g` for a
uniform exponent $`c`. The derivation must therefore be secure under such a key. This is a
stronger assumption than security under a uniform bit string. In the post-quantum theorem, the
key of the PRF is the KEM secret.

KS describes an analysis in CryptoVerif. It models the hash function as a random oracle for the
secrecy and the authentication of a completed exchange. For forward secrecy against a later
quantum adversary, it models the hash function as a PRF (KS, Section 4, p. 11). The Lean module
note says that the proof of the Diffie-Hellman theorem may need a random oracle in place of a
PRF. The plans of the two Diffie-Hellman hops 5 and 6 are written for that case, and the hops
wait for the decision
([issue #81](https://github.com/Beneficial-AI-Foundation/libsignal-verify/issues/81)). The
plans of the post-quantum hops use the PRF as it stands.

## The signature and the KEM

The signature assumption is joint unforgeability. It does not ask for strong unforgeability,
which also counts a new signature on a message that was signed as a forgery. The Lean module
note says that XEdDSA lacks the strong notion, because its encoding of signatures is not
unique. The note adds that the argument for authentication needs only that no one signs a new
message without the key. The book has not checked this claim about XEdDSA.

The event $`\mathrm{SigForge}` therefore compares signed keys and not the bytes of signatures.
A new signature on a key that Bob signed is no forgery in hop 3. Such a run still fails the
match of transcripts, and it belongs to the residual event of hop 5
([issue #35](https://github.com/Beneficial-AI-Foundation/libsignal-verify/issues/35)).

The theorems assume that the verification algorithm is deterministic. This holds for signature
schemes in general, but the definition of VCV-io leaves verification probabilistic. So the
hypothesis closes a gap of the model.

The theorem for the post-quantum case assumes that the KEM is perfectly correct. The Lean
module note says that production Kyber decapsulates wrongly with a small probability, so this
is an idealisation.

The bound on the KEM public keys is the last hypothesis of both theorems. It bounds the
collisions and the predictions of KEM public keys across the sessions of $`T`. The event
$`\mathrm{Guess}(\mathrm{cr})` of the section on the structure of the proof shows that they
break UAKE security, so no assumption on a primitive can replace the bound.

## Identifiers

The identifiers of the keys are not signed and not in the associated data of the model. KS
says that the identifiers are not security critical, because the key values are signed or in
the associated data (KS, Section 4.13, p. 17). Issue #35 shows that this breaks the match of
transcripts, and pull request #71 changes the experiment.

Both theorems assume that $`\mathrm{id}_{\mathrm{KEM}}` is injective. KS allows an identifier
with a smaller representation than the key, if collisions are unlikely (KS, Section 4.13,
p. 17). Such an identifier is not injective on all keys. The Lean module note says that the
hypothesis fails for production. There the identifiers are 32-bit prekey identifiers, and no
map from the KEM public keys of 1568 bytes to them is injective. A collision-resistant
identifier would be an improvement. Pull request #71 drops the hypothesis.

## The post-quantum theorem

PQXDH is designed to prevent attacks that record messages today and decrypt them with a
quantum computer later. For this, only the secrecy of the session key matters (KS,
Section 4.7, p. 14). KS says that PQXDH does not protect against an active quantum adversary,
who can compute the secret keys of curve keys and then impersonate Alice (KS, Section 4.8,
p. 15).

UAKE security has two parts, the secrecy of the key and the authenticity of $`T`, and it
cannot state secrecy alone. The post-quantum theorem therefore proves UAKE security for an
adversary that may break Diffie-Hellman, which is how the Lean docstring puts it. It assumes
the joint unforgeability of the identity signature scheme. In PQXDH the signature is an
elliptic-curve signature, which a quantum adversary breaks. So this hypothesis does not hold in
the post-quantum setting. A secrecy-only notion in place of UAKE would not need the
hypothesis. The theorem therefore does not express the aim of PQXDH.

## What the bounds cover

The experiment counts only the sessions that the adversary opens with $`T`. Each stage of the
adversary may open $`q` of them, so the number of sessions is up to $`2q`. Hops 5 and 6 carry
the factor $`q`, and hop 6 carries $`2q^2` for the pairs of sessions.

The hypotheses on the primitives bound every adversary, with no resource limit. So the bounds
say nothing about efficient adversaries
([issue #41](https://github.com/Beneficial-AI-Foundation/libsignal-verify/issues/41)). The
correctness and the security of the production handshake are tracked in
[issue #72](https://github.com/Beneficial-AI-Foundation/libsignal-verify/issues/72) and
[issue #79](https://github.com/Beneficial-AI-Foundation/libsignal-verify/issues/79).
