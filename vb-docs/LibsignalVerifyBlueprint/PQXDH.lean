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
$$`\begin{aligned}&((\mathrm{IK}_A, \mathrm{ik}_A), \mathrm{IK}_B, \mu)\\ &\in (G \times F) \times G \times \mathrm{Msg},\end{aligned}`
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
$$`\begin{aligned}&((\mathrm{IK}_B, \mathrm{ik}_B), (\mathrm{SPK}_B, \mathrm{spk}_B), \sigma_{\mathrm{SPK}})\\ &\in (G \times F) \times (G \times F) \times S,\end{aligned}`
where $`(\mathrm{IK}_B, \mathrm{ik}_B)` is the identity key pair of Bob,
$`(\mathrm{SPK}_B, \mathrm{spk}_B)` is his signed prekey pair, and $`\sigma_{\mathrm{SPK}}` is
the signature on the signed prekey.
:::
::::

::::definition "pqxdh_recipient_parameters" (lean := "Protocols.Models.PQXDH.RecipientParameters")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.RecipientParameters -docstrings -comments
Let $`F`, $`G`, $`\mathrm{PQPK}`, $`\mathrm{PQSK}` and $`S` be types. We define the _session
parameters of Bob_ to be the tuples
$$`\begin{aligned}(&(\mathrm{IK}_B, \mathrm{ik}_B), (\mathrm{SPK}_B, \mathrm{spk}_B),\\ &\sigma_{\mathrm{SPK}}, o, (\mathrm{PQPK}_B, \mathrm{pqsk}_B)),\end{aligned}`
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
$$`\begin{aligned}(&\mathrm{IK}, (\mathrm{SPK}, i_{\mathrm{SPK}}), \sigma_{\mathrm{SPK}},\\ &(\mathrm{PQPK}, i_{\mathrm{PQPK}}), \sigma_{\mathrm{PQPK}}, o)\end{aligned}`
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
$$`\begin{aligned}(&\mathrm{IK}_A, \mathrm{EK}_A, \mathrm{ct}, i_{\mathrm{SPK}},\\ &i_{\mathrm{PQPK}}, i_{\mathrm{OPK}}, c)\end{aligned}`
in $`G \times G \times \mathrm{CT} \times \mathrm{Id}_{\mathrm{EC}} \times \mathrm{Id}_{\mathrm{KEM}} \times (\mathrm{Id}_{\mathrm{EC}} + \{\ast\}) \times C`.
It has the identity public key and the ephemeral public key of Alice, a KEM ciphertext, the
identifiers of the signed prekey, of the KEM prekey and of the one-time prekey, which may be
absent, and an AEAD ciphertext.
:::
::::

KS lists the same items for the initial message (KS, Section 3.3, p. 10).

::::definition "pqxdh_session_context" (lean := "Protocols.Models.PQXDH.SessionContext") (uses := "pqxdh_key_material")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.SessionContext -docstrings -comments
Let $`G`, $`\mathrm{PQPK}`, $`\mathrm{Msg}`, $`K` and $`\mathrm{SS}` be types. A _session
context_ is a tuple
$$`\begin{aligned}&(\mathrm{sk}, k_B, \mathrm{AD}, \mu, \mathrm{km})\\ &\in K \times K \times (G \times G \times \mathrm{PQPK}) \times \mathrm{Msg} \times \mathrm{KM}(G, \mathrm{SS}),\end{aligned}`
with a session key $`\mathrm{sk}`, an AEAD key $`k_B`, associated data $`\mathrm{AD}`, a
message $`\mu` and the key material $`\mathrm{km}` that the session passed to the key
derivation.
:::
::::

Alice stores a session context when she sends her initial message, and she keeps it when she
completes. Bob stores one when he accepts her message. The key $`k_B` and the message serve the
confirmation message that Bob sends in the model and not in the protocol. The security
theorems compare the associated data and the key material of two sessions.

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
$$`\begin{aligned}p = (&(\mathrm{IK}_B, \mathrm{ik}_B), (\mathrm{SPK}_B, \mathrm{spk}_B),\\ &\sigma_{\mathrm{SPK}}, o, (\mathrm{PQPK}_B, \mathrm{pqsk}_B))\end{aligned}`
be session parameters of Bob. We define $`\mathrm{Publish}_P(p)` to be the probabilistic
computation with output in the prekey bundles that draws $`\sigma_{\mathrm{PQPK}}` from
$`\mathrm{Sign}(\mathrm{IK}_B, \mathrm{ik}_B, \mathrm{Enc}_{\mathrm{KEM}}(\mathrm{PQPK}_B))` and
outputs the bundle
$$`\begin{aligned}(&\mathrm{IK}_B, (\mathrm{SPK}_B, \mathrm{id}_{\mathrm{EC}}(\mathrm{SPK}_B)), \sigma_{\mathrm{SPK}},\\ &(\mathrm{PQPK}_B, \mathrm{id}_{\mathrm{KEM}}(\mathrm{PQPK}_B)), \sigma_{\mathrm{PQPK}}, o'),\end{aligned}`
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
$$`\begin{aligned}\beta = (&\mathrm{IK}, (\mathrm{SPK}, i_{\mathrm{SPK}}), \sigma_{\mathrm{SPK}},\\ &(\mathrm{PQPK}, i_{\mathrm{PQPK}}), \sigma_{\mathrm{PQPK}}, o)\end{aligned}`
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
6. Put $`\mathrm{km} = (\mathrm{DH}_1, \mathrm{DH}_2, \mathrm{DH}_3, \mathrm{DH}_4, \mathrm{ss})`,
   $`(\mathrm{sk}, k_A, k_B) = \mathrm{KDF}(\mathrm{km})`
   and $`\mathrm{AD} = (\mathrm{IK}_A, \mathrm{IK}, \mathrm{PQPK})`.
7. Run $`E(k_A, \mathrm{AD}, \mu)` to get $`c`.
8. Output the initial message
   $`(\mathrm{IK}_A, \mathrm{EK}_A, \mathrm{ct}, i_{\mathrm{SPK}}, i_{\mathrm{PQPK}}, i_{\mathrm{OPK}}, c)`,
   where $`i_{\mathrm{OPK}} = \ast` if $`o = \ast`, and the session context
   $`(\mathrm{sk}, k_B, \mathrm{AD}, \mu, \mathrm{km})`.
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
$$`\begin{aligned}p = (&(\mathrm{IK}_B, \mathrm{ik}_B), (\mathrm{SPK}_B, \mathrm{spk}_B),\\ &\sigma_{\mathrm{SPK}}, o, (\mathrm{PQPK}_B, \mathrm{pqsk}_B))\end{aligned}`
be session parameters of Bob, and let
$$`\begin{aligned}m = (&\mathrm{IK}_A, \mathrm{EK}_A, \mathrm{ct}, i_{\mathrm{SPK}},\\ &i_{\mathrm{PQPK}}, i_{\mathrm{OPK}}, c)\end{aligned}`
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
4. Put $`\mathrm{km} = (\mathrm{DH}_1, \mathrm{DH}_2, \mathrm{DH}_3, \mathrm{DH}_4, \mathrm{ss})`,
   $`(\mathrm{sk}, k_A, k_B) = \mathrm{KDF}(\mathrm{km})`
   and $`\mathrm{AD} = (\mathrm{IK}_A, \mathrm{IK}_B, \mathrm{PQPK}_B)`.
5. If $`D(k_A, \mathrm{AD}, c) = \mathsf{rej}`, output $`\bot`. Otherwise let
   $`\mu = D(k_A, \mathrm{AD}, c)`, and output the session context
   $`(\mathrm{sk}, k_B, \mathrm{AD}, \mu, \mathrm{km})`.
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
Let $`P` be a set of PQXDH parameters, let $`(\mathrm{sk}, k_B, \mathrm{AD}, \mu, \mathrm{km})`
be a session context, and let $`c \in C`. We define
$`\mathrm{Confirm}_P((\mathrm{sk}, k_B, \mathrm{AD}, \mu, \mathrm{km}), c)` to be
$`\mathrm{sk}` if $`D(k_B, \mathrm{AD}, c) = \mu`, and $`\bot` otherwise.
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
session contexts that wait for a confirmation, and the completed session contexts.

* $`\mathrm{init}(p) = (p, \ast)`: Alice starts in the state $`p` and waits for Bob to
  speak first.
* In a state $`p` that is an initiator parameter, on a message $`\mathsf{bundle}(\beta)`,
  Alice runs $`\mathrm{Initiate}_P(p, \beta)`. If the result is $`\bot`, she rejects. If it
  is $`(m, \kappa)`, she accepts, replies $`\mathsf{initial}(m)` with flag $`0`, and moves to
  the state $`\kappa`, waiting for a confirmation.
* In a state $`\kappa` that waits for a confirmation, on a message
  $`\mathsf{confirmation}(c)`, Alice computes $`\mathrm{Confirm}_P(\kappa, c)`. If the
  result is $`\bot`, she rejects. Otherwise she completes in the state $`\kappa`, marked as
  completed.
* In every other case she rejects.
* $`\mathrm{output}(s)` is the session key $`\mathrm{sk}` of $`\kappa` if $`s` is a completed
  session context $`\kappa`, and $`\mathrm{output}(s) = \ast` for every other state $`s`.
:::
::::

Bob speaks first, so his party starts with a first message.

::::definition "pqxdh_recipient" (lean := "Protocols.Models.PQXDH.recipient") (uses := "uake_party, pqxdh_message, pqxdh_gen_opk, pqxdh_publish, pqxdh_accept, pqxdh_recipient_identity, pqxdh_recipient_parameters")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.recipient -docstrings -comments
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field
and whose type $`G` is a vector space over $`F`, and let $`h \in \{0, 1\}`. We define the
party $`\mathrm{Bob}_{P,h}` over probabilistic computations, with inputs in the long-term
states of Bob, messages in $`W` and outputs in $`K + \{\bot\}`, as follows. Its states are
the session parameters of Bob and the session contexts.

* For the input $`((\mathrm{IK}_B, \mathrm{ik}_B), (\mathrm{SPK}_B, \mathrm{spk}_B), \sigma_{\mathrm{SPK}})`,
  $`\mathrm{init}` draws $`o` from $`\mathrm{GenOPK}_g(h)` and $`(\mathrm{PQPK}_B, \mathrm{pqsk}_B)`
  from $`\mathrm{KeyGen}_\Lambda`, puts
  $`p = ((\mathrm{IK}_B, \mathrm{ik}_B), (\mathrm{SPK}_B, \mathrm{spk}_B), \sigma_{\mathrm{SPK}}, o, (\mathrm{PQPK}_B, \mathrm{pqsk}_B))`,
  and draws $`\beta` from $`\mathrm{Publish}_P(p)`. The result is the state $`p` with the
  first message $`\mathsf{bundle}(\beta)`.
* In a state $`p` that is a session parameter, on a message $`\mathsf{initial}(m)`, Bob runs
  $`\mathrm{Accept}_P(p, m)`. If the result is $`\bot`, he rejects. If it is
  $`\kappa = (\mathrm{sk}, k_B, \mathrm{AD}, \mu, \mathrm{km})`, he draws $`c` from
  $`E(k_B, \mathrm{AD}, \mu)`, accepts, replies $`\mathsf{confirmation}(c)` with flag $`1`,
  and moves to the state $`\kappa`.
* In every other case he rejects.
* $`\mathrm{output}(s)` is the session key $`\mathrm{sk}` of $`\kappa` if $`s` is a session
  context $`\kappa`, and $`\mathrm{output}(s) = \ast` for every other state $`s`.
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
  $`(m, (\mathrm{sk}, k_B, \mathrm{AD}, \mu, \mathrm{km}))`, she accepts, replies $`\mathsf{initial}(m)`
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
$`\mathrm{Bob}_{P,h}` with the following changes. Its states are the session parameters of Bob
and the elements of $`K`. In a state $`p`, on a message
$`\mathsf{initial}(m)`, Bob runs $`\mathrm{Accept}_P(p, m)`. If the result is $`\bot`, he
rejects. If it is $`(\mathrm{sk}, k_B, \mathrm{AD}, \mu, \mathrm{km})`, he completes in the
state $`\mathrm{sk}`, with no reply. $`\mathrm{output}(s) = \mathrm{sk}` if
$`s = \mathrm{sk} \in K`, and $`\mathrm{output}(s) = \ast` for every other state $`s`.
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
$$`\begin{aligned}\Pr\big[&(X, x) \leftarrow \mathrm{KeyGen}_g;\ \sigma \leftarrow \mathrm{Sign}(X, x, \mu)\\ &: \mathrm{Verify}(X, \mu, \sigma) = 1\big] = 1.\end{aligned}`
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

The security theorems use the experiment of chapter 2 with two of its tests changed. The two
tests compare the states of the challenge session and of a session of $`T` under a partnering,
in place of their transcripts.

::::definition "uake_partnered_exp" (lean := "AKE.UAKE.Partnering, AKE.UAKE.authPartnered, AKE.UAKE.revealedPartnered, AKE.UAKE.PartneredExp, AKE.UAKE.partneredAdvantage") (uses := "uake_exp, uake_scheme, uake_transcript")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.Partnering -docstrings
Let $`\Pi` be a UAKE scheme. A _partnering_ $`\pi` for $`\Pi` is a relation between the
states of $`U` and the states of $`T`. A state of $`U` and a state of $`T` that are related are
_partners_ under $`\pi`.
:::
:::LibsignalVerifyBlueprint.pair AKE.UAKE.authPartnered -docstrings
Let $`\pi` be a partnering for $`\Pi`, let $`s^*` be a state of $`U` and $`\tau^*` a
transcript, and let a list of sessions with $`T` be given. We say that $`s^*` has an
_authentication partner_ among these sessions if one of them has a key in $`K`, has a state
that is a partner of $`s^*` under $`\pi`, and has a nonempty transcript whose last timestamp is
at most the last timestamp of $`\tau^*`, which is nonempty too.
:::
:::LibsignalVerifyBlueprint.pair AKE.UAKE.revealedPartnered -docstrings
Let $`\pi` be a partnering for $`\Pi`, let $`s^*` be a state of $`U`, and let a list of
sessions with $`T` be given. We say that $`s^*` has a _revealed partner_ among these sessions if
one of them is marked as revealed and has a state that is a partner of $`s^*` under $`\pi`.
:::
:::LibsignalVerifyBlueprint.pair AKE.UAKE.PartneredExp -docstrings
Let $`\Pi` be a UAKE scheme over a monad $`m` whose key space $`K` is finite and nonempty, let
$`\iota` be a monad morphism from probabilistic computations to $`m`, let $`\pi` be a
partnering for $`\Pi`, and let $`\mathcal{A}` be an adversary against $`\Pi`. We define the
_partnered experiment_ $`\mathsf{Exp}_\pi(\mathcal{A})` to be the experiment
$`\mathsf{Exp}(\mathcal{A})` of chapter 2 with two changes.

* In step 4, output $`1` if the state of the challenge session has no authentication partner
  under $`\pi` among the sessions with $`T`, with $`\tau^*` as its transcript, both read at the
  end of step 2.
* In step 7, output a uniform bit if the state of the challenge session has a revealed partner
  under $`\pi` among the sessions with $`T`, both read at the end of step 6.
:::
:::LibsignalVerifyBlueprint.pair AKE.UAKE.partneredAdvantage -docstrings
Let $`R` be a runtime for $`m`. The advantage of $`\mathcal{A}` in the partnered experiment is
$$`\mathrm{Adv}_{R,\pi}(\mathcal{A}) := \big|\Pr_R[\mathsf{Exp}_\pi(\mathcal{A}) = 1] - \tfrac{1}{2}\big|,`
where the experiment uses the monad morphism of $`R`.
:::
::::

The test of step 4 asks for a partner that accepted no later than the challenge session, and
the test of step 7 has no condition on time. In Lean, `finalizePartnered` runs steps 6 and 7.

::::definition "pqxdh_original_key_partnering" (lean := "Protocols.Models.PQXDH.originalKeyPartnering") (uses := "uake_partnered_exp, pqxdh_uake_initiator, pqxdh_session_context, pqxdh_initiator, pqxdh_recipient")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.originalKeyPartnering -docstrings -comments
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field
and whose type $`G` is a vector space over $`F`, let $`\mu \in \mathrm{Msg}`, and let
$`h \in \{0, 1\}`. We define _original-key partnering_ $`\pi_{\mathrm{ok}}` for
$`\Pi_B(P, \mu, h)` as follows. A state of $`\mathrm{Alice}_P` and a state of
$`\mathrm{Bob}_{P,h}` are partners if the state of Alice is a completed session context
$`\kappa_A`, the state of Bob is a session context $`\kappa_B`, and $`\kappa_A` and
$`\kappa_B` have the same associated data and the same key material.
:::
::::

The identifiers of the keys, the signatures and the one-time prekey of the bundle are not
compared, so they are not authenticated: a run that changes them without changing the key
material keeps the partner.

Both theorems bound the advantage $`\mathrm{Adv}_{R,\pi_{\mathrm{ok}}}(\mathcal{A})` in the
partnered experiment over original-key partnering, for the runtime $`R` of probabilistic
computations, of an adversary $`\mathcal{A}` against $`\Pi_B(P, \mu, h)`. The bound is a sum of bounds on the advantage against the primitives of
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
$$`\begin{aligned}&F(\mathrm{ss}, (X_1, X_2, X_3, X_4)) :=\\ &\quad \mathrm{KDF}(X_1, X_2, X_3, X_4, \mathrm{ss}).\end{aligned}`
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
$$`\begin{aligned}&F'(c, (X_1, X_2, X_4, \mathrm{ss})) :=\\ &\quad \mathrm{KDF}(X_1, X_2, c \cdot g, X_4, \mathrm{ss}).\end{aligned}`
:::
::::

In the run of PQXDH, $`\mathrm{DH}_3 = \mathrm{ek}_A \cdot \mathrm{spk}_B \cdot g`, so the key
$`c` of $`\mathrm{KDF}_{\mathrm{DH}}` stands for the product of the two secret exponents of
$`\mathrm{DH}_3`. The adversary of the PRF game chooses the other four arguments.

::::theorem "pqxdh_secure_dh" (lean := "Protocols.Models.PQXDH.uakeInitiator_secure_dh") (uses := "pqxdh_uake_initiator, pqxdh_opens_at_most, pqxdh_kdf_prf_dh, uake_partnered_exp, pqxdh_original_key_partnering, sig_joint_advantage, dh_gap_advantage, aead_int_ctxt_d_advantage, prf_advantage")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.uakeInitiator_secure_dh -docstrings -comments
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field,
whose type $`G` is a vector space over $`F`, whose type $`K` is finite and nonempty, and whose
type $`S` is nonempty. Let $`\mu \in \mathrm{Msg}`, let $`h \in \{0, 1\}`, let
$`\varepsilon_{\mathrm{sig}}`, $`\varepsilon_{\mathrm{gap}}`, $`\varepsilon_{\mathrm{aead}}`,
$`\varepsilon_{\mathrm{kdf}}` and $`\varepsilon_{\mathrm{pk}}` be real numbers, let
$`q \in \mathbb{N}`, let $`R` be the runtime of probabilistic computations, and let
$`\mathcal{A}` be an adversary against $`\Pi_B(P, \mu, h)` that opens at most $`q` sessions.
Suppose that

1. the verification algorithm is deterministic: for all $`X \in G`,
   $`\nu \in G + \mathrm{PQPK}` and $`\sigma \in S`, there is $`b` such that
   $`\mathrm{Verify}(X, \nu, \sigma) = \mathrm{pure}(b)`, the computation that returns $`b`;
2. every joint adversary against $`(\Sigma_P, \mathrm{DH})` has advantage at most
   $`\varepsilon_{\mathrm{sig}}`;
3. every Gap-DH adversary against $`(F, G, g)` has advantage at most
   $`\varepsilon_{\mathrm{gap}}`;
4. every INT-CTXT-D adversary against the AEAD scheme of $`P` has advantage at most
   $`\varepsilon_{\mathrm{aead}}`;
5. every PRF adversary against $`\mathrm{KDF}_{\mathrm{DH}}(P)` has advantage at most
   $`\varepsilon_{\mathrm{kdf}}`;
6. for every $`Y \in \mathrm{PQPK}`, the probability that $`\mathrm{KeyGen}_\Lambda` outputs
   a public key equal to $`Y` is at most $`\varepsilon_{\mathrm{pk}}`.

Then
$$`\begin{aligned}\mathrm{Adv}_{R,\pi_{\mathrm{ok}}}(\mathcal{A}) \le{}& \varepsilon_{\mathrm{sig}} + 2q\,(\varepsilon_{\mathrm{gap}} + 2\varepsilon_{\mathrm{aead}} + \varepsilon_{\mathrm{kdf}})\\ &+ 3q^2\,\varepsilon_{\mathrm{pk}}.\end{aligned}`
:::
::::

The second and the third hypotheses are the joint unforgeability of the identity signature
scheme and the Gap-DH problem of chapter 2. The fourth is INT-CTXT-D of the AEAD scheme. The
first hypothesis is the Lean statement that verification is deterministic. A comment in the
Lean file calls this a gap in the model, because VCV-io leaves verification probabilistic
although it is deterministic for signature schemes in general.

The theorem for the post-quantum case has no Diffie-Hellman hypothesis. It assumes that the KEM
is perfectly correct and IND-CCA secure, and that the key derivation is a PRF with the KEM
secret as its key.

::::theorem "pqxdh_secure_pq" (lean := "Protocols.Models.PQXDH.uakeInitiator_secure_pq") (uses := "pqxdh_uake_initiator, pqxdh_opens_at_most, pqxdh_kdf_prf, uake_partnered_exp, pqxdh_original_key_partnering, sig_joint_advantage, kem_perfectly_correct, kem_ind_cca_advantage, aead_int_ctxt_d_advantage, prf_advantage")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.uakeInitiator_secure_pq -docstrings -comments
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field,
whose type $`G` is a vector space over $`F`, whose types $`K` and $`\mathrm{SS}` are finite and
nonempty, and whose types $`S` and $`\mathrm{PQSK}` are nonempty. Let $`\mu \in \mathrm{Msg}`,
let $`h \in \{0, 1\}`, let $`\varepsilon_{\mathrm{sig}}`, $`\varepsilon_{\mathrm{kem}}`,
$`\varepsilon_{\mathrm{aead}}`, $`\varepsilon_{\mathrm{kdf}}` and $`\varepsilon_{\mathrm{pk}}`
be real numbers, let $`q \in \mathbb{N}`, let $`R` be the runtime of probabilistic
computations, and let $`\mathcal{A}` be an adversary against $`\Pi_B(P, \mu, h)` that opens at
most $`q` sessions. Suppose that

1. the verification algorithm is deterministic: for all $`X \in G`,
   $`\nu \in G + \mathrm{PQPK}` and $`\sigma \in S`, there is $`b` such that
   $`\mathrm{Verify}(X, \nu, \sigma) = \mathrm{pure}(b)`, the computation that returns $`b`;
2. the KEM $`\Lambda` is perfectly correct under the runtime of probabilistic computations;
3. every joint adversary against $`(\Sigma_P, \mathrm{DH})` has advantage at most
   $`\varepsilon_{\mathrm{sig}}`;
4. every IND-CCA adversary against $`\Lambda` has advantage at most
   $`\varepsilon_{\mathrm{kem}}`;
5. every INT-CTXT-D adversary against the AEAD scheme of $`P` has advantage at most
   $`\varepsilon_{\mathrm{aead}}`;
6. every PRF adversary against $`\mathrm{KDF}_{\mathrm{SS}}(P)` has advantage at most
   $`\varepsilon_{\mathrm{kdf}}`;
7. for every $`Y \in \mathrm{PQPK}`, the probability that $`\mathrm{KeyGen}_\Lambda` outputs
   a public key equal to $`Y` is at most $`\varepsilon_{\mathrm{pk}}`.

Then
$$`\begin{aligned}\mathrm{Adv}_{R,\pi_{\mathrm{ok}}}(\mathcal{A}) \le{}& \varepsilon_{\mathrm{sig}} + 2q\,(\varepsilon_{\mathrm{kem}} + \varepsilon_{\mathrm{aead}} + \varepsilon_{\mathrm{kdf}})\\ &+ 3q^2\,\varepsilon_{\mathrm{pk}}.\end{aligned}`
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
The theorems use original-key partnering and not the matching of transcripts of the experiment
of chapter 2. Under transcript matching, a run in which the adversary changes only the
identifiers in the bundle, which are not signed, gives Alice and Bob the same keys, but the
transcripts do not match, and the run counts as a forgery
([issue #35](https://github.com/Beneficial-AI-Foundation/libsignal-verify/issues/35)).

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
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field
and whose type $`G` is a vector space over $`F`, let $`\mu \in \mathrm{Msg}`, let
$`h \in \{0, 1\}`, and let $`\mathrm{cr} = (K_0, \tau^*, (\tau_1, \dots, \tau_n))` be a
challenge result of $`\Pi_B(P, \mu, h)`. We define the list $`\mathrm{Bun}_T(\mathrm{cr})` of
the _bundles of $`T`_ to be the list of those $`\mathrm{bun}(\tau_i)` that differ from
$`\ast`, in the order of $`i`.
:::
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.challengeBundle -docstrings -comments
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field
and whose type $`G` is a vector space over $`F`, let $`\mu \in \mathrm{Msg}`, let
$`h \in \{0, 1\}`, and let $`\mathrm{cr} = (K_0, \tau^*, (\tau_1, \dots, \tau_n))` be a
challenge result of $`\Pi_B(P, \mu, h)`. We define the _bundle of $`U`_ to be
$`\mathrm{Bun}_U(\mathrm{cr}) := \mathrm{bun}(\tau^*)`, which is $`\ast` if the challenge
session has accepted no bundle.
:::
::::

::::definition "pqxdh_honest_bundle" (lean := "Protocols.Models.PQXDH.honestBundle") (uses := "pqxdh_bundles, pqxdh_prekey_bundle, pqxdh_recipient_identity")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.honestBundle -docstrings -comments
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field
and whose type $`G` is a vector space over $`F`, let $`\mu \in \mathrm{Msg}`, let
$`h \in \{0, 1\}`, let $`\mathrm{tk}` be the long-term state of Bob, with signed prekey
$`\mathrm{SPK}_B`, let $`\mathrm{cr}` be a challenge result of $`\Pi_B(P, \mu, h)`, and let
$$`\begin{aligned}\beta = (&\mathrm{IK}, (\mathrm{SPK}, i_{\mathrm{SPK}}), \sigma_{\mathrm{SPK}},\\ &(\mathrm{PQPK}, i_{\mathrm{PQPK}}), \sigma_{\mathrm{PQPK}}, o)\end{aligned}`
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
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field
and whose type $`G` is a vector space over $`F`, let $`\mu \in \mathrm{Msg}`, let
$`h \in \{0, 1\}`, and let $`\mathrm{cr} = (K_0, \tau^*, (\tau_1, \dots, \tau_n))` be a
challenge result of $`\Pi_B(P, \mu, h)`. We say that the _KEM-key event_
$`\mathrm{Guess}(\mathrm{cr})` holds if one of the following holds.

1. Two bundles in $`\mathrm{Bun}_T(\mathrm{cr})` have the same KEM public key.
2. The bundle $`\mathrm{Bun}_U(\mathrm{cr})` and $`\mathrm{bun}(\tau_i)` have the same KEM
   public key for some $`i`, and $`\mathrm{start}(\tau^*)` and $`\mathrm{start}(\tau_i)` both
   differ from $`\ast` and $`\mathrm{start}(\tau^*) < \mathrm{start}(\tau_i)`.
:::
::::

The first case is a collision of the KEM keys that sessions of $`T` draw. In the second case,
the challenge session accepted a bundle before a session of $`T` carrying the same KEM key was
opened, so the adversary predicted a key that was not yet drawn. No assumption on a primitive
excludes the event, and hop 4 below bounds its probability by the bound on the KEM public keys.
In the transcript-matching experiment of chapter 2, a KEM with colliding or predictable public
keys breaks UAKE security. A second session that holds the same KEM key, and the same one-time
prekey when one is in use, accepts a replay of the initial message of the challenge session and
derives the same session key. The adversary can reveal that key without matching the challenge
transcript. In the partnered experiment over original-key partnering, a session of $`T` that
holds the associated data and the key material of the challenge session is its partner,
whatever its transcript and the time at which it accepted, so revealing it makes the experiment
output a uniform bit.

::::definition "pqxdh_challenge_partnered" (lean := "Protocols.Models.PQXDH.challengePartnered") (uses := "pqxdh_challenge_result, pqxdh_original_key_partnering, uake_partnered_exp")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.challengePartnered -docstrings -comments
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field
and whose type $`G` is a vector space over $`F`, let $`\mu \in \mathrm{Msg}`, let
$`h \in \{0, 1\}`, let $`\mathrm{cr} = (K_0, \tau^*, (\tau_1, \dots, \tau_n))` be a challenge
result of $`\Pi_B(P, \mu, h)`, and let $`e` be a state of the oracles, with a state $`s^*` of
the challenge session and a list of sessions with $`T`. We say that the challenge is
_partnered_, $`\mathrm{Partnered}(\mathrm{cr}, e)`, if $`s^*` has an authentication partner
under $`\pi_{\mathrm{ok}}` among the sessions with $`T` of $`e`, with $`\tau^*` as its
transcript.
:::
::::

So the challenge is partnered when a session of Bob has a key, holds the associated data and
the key material of Alice, and accepted no later than she did.

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
result $`\mathrm{cr}` of this step, with the state of $`\mathcal{A}`, the state $`e` of the
oracles, which holds the challenge session and the sessions of $`T`, and $`\mathrm{tk}`.
:::
::::

The challenge bit of the experiment of chapter 2 does not enter the challenge phase. The
experiments below draw it where they need it. This is the first part of
$`\mathsf{Exp}(\mathcal{A})` up to the order of independent draws.

::::definition "pqxdh_forge" (lean := "Protocols.Models.PQXDH.forgeExp, Protocols.Models.PQXDH.forgeProb") (uses := "pqxdh_challenge_phase, pqxdh_challenge_partnered")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.forgeExp -docstrings -comments
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field
and whose type $`G` is a vector space over $`F`, let $`\mu \in \mathrm{Msg}`, let
$`h \in \{0, 1\}`, and let $`\mathcal{A}` be an adversary against $`\Pi_B(P, \mu, h)`. We
define the _forgery experiment_ $`\mathrm{Forge}(\mathcal{A})` to be the following
computation with output in $`\{0, 1\}`. Run $`\mathrm{Chal}(\mathcal{A})` to get
$`\mathrm{cr} = (K_0, \tau^*, (\tau_1, \dots, \tau_n))` and the state $`e` of the oracles, and
output $`1` if $`K_0 \neq \bot` and $`\mathrm{Partnered}(\mathrm{cr}, e)` does not hold, and
$`0` otherwise.
:::
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.forgeProb -docstrings -comments
We write $`\mathrm{forge}(\mathcal{A}) := \Pr[\mathrm{Forge}(\mathcal{A}) = 1]` as a real
number.
:::
::::

In a forgery, the challenge session has completed, and no session of $`T` that accepted no
later than Alice holds her associated data and key material. This is the run on which the
partnered experiment outputs $`1` in its step 4.

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

::::definition "pqxdh_forge_honest_good" (lean := "Protocols.Models.PQXDH.forgeHonestGoodExp, Protocols.Models.PQXDH.forgeHonestGoodProb") (uses := "pqxdh_challenge_phase, pqxdh_honest_bundle, pqxdh_pqpk_guessed, pqxdh_challenge_partnered")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.forgeHonestGoodExp -docstrings -comments
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field
and whose type $`G` is a vector space over $`F`, let $`\mu \in \mathrm{Msg}`, let
$`h \in \{0, 1\}`, and let $`\mathcal{A}` be an adversary against $`\Pi_B(P, \mu, h)`. We
define the _residual forgery experiment_ $`\mathrm{Good}(\mathcal{A})` to be the following
computation with output in $`\{0, 1\}`. Run $`\mathrm{Chal}(\mathcal{A})` to get
$`\mathrm{cr} = (K_0, \tau^*, (\tau_1, \dots, \tau_n))`, the state $`e` of the oracles and the
long-term state $`\mathrm{tk}` of Bob. Output $`1` if $`K_0 \neq \bot`,
$`\mathrm{Partnered}(\mathrm{cr}, e)` does not hold, the bundle
$`\mathrm{Bun}_U(\mathrm{cr})` is $`\ast` or honest for $`\mathrm{tk}` and $`\mathrm{cr}`,
and $`\mathrm{Guess}(\mathrm{cr})` does not hold. Otherwise output $`0`.
:::
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.forgeHonestGoodProb -docstrings -comments
We write $`\mathrm{good}(\mathcal{A}) := \Pr[\mathrm{Good}(\mathcal{A}) = 1]` as a real
number.
:::
::::

::::definition "pqxdh_indist" (lean := "Protocols.Models.PQXDH.indistExp, Protocols.Models.PQXDH.indistAdvantage") (uses := "pqxdh_challenge_phase, uake_partnered_exp, pqxdh_original_key_partnering, pqxdh_challenge_partnered")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.indistExp -docstrings -comments
Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a finite field,
whose type $`G` is a vector space over $`F`, and whose type $`K` is finite and nonempty, let
$`\mu \in \mathrm{Msg}`, let $`h \in \{0, 1\}`, and let $`\mathcal{A}` be an adversary against
$`\Pi_B(P, \mu, h)`. We define the _coin-flipped experiment_ $`\mathrm{Ind}(\mathcal{A})` to
be the following computation with output in $`\{0, 1\}`. Run $`\mathrm{Setup}_P(\mu)` to get
$`(\mathrm{uk}, \mathrm{tk})`, draw a uniform bit $`b`, and run step 2 of
$`\mathsf{Exp}(\mathcal{A})` with these keys, to get
$`\mathrm{cr} = (K_0, \tau^*, (\tau_1, \dots, \tau_n))`, the state of $`\mathcal{A}` and the
state $`e` of the oracles. Then do the following.

1. If $`K_0 = \bot`, run steps 6 and 7 of the partnered experiment
   $`\mathsf{Exp}_{\pi_{\mathrm{ok}}}(\mathcal{A})` with $`K_b = \bot`, and output the result.
2. Otherwise, if $`\mathrm{Partnered}(\mathrm{cr}, e)` does not hold, output a uniform bit.
3. Otherwise, draw $`K_1` uniformly from $`K`, run steps 6 and 7 of
   $`\mathsf{Exp}_{\pi_{\mathrm{ok}}}(\mathcal{A})` with this $`K_1` and the bit $`b`, and
   output the result.
:::
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.indistAdvantage -docstrings -comments
We write
$`\mathrm{ind}(\mathcal{A}) := \big|\Pr[\mathrm{Ind}(\mathcal{A}) = 1] - \tfrac{1}{2}\big|` as a
real number.
:::
::::

The experiment is $`\mathsf{Exp}_{\pi_{\mathrm{ok}}}(\mathcal{A})` with one change: where
$`\mathsf{Exp}_{\pi_{\mathrm{ok}}}(\mathcal{A})` outputs $`1` because the challenge session
accepted with no authentication partner, this experiment outputs a uniform bit.

## The six hops

Hops 1 and 2 use no hypothesis on the primitives. Hop 3 uses the joint unforgeability of the
identity signature scheme, and hop 4 uses the bound on the KEM public keys. Hops 5 and 6 use
the remaining hypotheses of the theorems, and hop 6 also uses the bound on the KEM public
keys.

::::theorem "pqxdh_hop1" (lean := "Protocols.Models.PQXDH.advantage_le_forgeProb_add_indistAdvantage") (uses := "pqxdh_forge, pqxdh_indist, uake_partnered_exp, pqxdh_original_key_partnering")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.advantage_le_forgeProb_add_indistAdvantage (part := "signature") -docstrings -comments
*Hop 1.* Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a
finite field, whose type $`G` is a vector space over $`F`, and whose type $`K` is finite and
nonempty, let $`\mu \in \mathrm{Msg}`, let $`h \in \{0, 1\}`, let $`R` be the runtime of
probabilistic computations, and let $`\mathcal{A}` be an adversary against
$`\Pi_B(P, \mu, h)`. Then
$$`\mathrm{Adv}_{R,\pi_{\mathrm{ok}}}(\mathcal{A}) \le \mathrm{forge}(\mathcal{A}) + \mathrm{ind}(\mathcal{A}).`
:::
::::

::::theorem "pqxdh_hop2" (lean := "Protocols.Models.PQXDH.forgeProb_le_sigForge_add_pqpkGuessed_add_forgeHonestGood") (uses := "pqxdh_forge, pqxdh_sig_forge, pqxdh_guess, pqxdh_forge_honest_good")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.forgeProb_le_sigForge_add_pqpkGuessed_add_forgeHonestGood (part := "signature") -docstrings -comments
*Hop 2.* Let $`P` be a set of PQXDH parameters with generator $`g`, whose type $`F` is a
finite field and whose type $`G` is a vector space over $`F`, let $`\mu \in \mathrm{Msg}`, let
$`h \in \{0, 1\}`, and let $`\mathcal{A}` be an adversary against $`\Pi_B(P, \mu, h)`. Then
$$`\begin{aligned}\mathrm{forge}(\mathcal{A}) \le{}& \mathrm{sigForge}(\mathcal{A}) + \mathrm{guess}(\mathcal{A})\\ &+ \mathrm{good}(\mathcal{A}).\end{aligned}`
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
$$`\begin{aligned}\mathrm{bun}(\tau) = (&\mathrm{IK}, (\mathrm{SPK}, i_{\mathrm{SPK}}), \sigma_{\mathrm{SPK}},\\ &(\mathrm{PQPK}, i_{\mathrm{PQPK}}), \sigma_{\mathrm{PQPK}}, o).\end{aligned}`
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
$`\mathrm{Verify}(X, \nu, \sigma) = \mathrm{pure}(b)`, the computation that returns $`b`. Then
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
$`b` such that $`\mathrm{Verify}(X, \nu, \sigma) = \mathrm{pure}(b)`, the computation that returns
$`b`. Suppose also that every
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

The remaining four hops are admitted.

::::theorem "pqxdh_hop5_dh" (lean := "Protocols.Models.PQXDH.forgeHonestGoodProb_le_gap") (uses := "pqxdh_forge_honest_good, pqxdh_opens_at_most, pqxdh_kdf_prf_dh, dh_gap_advantage, aead_int_ctxt_d_advantage, prf_advantage")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.forgeHonestGoodProb_le_gap -docstrings -comments
*Hop 5, Diffie-Hellman case.* Let $`P` be a set of PQXDH parameters with generator $`g`,
whose type $`F` is a finite field, whose type $`G` is a vector space over $`F`, and whose
type $`K` is finite and nonempty. Let $`\mu \in \mathrm{Msg}`, let $`h \in \{0, 1\}`, let
$`q \in \mathbb{N}`, let $`\varepsilon_{\mathrm{gap}}`, $`\varepsilon_{\mathrm{aead}}` and
$`\varepsilon_{\mathrm{kdf}}` be real numbers, and let $`\mathcal{A}` be an adversary against
$`\Pi_B(P, \mu, h)` that opens at most $`q` sessions. Suppose that every Gap-DH adversary has
advantage at most $`\varepsilon_{\mathrm{gap}}`, that every INT-CTXT-D adversary against the AEAD scheme has
advantage at most $`\varepsilon_{\mathrm{aead}}`, and that every PRF adversary against
$`\mathrm{KDF}_{\mathrm{DH}}(P)` has advantage at most $`\varepsilon_{\mathrm{kdf}}`. Then
$$`\mathrm{good}(\mathcal{A}) \le q\,(\varepsilon_{\mathrm{gap}} + 2\varepsilon_{\mathrm{aead}} + \varepsilon_{\mathrm{kdf}}).`
:::
::::

The statement is admitted, and VersoBlueprint marks it as containing `sorry`. For $`q = 0` the
bounds of hops 4, 5 and 6 are $`0`, and each theorem bounds the advantage by
$`\varepsilon_{\mathrm{sig}}`.

::::theorem "pqxdh_hop6_dh" (lean := "Protocols.Models.PQXDH.indistAdvantage_le_gap") (uses := "pqxdh_indist, pqxdh_opens_at_most, pqxdh_kdf_prf_dh, dh_gap_advantage, aead_int_ctxt_d_advantage, prf_advantage")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.indistAdvantage_le_gap -docstrings -comments
*Hop 6, Diffie-Hellman case.* Let $`P` be a set of PQXDH parameters with generator $`g`,
whose type $`F` is a finite field, whose type $`G` is a vector space over $`F`, and whose
type $`K` is finite and nonempty. Let $`\mu \in \mathrm{Msg}`, let $`h \in \{0, 1\}`, let
$`q \in \mathbb{N}`, let $`\varepsilon_{\mathrm{gap}}`, $`\varepsilon_{\mathrm{aead}}`,
$`\varepsilon_{\mathrm{kdf}}` and $`\varepsilon_{\mathrm{pk}}` be real numbers, and let
$`\mathcal{A}` be an adversary against $`\Pi_B(P, \mu, h)` that opens at most $`q` sessions.
Suppose that every Gap-DH adversary has advantage at most $`\varepsilon_{\mathrm{gap}}`, that
every INT-CTXT-D adversary against the AEAD scheme has advantage at most $`\varepsilon_{\mathrm{aead}}`, that every PRF adversary
against $`\mathrm{KDF}_{\mathrm{DH}}(P)` has advantage at most
$`\varepsilon_{\mathrm{kdf}}`, and that for every $`Y \in \mathrm{PQPK}` the probability that
$`\mathrm{KeyGen}_\Lambda` outputs a public key equal to $`Y` is at most
$`\varepsilon_{\mathrm{pk}}`. Then
$$`\begin{aligned}\mathrm{ind}(\mathcal{A}) \le{}& q\,(\varepsilon_{\mathrm{gap}} + \varepsilon_{\mathrm{aead}} + \varepsilon_{\mathrm{kdf}})\\ &+ 2q^2\,\varepsilon_{\mathrm{pk}}.\end{aligned}`
:::
::::

The statement is admitted.

::::theorem "pqxdh_hop5_pq" (lean := "Protocols.Models.PQXDH.forgeHonestGoodProb_le_pq") (uses := "pqxdh_forge_honest_good, pqxdh_opens_at_most, pqxdh_kdf_prf, kem_perfectly_correct, kem_ind_cca_advantage, aead_int_ctxt_d_advantage, prf_advantage")
:::LibsignalVerifyBlueprint.pair Protocols.Models.PQXDH.forgeHonestGoodProb_le_pq -docstrings -comments
*Hop 5, post-quantum case.* Let $`P` be a set of PQXDH parameters with generator $`g`,
whose type $`F` is a finite field, whose type $`G` is a vector space over $`F`, and whose
types $`K` and $`\mathrm{SS}` are finite and nonempty. Let $`\mu \in \mathrm{Msg}`, let
$`h \in \{0, 1\}`, let $`q \in \mathbb{N}`, let $`\varepsilon_{\mathrm{kem}}`,
$`\varepsilon_{\mathrm{aead}}` and $`\varepsilon_{\mathrm{kdf}}` be real numbers, and let
$`\mathcal{A}` be an adversary against $`\Pi_B(P, \mu, h)` that opens at most $`q` sessions.
Suppose that $`\Lambda` is perfectly correct under the runtime of probabilistic computations,
that every IND-CCA adversary against $`\Lambda` has advantage at most
$`\varepsilon_{\mathrm{kem}}`, that every INT-CTXT-D
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
Suppose that $`\Lambda` is perfectly correct under the runtime of probabilistic computations,
that every IND-CCA adversary against $`\Lambda` has advantage at most
$`\varepsilon_{\mathrm{kem}}`, that every PRF adversary
against $`\mathrm{KDF}_{\mathrm{SS}}(P)` has advantage at most $`\varepsilon_{\mathrm{kdf}}`,
and that for every $`Y \in \mathrm{PQPK}` the probability that $`\mathrm{KeyGen}_\Lambda`
outputs a public key equal to $`Y` is at most $`\varepsilon_{\mathrm{pk}}`. Then
$$`\mathrm{ind}(\mathcal{A}) \le q\,(\varepsilon_{\mathrm{kem}} + \varepsilon_{\mathrm{kdf}}) + 2q^2\,\varepsilon_{\mathrm{pk}}.`
:::
::::

Both post-quantum hops are admitted. They assume that the KEM is perfectly correct, which is an
idealisation, as the section on modelling choices says. The post-quantum hop 6 has no
hypothesis on the AEAD scheme and no AEAD term.

## What the statements of hops 5 and 6 do not cover

The Lean module note of the security theorems states two limits of the statements.

Original-key partnering compares the associated data and the key material, and the key
derivation reads the key material only. A session of $`T` with the key material of the
challenge session and other associated data derives the same three keys as Alice. A session
with other key material holds her session key $`\mathrm{sk}`, or her key $`k_B`, when
$`\mathrm{KDF}` gives equal outputs in that component. Neither session is her partner.
Revealing a session that holds her $`\mathrm{sk}` returns her session key, and the experiment
draws no uniform bit for it. Confirm decrypts under her $`k_B` and her associated data. The
definitions do not exclude that she accepts a confirmation from such a session while no session
that accepted no later than she did is her partner, and the experiment then outputs $`1`. No
hypothesis of either theorem is about equal outputs of the key derivation. The PRF hypothesis
on $`\mathrm{KDF}_{\mathrm{DH}}(P)` is about one uniform key in the place of the third
Diffie-Hellman value, and the one on $`\mathrm{KDF}_{\mathrm{SS}}(P)` is about one uniform KEM
secret. Neither says anything about two inputs that differ in that place. The bounds have no
term of their own for these runs.

Accept computes the three keys before the AEAD decryption of the ciphertext of the initial
message, so a session of $`T` that rejects the ciphertext has still derived keys from its key
material. The AEAD scheme of chapter 2 has no laws. Nothing in the model says that a ciphertext
made under one key, or with other associated data, fails to decrypt under another key or other
associated data. Perfect correctness of the AEAD scheme concerns one key and one associated
data, and the security theorems do not assume it. Rejection under another key or other
associated data is only the security property INT-CTXT-D, which bounds it for one uniform key
and counts only the pairs that its encryption oracle did not output. INT-CTXT-D is a hypothesis
of hop 5 in both theorems and of hop 6 in the Diffie-Hellman theorem.

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
PRF. The module note of the two Diffie-Hellman hops 5 and 6 says that their proofs are deferred
to that change of the model
([issue #81](https://github.com/Beneficial-AI-Foundation/libsignal-verify/issues/81)). The
post-quantum hops are stated with the PRF as it stands.

## The signature and the KEM

The signature assumption is joint unforgeability. It does not ask for strong unforgeability,
which also counts a new signature on a message that was signed as a forgery. The Lean module
note says that XEdDSA lacks the strong notion, because its encoding of signatures is not
unique. The note adds that the argument for authentication needs only that no one signs a new
message without the key. The book has not checked this claim about XEdDSA.

The event $`\mathrm{SigForge}` therefore compares signed keys and not the bytes of signatures.
A new signature on a key that Bob signed is no forgery in hop 3. Such a run keeps the
associated data and the key material, so Alice keeps her original-key partner, and the run is
in no forgery event. It fails the match of transcripts of chapter 2
([issue #35](https://github.com/Beneficial-AI-Foundation/libsignal-verify/issues/35)).

The theorems assume that the verification algorithm is deterministic. This holds for signature
schemes in general, but the definition of VCV-io leaves verification probabilistic. So the
hypothesis closes a gap of the model.

The theorem for the post-quantum case assumes that the KEM is perfectly correct. The Lean
module note says that production Kyber decapsulates wrongly with a small probability, so this
is an idealisation.

The bound on the KEM public keys is the last hypothesis of both theorems. It bounds the
collisions and the predictions of KEM public keys across the sessions of $`T`. No assumption on
a primitive excludes them. The section on the structure of the proof shows, at the event
$`\mathrm{Guess}(\mathrm{cr})`, how they break UAKE security in the transcript-matching
experiment of chapter 2.

## Identifiers

The identifiers of the keys are not signed and not in the associated data of the model. KS
says that the identifiers are not security critical, because the key values are signed or in
the associated data (KS, Section 4.13, p. 17). Issue #35 shows that this breaks the match of
transcripts. The security theorems therefore use original-key partnering, which does not
compare the identifiers.

The security theorems make no assumption on $`\mathrm{id}_{\mathrm{KEM}}`. KS allows an
identifier with a smaller representation than the key, if collisions are unlikely (KS,
Section 4.13, p. 17). Such an identifier is not injective on all keys. In production the
identifiers are 32-bit prekey identifiers, and no map from the KEM public keys of 1568 bytes to
them is injective.

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
