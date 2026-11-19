# Contract reviews

The PQXDH statements of the Full realization rest on contracts: named hypotheses about opaque leaves of
the extraction. `Protocols/LEDGER.md` lists them. This file reviews the contracts that stay assumptions:
what each one states, which Rust code it stands for, why we believe it, what breaks if it is false, and
what would discharge it.

## Scope and conventions

The file covers:

- the contracts in `Protocols/PQXDH/Contracts.lean`, with their fault-or-value forms;
- `HkdfSha256Contract` in `rust/Libsignal/Proofs/Protocol/Crypto/HkdfSha256.lean`;
- `KyberBridge` in `Protocols/PQXDH/SecurityDefs.lean` and `KyberDeltaCorrect` in `Protocols/PQXDH/Kem.lean`;
- the opaque declarations of the extraction that the PQXDH statements reach. These are the non-logical
  axioms in the `#guard_msgs` checks of `rust/Libsignal/Specs/Protocol/Pqxdh.lean` and
  `rust/Libsignal/Specs/Protocol/Kem.lean` and `Protocols/Specs/PQXDH.lean`.

The fault-or-value form of a contract says only what a call returns when it returns: each `*Partial`
definition in `Protocols/PQXDH/Contracts.lean` assumes that the call equals `.ok r` and constrains `r`,
so it allows a panic or non-termination. The total form says that the call returns, and what it
returns, under its own premises. A fault-or-value form does not always follow from its total form
(finding 1).

Policies and modelling choices (`ECKeyPairValid`, `PQKeyPairShape`, `Adversary.SendsFittingMessages`,
`P.coins`, `P.ecKeygen`, `P.pqKeygen`, the synthetic AEAD wrapper) are not contracts. The ledger lists
them, and this file does not review them.

Each review separates two kinds of evidence. "Checked here" means that we read the code or did the
arithmetic for this review. "From the source" means that we take the claim from the cited code or
document without checking it again.

Rust crates are at the versions that `Cargo.lock` pins: `hkdf` 0.13.0, `hmac` 0.13.0, `libcrux-ml-kem`
0.0.10, `rand` 0.9.4, `rand_core` 0.9.5, `curve25519-dalek` 5.0.0 and `x25519-dalek` 3.0.0. A path in a
crate, such as `src/lib.rs`, is relative to that crate's root.

The committed `rust/` tree is upstream libsignal. The extraction runs on a copy with the patches of
`translation-patches/` applied. The Lean docstrings and the extracted `Source:` comments cite line
numbers in that patched copy. This file cites the committed tree unless it says "patched".

## Findings

1. **Two fault-or-value forms do not follow from their total forms.** The module docstring of
   `Protocols/PQXDH/Contracts.lean` says that the fault-or-value form of a contract follows from its
   total form. No Lean lemma proves this. For the first part of `SignaturePartial` and for the
   1568-byte branch of `KyberPartial` it cannot be derived in Lean: these parts quantify over every
   generator, while `SignTotal` and `KyberEncapsBackend` assume `RngTotal`, and the operations are
   opaque. Both parts are true
   of the Rust code, because array types fix the output sizes. They are therefore separate trusted
   claims, not consequences of the total forms. See sections 4 and 7.
2. **Kyber termination is a claim about SHAKE128 on every seed.** `KyberEncapsBackend` and
   `KyberDecaps` state termination for every key of the right length. libcrux samples the public matrix
   in a loop with no bound, and its seed comes from the key, which the adversary chooses. We know of no
   published proof that this loop ends on every seed. libcrux marks the sampling function
   `verification_status(lax)`. Section 4 gives a deterministic argument from the fact that
   Keccak-f[1600] is a permutation. It is a possible discharge route, not a proof: this review checked
   its steps only for libcrux's portable backend, and not that libcrux's permutation is Keccak-f[1600].
   The contracts still trust termination. See section 4.
3. **No published δ reaches `KyberDeltaCorrect` yet.** The published failure bound is for Kyber's own
   key generation and uniform coins. The contract bounds the failure mass over the ideal draws
   `P.pqKeygen` and `P.coins`, counting faults, protocol errors and mismatched secrets. Reusing a
   published δ needs a proof that this mass is at most δ, and no such proof is done. The contract does
   not need the draws to be production's (#75), nor termination on every key (section 4): only the
   failure mass on the ideal draws counts. See section 6.
4. **The HKDF contract describes a patched helper.** `crypto::hkdf_sha256` exists only in the patched
   copy. Its link to production is the two translation patches, which we checked. See section 1.
5. **Stale citation.** The docstring of `RngTotal` cites `rand_core` 0.9.3. `Cargo.lock` pins 0.9.5.
   The cited lines are the same in both versions.

## Summary

| Contract | Stands for | Discharge |
| --- | --- | --- |
| `HkdfSha256Contract` | `crypto::hkdf_sha256` (patched), `hkdf` 0.13.0 | a verified HMAC-SHA256 and HKDF, or an extraction of `hkdf`, `hmac` and `sha2` |
| `ToOwnedTotal` | `<str as ToOwned>::to_owned` | a model of `String` construction in the Aeneas standard library |
| `RngTotal` | the caller's generator; production passes `UnwrapErr<OsRng>` | #75; an OS entropy failure stays outside any proof |
| `KyberEncapsBadLength`, `KyberEncapsBackend`, `KyberDecaps` | `kyber1024::Parameters`, libcrux `kyber1024` | a model of libcrux; for termination, a bound in libcrux, an assumption on SHAKE128, or the permutation argument of section 4 once all its steps are checked |
| `KyberBridge` | libcrux Kyber-1024 as the abstract KEM of the PQ statement | a model of libcrux, with #75 for the coins |
| `KyberDeltaCorrect` | the decryption-failure probability of Kyber-1024 | a proof that the failure mass on the ideal draws is at most δ, from the published analysis and a model of libcrux |
| `AgreementDerived`, `AgreementTotal`, `TorsionFreeTotal`, `DerivedCanonical`, `SignTotal`, `SignVerify`, `VerifyTotal` | X25519 and XEdDSA in `rust/core/src/curve.rs` | #76, from the curve25519-dalek specifications |

## 1. `HkdfSha256Contract`

**Statement.** `HkdfSha256Contract H` in `rust/Libsignal/Proofs/Protocol/Crypto/HkdfSha256.lean`. For
every input key material `ikm`, every `info` and every 96-byte buffer `out`, the call
`crypto.hkdf_sha256 none ikm info out` returns `Ok(())` and a buffer of the same length. The buffer
holds `hkdfSha256Okm96 H none ikm info`: HKDF-Extract followed by HKDF-Expand (RFC 5869, Sections 2.2
and 2.3) for 96 bytes, computed from the MAC interface `H`. The contract does not say that `H` is
HMAC-SHA256.

**Stands for.** The helper `libsignal_protocol::crypto::hkdf_sha256` that
`translation-patches/protocol-crypto-hkdf_sha256.patch` adds. Its body is
`hkdf::Hkdf::<Sha256>::new(salt, input_key_material).expand(info, output)`. Production has no such
helper. Upstream `HandshakeKeys::derive_with_label` (`rust/protocol/src/pqxdh.rs`) makes the same
`Hkdf` call inside `libsignal_core::derive_arrays`.
`translation-patches/protocol-pqxdh-HandshakeKeys-derive_with_label.patch` replaces that call with the
helper on a 96-byte buffer, split into three 32-byte arrays.

**Checked here.**

- In `hkdf` 0.13.0, a missing salt becomes `Output::<H>::default()`, that is 32 zero bytes
  (`src/lib.rs:46-50`). This is RFC 5869's default salt and the Lean `hkdfDefaultSalt`.
- Extract is the HMAC of `ikm` under the salt (`src/lib.rs:53-64`, `:117-121`).
- `expand_multi_info` (`src/lib.rs:130-166`) computes `T(i) = HMAC(PRK, T(i-1) | info | i)` with a
  one-byte counter `i` from 1. This is `hkdfExpandBlock`. It returns an error only when the output is
  longer than 255 · 32 bytes, so 96 bytes give `Ok(())`. The loop runs three times.
- The three `expect` calls on this path cannot fail. HMAC accepts a key of any length
  (`src/hmac_impl.rs`), and the PRK has 32 bytes, at least `HashLen` (`src/lib.rs:60-64`, `from_prk`).
  The counter `u8::try_from(block_n).expect(..) + 1` (`src/lib.rs:155`) sees the block indices 0, 1
  and 2, so the conversion succeeds and the sum is at most 3.
- `derive_arrays` (`rust/core/src/lib.rs:40-66`) fills a `#[repr(C)]` struct of three `[u8; 32]`
  arrays and returns them in order. So the patched split `[..32]`, `[32..64]`, `[64..]` gives the same
  three arrays.

**From the source.** That `Hmac<Sha256>` from the `hmac` and `sha2` crates computes HMAC-SHA256
(FIPS 198-1 over FIPS 180-4).

**Gaps.** The contract describes the patched helper. Its link to production is the two patches, which
we read. `H` is a parameter: a theorem that assumes `HkdfSha256Contract H` holds for every `H` that the
helper matches, and the identification of `H` with HMAC-SHA256 is outside Lean. The contract covers
only the call that PQXDH makes: no salt and 96 bytes of output.

The contract allows `ikm` and `info` of any length, and the argument above bounds only the output.
HMAC's inner SHA-256 hash receives one 64-byte pad block before the message (`hmac` 0.13.0,
`src/block_api.rs:53-63`). `sha2` 0.11.0 computes the message length in bits as `8 * (…)` in `u64`
(`src/block_api.rs:66`), so the product overflows once a hash has received 2^61 bytes or more. The
workspace builds `sha2` without overflow checks in release (`Cargo.toml`,
`[profile.release.package.sha2]`), so the product wraps there, and a build with overflow checks
panics. With overflow checks, the contract is therefore stronger than the Rust code on inputs this
long. In the release profile the call returns, but SHA-256 (FIPS 180-4) is defined only for messages
shorter than 2^64 bits, so there the reading of `H` as HMAC-SHA256 fails. The PQXDH call is far below this limit: its input
key material has at most 192 bytes (`deriveKeysTotal` in `Protocols/PQXDH/Kdf.lean`), and its `info`
is the fixed label `WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024`.

**If false.** `derive_spec` and `derive_with_label_spec` take `HkdfSha256Contract H` as the hypothesis
`h_hkdf`. If the contract fails for HMAC-SHA256, this hypothesis fails for that `H`. The two theorems
then say nothing about production: neither that the derivation returns, nor that the root key, the
chain key and the pqr key are bytes 0 to 32, 32 to 64 and 64 to 96 of the HKDF output. The same
hypothesis fails in `deriveKeysTotal` and in every Full statement that takes the contract:
`coreCompletion_extracted`, `jointKeyAgreement_extracted`, both `wrapperAgreement_*`,
`fullExp_noLostMass` and the two `_total` corollaries. The security statements take the fault-or-value
form `HkdfSha256Partial` through `PartialContracts`. If the helper returns anything else (an error, another length or other bytes), that hypothesis
fails too, and the security statements say nothing about production's key derivation. If the helper
could fail, the `expect` in `derive_with_label` would panic.

**Discharge.** A verified HMAC-SHA256 and HKDF that the extraction can call, or an extraction of the
`hkdf`, `hmac` and `sha2` crates. `derive_spec` already proves the extracted key derivation from this
contract, so nothing else needs to change.

**Fault-or-value form.** `HkdfSha256Partial H`. It follows from the total form, on the same domain.

## 2. `ToOwnedTotal`

**Statement.** `ToOwnedTotal` in `Protocols/PQXDH/Contracts.lean`: for every `s : Str`, the call
`Str.Insts.AllocBorrowToOwnedString.to_owned s` returns some value. The contract says that the call
terminates without a panic. It says nothing about the returned string.

**Stands for.** `<str as ToOwned>::to_owned` from Rust's `alloc` library. `pqxdh_accept` calls it once,
to build the message `"incoming base key is invalid"` when the initiator's ephemeral key is not
canonical (`rust/protocol/src/pqxdh.rs:328-333`; patched 339-344).

**Checked here.** The call site, and that the string goes only into the error value
`SignalProtocolError::InvalidMessage`. The closure of `pqxdh_accept` contains no other axiom of the
string library.

**From the source.** `to_owned` copies the bytes of an existing `str` into a new `String`. Its only
failure is allocation failure. Then `handle_alloc_error` does not return normally. With `std`, the
default prints a message and aborts the process, and the global configuration can make it panic
instead (Rust 1.98.1, `library/alloc/src/alloc.rs:519-532`). Like the rest of the extraction, the
contract does not model running out of memory.

**Gaps.** The statement is for every `Str`, not only the literal. On every Rust `str` that exists in
memory, the Rust function behaves the same, so the contract matches it there. At the Aeneas pin, `Str`
is `Slice U8` with no UTF-8 invariant (`Aeneas/Std/StringDef.lean:8`), while a Rust `str` must be
valid UTF-8. So the contract also covers byte slices that no Rust `str` represents. The one call on
this path passes an ASCII literal, which is valid UTF-8.

**If false.** `pqxdh_accept` could fault on the rejection branch. Honest keys pass `is_canonical`
(`DerivedCanonical`), so honest runs do not take this branch. The adversary can send a non-canonical
key, so `fullExp_noLostMass` and the `_total` corollaries depend on the contract.

**Discharge.** None is available now. The Aeneas standard library has no way to build a `String` from
a `str`, and it does not model `String::from`, `to_string` or `format!` either. So no translation patch
can route the call through a modelled function. A model of `String` construction in the Aeneas library
would allow a body.

**Fault-or-value form.** None. `PartialContracts` does not include `ToOwnedTotal`.

## 3. `RngTotal`

**Statement.** `RngTotal core Dom` in `Protocols/PQXDH/Contracts.lean`. Here `core` is a
`rand_core_1.RngCore R` instance, the generator's methods on states of type `R`. `Dom : R → Prop` is
the set of states on which the contract holds. On every state in `Dom`, the
methods `next_u32`, `next_u64` and `fill_bytes` terminate without a panic and return a state in `Dom`.
`fill_bytes` also keeps the length of the buffer.

**Stands for.** The caller's generator. `RngTotal` is a hypothesis on the `rand_core_1.RngCore`
instance over which the statements quantify. It is not about an opaque declaration. libsignal's
language bridge passes `rand::rngs::OsRng.unwrap_err()` to `process_prekey_bundle`
(`rust/bridge/shared/src/protocol.rs:1011`). This is `UnwrapErr<OsRng>` from `rand_core` 0.9.5.

**Checked here.** Each method of `UnwrapErr` calls the `try_` method of the inner generator and unwraps
it (`rand_core` 0.9.5, `src/lib.rs:300-315`). So `UnwrapErr<OsRng>` panics exactly when the operating
system's entropy source returns an error. `fill_bytes` writes into the caller's slice in place, and a
Rust slice cannot change its length, so the length condition holds.

**Gaps.** For production, totality rests on two properties of the OS entropy source: each request
returns no error, and each request returns at all. `OsRng` documents that its first call may block
until the system's RNG is initialised (`rand_core` 0.9.5, `src/os.rs:24-34`). Both properties are
outside any proof. The extraction declares the methods of `UnwrapErr` as axioms
(`rand_core_1.UnwrapErr.Insts.Rand_core_1RngCore.*`), but no statement uses that instance. The
statements hold for every generator that satisfies `RngTotal`.

**If false.** Signing and Kyber encapsulation could fault, because `SignTotal` and
`KyberEncapsBackend` take `RngTotal` as a premise. The completion and agreement statements and
`fullExp_noLostMass` depend on it. The two fault-counting security statements,
`uakeInitiator_secure_dh` and `uakeInitiator_secure_pq`, do not take it: they count faults in `Pr[⊥]`.
The two `_total` corollaries take `RngTotal` for both views of the generator, on a domain that
contains the states from `P.coins` (`Protocols/PQXDH/Security.lean`), so they depend on it.

**Discharge.** #75 (step 3) decides whether the per-session draw `P.coins` needs a correspondence with
production's generator. For a deterministic generator, such as the
ChaCha generator of the tests, `RngTotal` could be proved from a body.

## 4. Kyber1024 backend: `KyberEncapsBadLength`, `KyberEncapsBackend`, `KyberDecaps`

**Statements.** All three are in `Protocols/PQXDH/Contracts.lean`.

- `KyberEncapsBadLength`: on a public key that does not have 1568 bytes, encapsulation returns
  `BadKEMKeyLength` and leaves the generator state unchanged.
- `KyberEncapsBackend`: when the generator is total on `Dom` and the state is in `Dom`, encapsulation
  on a 1568-byte key terminates without a panic. It returns a 32-byte secret, a 1568-byte ciphertext
  and a state in `Dom`.
- `KyberDecaps`: on every secret key and ciphertext, decapsulation terminates without a panic. It
  returns `BadKeyLength` if the key does not have 3168 bytes, else `BadCiphertext` if the ciphertext
  does not have 1568 bytes, else a 32-byte secret.

**Stands for.** `encapsulate` and `decapsulate` of `kyber1024::Parameters`
(`rust/protocol/src/kem/kyber1024.rs:31-54`). They call `libcrux_ml_kem::kyber1024::{encapsulate,
decapsulate}` from `libcrux-ml-kem` 0.0.10. That module is "Kyber 1024 (NIST PQC Round 3)"
(`src/lib.rs:104-114`): the pre-standard Kyber, not ML-KEM.

**Checked here.**

- libsignal converts its byte slices with `MlKem1024PublicKey::try_from`,
  `MlKem1024PrivateKey::try_from` and `MlKem1024Ciphertext::try_from`. Each succeeds exactly when the
  slice has the array's length (`src/types.rs:45-54`).
- The lengths follow from the constants of `src/mlkem1024.rs:1-19` (rank 4, compression 11 and 5)
  and `src/constants.rs` (256 coefficients of 12 bits, a 32-byte digest). The public key has 4 · 384 + 32 = 1568 bytes, the secret key
  1536 + 1568 + 32 + 32 = 3168 bytes and the ciphertext 4 · 352 + 160 = 1568 bytes. The shared secret
  has 32 bytes (`src/constants.rs:14`).
- Encapsulation converts the key before `csprng.random()`, so a bad length leaves the state unchanged.
  Decapsulation checks the key before the ciphertext, in the order of `KyberDecaps`.
- Array types fix the sizes of the outputs.

**From the source.**

- Termination. libcrux samples the public matrix in `sample_from_xof` (`src/sampling.rs:75-105`). After
  three SHAKE128 blocks it squeezes further blocks in `while !done` with no bound (`:95-102`). The loop
  ends once every entry has 256 coefficients below q. Its seed comes from the public key, and
  decapsulation samples the same matrix when it re-encrypts. The source comment cites ePrint 2023/708
  for the claim that more than five blocks are rarely needed.
- Panic freedom of libcrux's arithmetic. libcrux carries hax and F* annotations, but `sample_from_xof`
  is marked `verification_status(lax)` (`src/sampling.rs:74`).
- On a 1568-byte ciphertext that does not match the key, Kyber returns a pseudorandom secret, not an
  error (implicit rejection). `KyberDecaps` claims only that some 32-byte secret is returned.

**Gaps.** Termination on every key is a claim about SHAKE128 on every seed, and the adversary chooses
the seed. Under a random-oracle view of SHAKE128 the loop ends with probability 1. For a fixed seed,
we know of no published proof. The route below may give one, but this review did not check all its
steps. libsignal does not call libcrux's `validate_public_key`, so encapsulation accepts any 1568
bytes. The contract matches this.

**A possible discharge route for termination (not fully checked).** For a fixed seed, the sampling
loop may end for a deterministic reason. We checked the first three steps below in `libcrux-sha3`
0.0.10 and in the portable backend of `libcrux-ml-kem` 0.0.10, both pinned in `Cargo.lock`.

1. Each matrix entry absorbs a 34-byte seed into a zero state with rate 168 bytes
   (`libcrux-ml-kem` `src/hash_functions.rs:133-172`; `libcrux-sha3`
   `src/portable/incremental.rs:246-290`, `src/generic_keccak.rs:44-48`). Padding
   writes the delimiter at byte 34 and `0x80` at byte 167 (`src/simd/portable.rs:91-106`). So the
   state `S` before the first permutation has zero bytes at offsets 36, 37 and 38.
2. `absorb_final` applies the permutation `f` after padding (`src/generic_keccak.rs:282-298`). The
   first three blocks are the rate parts of `f(S)`, `f²(S)` and `f³(S)`, and each later block applies
   `f` once more (`src/generic_keccak/portable.rs:14-43`). Load and squeeze use the same
   little-endian lane order (`src/simd/portable.rs:56-83`, `:115-140`). So block `k` is the first 168
   bytes of `fᵏ(S)`.
3. The sampler reads each block in 24-byte chunks and each chunk in 3-byte groups
   (`libcrux-ml-kem` `src/sampling.rs:45-71`, `src/vector/portable/sampling.rs:8-32`). 168 is a
   multiple of 24, so the group at bytes 36 to 38 of a block is aligned. A zero group gives two
   values 0 < q, and the sampler accepts both while the entry is not yet full. The count of accepted
   coefficients never decreases.
4. Not checked: that libcrux's `keccakf1600` is a permutation of the 1600-bit state, for example
   because it computes Keccak-f[1600]. If it is, `S` lies on a cycle of `f`, so `fᵖ(S) = S` for some
   `p ≥ 1`. Then blocks `p`, `2p`, … contain the zero group, and each entry fills after at most 128
   such blocks.
5. Not checked: the neon and avx2 backends, which libcrux can use in place of the portable one, and
   the path by which decapsulation reaches the sampler.

The argument gives no useful time bound, because `p` can be as large as 2^1600.

**If false.** Alice's encapsulation or Bob's decapsulation could fault on honest runs. All completion
and agreement statements and `fullExp_noLostMass` depend on these contracts. The security statements
use the fault-or-value form `KyberPartial`, which claims no termination.

**Discharge.** A model of libcrux's Kyber-1024. Termination needs a bound on the sampling loop in
libcrux, an explicit assumption on SHAKE128, or the route above once all its steps are checked for
every backend.

**Fault-or-value form.** `KyberPartial`. Its decapsulation part and its bad-length part follow from
`KyberDecaps` and `KyberEncapsBadLength`. Its 1568-byte encapsulation part says, for every generator,
that a returning call gives a 32-byte secret and a 1568-byte ciphertext. `KyberEncapsBackend` gives
this only for generators that satisfy `RngTotal`. So this part is a separate claim. It holds for the
Rust code, because array types fix both sizes.

## 5. `KyberBridge`

**Statement.** `KyberBridge P K` in `Protocols/PQXDH/SecurityDefs.lean`. For an abstract KEM `K`:

- `P.pqKeygen` is `K`'s key generation.
- `K`'s encapsulation is a function `encDet` of the public key and of a generator state from
  `P.coins`; its decapsulation is a function `decDet`.
- When the extracted encapsulation returns on a 1568-byte key, it returns `encDet`'s output.
- When the extracted decapsulation returns on a secret key from `P.pqKeygen`, it returns `decDet`'s
  key, or an error where `decDet` gives no key.
- The bridge claims no termination.

**Stands for.** The claim that libcrux's Kyber-1024, with coins drawn from the caller's generator, is
the KEM whose IND-CCA security the PQ statement assumes.

**Checked here.** We read the statement and the two extracted wrappers it names in
`rust/Libsignal/Translated/Protocol/Funs.lean`: `kem.KeyPublic.encapsulate`, which also serializes the
ciphertext, and `kem.KeySecret.decapsulate`, which first deserializes the ciphertext and checks the
key type. The bridge's clauses on the extracted calls constrain only calls that return: encapsulation
on a 1568-byte public key, for every generator state, including states outside the support of
`P.coins`, and decapsulation on secret keys from `P.pqKeygen`. Its clauses on `K` are three
equations: `P.pqKeygen` is `K`'s key generation, `K`'s encapsulation is `encDet` applied to a state
from `P.coins`, and `K`'s decapsulation is `decDet`. Given `KyberPartial`, a returning encapsulation on
a 1568-byte key gives a 32-byte secret, and a returning decapsulation gives an error or a 32-byte
secret. A Lean function is deterministic, so one can then define `encDet` and `decDet` from the
extracted calls, and a `K` from them, so that the bridge holds by construction. This construction
needs arbitrary defaults in three cases: a call that faults, a public key of another length, and a
secret key outside the support of `P.pqKeygen`. Two such `K` can agree on every call that returns and
differ on these inputs, and the IND-CCA premise is about the chosen `K`, defaults included. For a `K`
given in advance the bridge is not automatic: its three equations and its two clauses on returning
calls must be checked. We did not write this construction in Lean.

**Gaps.** IND-CCA of Kyber-1024 is a hardness assumption, out of scope for the correctness work (#72).
libsignal draws the 32 encapsulation bytes with `csprng.random()`. The premise is the standard Kyber
assumption only if these bytes are uniform when the state comes from `P.coins`. #75 includes the
`P.coins` draw (its step 3). Two more
differences separate the Lean premise from the usual computational assumption. The premise `hkem` of
`uakeInitiator_secure_pq` bounds the advantage of every `K.IND_CCA_Adversary`, with no resource bound
(#41; see the limits in the module docstring of `Protocols/PQXDH/Security.lean`). And `K`'s key
generation is the law of `P.pqKeygen`, so the premise is about Kyber's own key generation only if
`P.pqKeygen` draws keys as Kyber does. #75 lists `P.pqKeygen` among the ideal draws that nothing
relates yet, but none of its proposed steps relates it to Kyber's key generation.

**If false.** `uakeInitiator_secure_pq` and `uakeInitiator_secure_pq_total` take `KyberBridge P K` as a
hypothesis, next to the IND-CCA premise on `K`. If the bridge fails for a `K`, the statements say
nothing for that `K`, so its IND-CCA premise gives no bound on the extracted Kyber.

**Discharge.** A model of libcrux's Kyber-1024, with #75 for the coins.

## 6. `KyberDeltaCorrect`

**Statement.** `KyberDeltaCorrect P δ` in `Protocols/PQXDH/Kem.lean`: the correctness error of
`kyberKem P` under `rustRuntime` is at most `δ`. This is the probability, over a key pair from
`P.pqKeygen` and a state from `P.coins`, that encapsulation and decapsulation do not return the same
secret. Faults and protocol errors count as failures. `δ` stays symbolic.

**Stands for.** The decryption-failure probability of Kyber-1024 as libcrux implements it.

**Why believed.** In this paragraph, three facts about libcrux's `kyber1024` are checked here: its
round-3 label (`src/lib.rs:104-114`), rank 4, and compression 11 and 5. The failure analysis is cited
from a specification that we did not read. The round-3 Kyber specification analyses the failure probability of Kyber-1024
(R. Avanzi et al., *CRYSTALS-Kyber: Algorithm Specifications and Supporting Documentation*, version
3.02, 2021). We did not read it for this review and give no value for δ here. libcrux's `kyber1024`
is round-3 Kyber with the Kyber-1024 parameters. We checked rank 4 and compression 11 and 5 in
`src/mlkem1024.rs`. So that analysis applies if libcrux implements the specification, which is a
question for libcrux (#72 puts it out of scope).

**Gaps.**

- The published bound is over Kyber's own key generation from uniform seeds and uniform 32-byte
  encapsulation coins. The contract is over `P.pqKeygen`, which only `PQKeyPairShape` constrains, and
  over the generator states of `P.coins`. Reusing a published δ needs a proof that the failure mass
  on these draws, counting faults, protocol errors and mismatched secrets, is at most δ. Such a proof
  would also need libcrux to implement the specification and the wrappers not to fault. It does not
  need the draws to be production's. #75 lists `P.pqKeygen` and `P.coins` among the ideal draws that
  nothing relates yet, but none of its proposed steps relates `P.pqKeygen` to Kyber's key generation.
  No route to the proof is done.
- The contract averages over key pairs and coins, as `KEMScheme.deltaCorrect` does. VCVio supplies the
  experiment `KEMScheme.correctnessExperiment`. This project defines `correctnessError` and
  `deltaCorrect` in `Protocols/ToVCVio/CryptoFoundations/KEMCorrectness.lean`, after secure-messaging.
  VCVio's own `deltaCorrect` is a different predicate, for public-key encryption. Fiedler and Günther
  phrase δ-correctness "for every key pair (pk, sk) ←$ KGen(), and every encapsulation
  (ct, ss) ←$ Enc(pk)" (*Security Analysis of Signal's PQXDH Handshake*, PKC 2025, Section 3). A
  reader who carries their δ_corr over should check that it is the same averaged quantity.
- Faults and protocol errors count as failures. The bound concerns only the faults, protocol errors
  and mismatches on the ideal draws, so termination on every key, as section 4 states it, is not
  necessary for it.

**If false.** `jointKeyAgreement_extracted` and both `wrapperAgreement_*` take `KyberDeltaCorrect P δ`
as a hypothesis and conclude that the two parties agree with probability at least `1 − δ`. If the
correctness error is above the chosen `δ`, the hypothesis fails, and these statements give no
agreement bound for that `δ`.

**Discharge.** A proof that the failure mass on the ideal draws is at most δ, from the published
analysis and a model of libcrux. #75 has no step yet for `P.pqKeygen`.

## 7. Curve25519 and XEdDSA contracts

All seven are in `Protocols/PQXDH/Contracts.lean`. #76 plans to discharge them from the
curve25519-dalek specifications. This review stands until then.

**Stands for.** `PrivateKey::public_key`, `calculate_agreement` and `calculate_signature` and
`PublicKey::is_torsion_free`, `is_canonical` and `verify_signature_for_multipart_message` in
`rust/core/src/curve.rs`, over `rust/core/src/curve/curve25519.rs`, `x25519-dalek` 3.0.0 and
`curve25519-dalek` 5.0.0.

| Contract | Statement | Checked here | From the source |
| --- | --- | --- | --- |
| `AgreementTotal` | agreement returns 32 bytes or `InvalidKeyAgreement` | `calculate_agreement` (`curve.rs:296-309`) runs X25519 and rejects only the all-zero value | assumed: X25519 itself does not panic |
| `AgreementDerived` | on keys with derived public halves, both agreements return the same 32 bytes | `public_key` (`curve.rs:259-267`) and agreement both use the clamped scalar (`curve25519.rs:170-174`); argument 1 below the table | both values are the u-coordinate of the product of the two clamped scalars with the base point, and that u-coordinate is 0 only for the identity and the point of order 2 |
| `TorsionFreeTotal` | the torsion check returns a Boolean | `is_torsion_free` (`curve.rs:165-174`) has no panic path of its own | assumed: `to_edwards` and `is_torsion_free` of curve25519-dalek do not panic |
| `DerivedCanonical` | a derived public key passes `is_canonical` | `is_canonical` is `is_torsion_free && scalar_is_in_range` (`curve.rs:165-190`) | a derived key lies in the prime-order subgroup, and its u-coordinate is encoded below `2^255 - 19` |
| `SignTotal` | when both views of the generator, `crng.RngCoreInst` and `rng.rand_core_1RngCoreInst`, are total on the same `Dom` and the starting state is in `Dom`, signing returns 64 bytes and a state in `Dom` | signing (`curve.rs:275-294`, `curve25519.rs:66-117`) draws 64 bytes with `fill_bytes` and always returns `Ok` of a 64-byte array | assumed: SHA-512 and scalar arithmetic do not panic |
| `SignVerify` | a signature by `sk` verifies under the public key derived from `sk` | argument 2 below the table | `to_edwards` on `A`'s u-coordinate and sign bit returns `A` |
| `VerifyTotal` | verification returns a Boolean | `verify_signature_for_multipart_message` (`curve.rs:138-151`) returns `false` on a wrong signature length and otherwise calls `verify_signature`. That function returns `false` on a failed `to_edwards` or when bit 253 or 254 of `s` is set (`curve25519.rs:125-139`), and otherwise compares the recomputed `R` with the signature bytes (`:142-158`). The libsignal code has no panic path of its own | assumed: curve25519-dalek's double-scalar multiplication does not panic |

**Checked here, argument 1 (`AgreementDerived`).** A clamped scalar is a multiple of 8 in
`[2^254, 2^255)`. If it were a multiple `kℓ` of the group order, then `k < 8`, and `8 ∣ kℓ` with `ℓ`
odd forces `8 ∣ k`, a contradiction.

**Checked here, argument 2 (`SignVerify`).** The signer uses `A = aB` with `a` the clamped scalar and
puts `A`'s sign bit in the top bit of the signature. `s = ha + r` is reduced, so `s < 2^253` and the
high-bit check passes (`curve25519.rs:119-159`). The verifier hashes `R`, the compressed `A` and the
message, the same inputs as the signer, so it gets the same `h` (`:101-108`, `:142-149`), given that
`to_edwards` returns `A` (last column of the table). It then computes `sB − hA` (`:151-155`;
`curve25519-dalek` 5.0.0 documents this function as computing `aA + bB`, `src/edwards.rs:1079`).
Since `A = aB` with `a` reduced modulo the order of `B`, `sB − hA = (ha + r)B − haB = rB`. The
compression of `rB` is the first 32 bytes of the signature (`:99`, `:112`), so the final comparison
succeeds (`:156-158`).

The cells marked "assumed" are not checked. The `curve25519-dalek` 5.0.0 doc comments that we read
(`src/montgomery.rs:227-239` for `to_edwards`, `src/edwards.rs:1079` for the double-scalar
multiplication) say what these functions compute but state no guarantee that they do not panic. We
did not look for such a guarantee for X25519 or SHA-512, and we did not read any of this code for
panics.

**Gaps.** The docstring of `VerifyTotal` also says that verification returns `false` on a malformed
signature or key. The statement does not include this: it states only that a Boolean is returned.

**If false.** The completion and agreement statements and `fullExp_noLostMass` take `CoreContracts`
and, for the wrapper, `SignatureContracts`. The security statements take the fault-or-value forms.

**Fault-or-value forms.** `AgreementPartial` and `DerivedCanonicalPartial` follow from the total forms.
The second part of `SignaturePartial` follows from `SignVerify`. The first part says, for every
generator, that a returning call gives a 64-byte signature. `SignTotal` gives this only for generators
that satisfy `RngTotal`, so this part is a separate claim. It holds for the Rust code, which returns a
64-byte array.

## 8. Opaque declarations reached by the PQXDH statements

The declarations below are all the axioms of the extraction that the frozen closures of
`pqxdh_initiate`, `pqxdh_accept` and the Full statements contain. A closure is frozen when a
`#guard_msgs` check on its `#print axioms` output fixes it, so that `lake build` fails when it
changes. The checks are those of the two spec summaries named under "Scope and conventions". No other
axiom of the extraction is reached. Besides these declarations, the closures contain `propext`,
`Classical.choice` and `Quot.sound`. Seven closures in `Protocols/Specs/PQXDH.lean` also contain
`sorryAx`: those of `uakeInitiator_secure_dh`, `uakeInitiator_secure_pq`, their two `_total`
corollaries, `fullExp_noLostMass` and both `wrapperAgreement_*`. This `sorryAx` comes
from the admitted statements that `Protocols/LEDGER.md` lists under "Security placeholders" and
"Temporary stubs", not from the extraction.

| Declaration | Covered by |
| --- | --- |
| `crypto.hkdf_sha256` | `HkdfSha256Contract` (section 1) |
| `Str.Insts.AllocBorrowToOwnedString.to_owned` | `ToOwnedTotal` (section 2) |
| `kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate` | `KyberEncapsBadLength`, `KyberEncapsBackend`, `KyberBridge`, `KyberDeltaCorrect` (sections 4 to 6) |
| `kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate` | `KyberDecaps`, `KyberBridge`, `KyberDeltaCorrect` (sections 4 to 6) |
| `curve.PrivateKey.calculate_agreement` | `AgreementDerived`, `AgreementTotal` (section 7) |
| `curve.PrivateKey.public_key` | `AgreementDerived`, `DerivedCanonical`, `SignVerify` (section 7); the policy `ECKeyPairValid` |
| `curve.PrivateKey.calculate_signature` | `SignTotal`, `SignVerify` (section 7) |
| `curve.PublicKey.is_torsion_free` | `TorsionFreeTotal`, and `DerivedCanonical` through `is_canonical` (section 7) |
| `curve.PublicKey.verify_signature_for_multipart_message` | `VerifyTotal`, and `SignVerify` through `verify_signature` (section 7) |
| `kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length`, `kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length` | none needed, see below |
| `core.num.niche_types.NonZeroU8Inner`, `core.num.nonzero.NonZero` | none needed, see below |

**Checked here.**

- The contracts constrain the same constants that the entry points call. The closures of
  `CoreContracts`, `SignatureContracts` and `PartialContracts` name the `curve.*` declarations of
  `rust/Libsignal/Translated/Core/FunsExternal.lean`. They do not name the `libsignal_core.curve.*`
  duplicates in `rust/Libsignal/Translated/Protocol/FunsExternal.lean`, which nothing on these paths
  reaches.
- The two `key_length` axioms enter the closures only as the field of the `KeyKind` instances
  (`rust/Libsignal/Translated/Protocol/Funs.lean`). On the PQXDH paths the instance is passed to
  `KeyMaterial`'s `deref`, which ignores it and returns the key bytes. No PQXDH path calls `key_length`.
- The two `NonZero` axioms are opaque types from Rust's `core`. They enter because variants of
  `SignalProtocolError` carry a `ProtocolAddress`, whose `DeviceId` holds a `NonZero<u8>`. An axiom of
  type `Type` claims only that a type exists.
