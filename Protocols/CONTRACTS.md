# Contract reviews

The PQXDH statements of the Full realization rest on contracts: named hypotheses about opaque leaves of
the extraction, or about extracted functions whose bodies call opaque leaves. `Protocols/LEDGER.md`
lists them. This file reviews the contracts that stay assumptions: what each one states, which Rust
code it stands for, why we believe it, what breaks if it is false, and what would discharge it. It
also reviews `GenerateTotal`, which is now proved from two of them (section 8), and
`HkdfSha256Contract`, which is now proved from `HkdfSha256RfcContract` (section 1).

## Scope and conventions

The file covers:

- the contracts in `Protocols/PQXDH/Contracts.lean`, with their fault-or-value forms where they exist;
- `HkdfSha256RfcContract` in `rust/Libsignal/Proofs/Protocol/Crypto/HkdfSha256.lean`, and
  `HkdfSha256Contract` in the same file, which is proved from it;
- `KyberBridge` in `Protocols/PQXDH/SecurityDefs.lean`, and `KyberDeltaCorrect` and
  `KyberDeltaCorrectAfterGenerate` in `Protocols/PQXDH/Kem.lean`;
- the opaque declarations of the extraction that the PQXDH statements reach. These are the axioms of
  the extraction among those that the `#guard_msgs` checks of `rust/Libsignal/Specs/Protocol/Pqxdh.lean`,
  `rust/Libsignal/Specs/Protocol/Kem.lean` and `Protocols/Specs/PQXDH.lean` print. The checks also
  print `propext`, `Classical.choice` and `Quot.sound`, and five checks in `Protocols/Specs/PQXDH.lean`
  print `sorryAx`. None of these comes from the extraction (section 9).

The fault-or-value form of a contract says only what a call returns when it returns: each `*Partial`
definition in `Protocols/PQXDH/Contracts.lean` assumes that the call equals `.ok r` and constrains `r`,
so it allows a panic or non-termination. The total form says that the call returns, and what it
returns, under its own premises. A fault-or-value form does not always follow from its total form
(finding 1). `ToOwnedTotal` and `GenerateTotal` have no fault-or-value form (finding 6).
`ClampIntegerContract` and `X25519SecretContract` are stated in one form. What each gives as a
fault-or-value form is in sections 10 and 11.

Policies and modelling choices (`ECKeyPairValid`, `PQKeyPairShape`, `Adversary.SendsFittingMessages`,
`P.coins`, `P.ecKeygen`, `P.pqKeygen`, the synthetic AEAD wrapper, the last-resort Kyber prekey,
`KyberPrekeyKind`) are not contracts, and neither are the limits of the model, such as the missing
corruption oracle. The ledger lists them, and this file does not review them.

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

1. **Two parts of the fault-or-value forms do not follow from the total forms.** The first part of
   `SignaturePartial` and the part of `KyberPartial` for encapsulation on a 1568-byte key cannot be
   derived in Lean from the total forms: these parts quantify over every generator, while
   `SignTotal` and `KyberEncapsBackend` assume `RngTotal`, and the operations are opaque. Both parts
   are true of the Rust code, because array types fix the output sizes. They are therefore separate
   trusted claims, not consequences of the total forms. Every other part of the fault-or-value forms
   follows from a total form. Lean proves this for HKDF (`hkdfSha256Partial_of_contract`). For the
   other contracts no Lean lemma states these implications: this review checked them against the
   definitions. See sections 1, 4 and 7.
2. **Kyber termination is a claim about SHAKE128 on every seed.** `KyberEncapsBackend` and
   `KyberDecaps` state termination for every key of the right length. libcrux samples the public matrix
   in a loop with no bound, and its seed comes from the key, which the adversary chooses. For Kyber as
   specified, Barbosa and Schwabe prove that matrix sampling ends on every seed; the only property of
   Keccak-f[1600] they use is that it is a permutation of the 1600-bit state (*Kyber terminates*, IACR
   ePrint 2023/708, Section 3). Their proof is about the algorithm, and we know of no proof for
   libcrux's code. libcrux marks the sampling function `verification_status(lax)`. Section 4 applies
   their argument to libcrux's code. It is a possible discharge route, not a proof: this review checked
   its steps only for libcrux's portable backend, and not that libcrux's permutation is Keccak-f[1600].
   The contracts still trust termination. See section 4.
3. **No published δ reaches `KyberDeltaCorrect` or `KyberDeltaCorrectAfterGenerate` yet.** The
   published failure bound is for Kyber's own key generation and uniform coins. `KyberDeltaCorrect`
   bounds the failure mass over the ideal draws `P.pqKeygen` and `P.coins`, counting faults, protocol
   errors and mismatched secrets. Reusing a published δ needs a proof that this mass is at most δ, and
   no such proof is done. The contract does not need the draws to be production's (#75), nor
   termination on every key (section 4): only the failure mass on the ideal draws counts.
   `KyberDeltaCorrectAfterGenerate` bounds the same mass with encapsulation on the state that Core's
   `generate` returns. No premise describes the law of that state, and this contract cannot be derived
   in Lean from `KyberDeltaCorrect`. See section 6.
4. **The HKDF contracts describe a patched helper.** `crypto::hkdf_sha256` exists only in the patched
   copy. Its link to production is the translation patches that add it and route its callers through
   it, which we checked. See section 1.
5. **Stale citation.** The docstring of `RngTotal` cites `rand_core` 0.9.3. `Cargo.lock` pins 0.9.5.
   The cited lines are the same in both versions.
6. **The security statements reach `generate` with no premise on it.** `uakeInitiator_secure_dh` and
   `uakeInitiator_secure_pq` run Core's extracted `curve.KeyPair.generate`, and their closures contain
   the outside items that its body calls (section 9). These statements take neither `GenerateTotal`
   nor a fault-or-value form of it, because `PartialContracts` has none. They count the faults of
   `generate` in `Pr[⊥]`, but no premise says what a returning call gives: a pair with a derived
   public half, or a key whose law relates to `P.ecKeygen`. `Protocols/LEDGER.md` records this under
   "Security placeholders". `ToOwnedTotal` has no fault-or-value form either, but its string goes only
   into an error value (section 2). See section 8.

## Summary

| Contract | Stands for | Discharge |
| --- | --- | --- |
| `HkdfSha256RfcContract` | `crypto::hkdf_sha256` (patched), `hkdf` 0.13.0, for every optional salt and every output of at most 8,160 bytes, on input lengths that keep every SHA-256 input below 2^61 bytes (`HkdfSha256Domain`) | a verified HMAC-SHA256 and HKDF, or an extraction of `hkdf`, `hmac` and `sha2`, with a proof that it meets the contract |
| `HkdfSha256Contract` | the same helper with no salt and 96 bytes of output, on the same input lengths | proved from `HkdfSha256RfcContract` (`hkdfSha256Contract_of_rfc`) |
| `ToOwnedTotal` | `<str as ToOwned>::to_owned` | a model of `String` construction in the Aeneas standard library |
| `RngTotal` | the caller's generator; production passes `UnwrapErr<OsRng>` | the caller's choice of generator; #84 for how the drawn states relate to it; an OS entropy failure stays outside any proof |
| `KyberEncapsBadLength`, `KyberEncapsBackend`, `KyberDecaps` | `kyber1024::Parameters`, libcrux `kyber1024` | a model of libcrux; for termination, a bound in libcrux, an assumption on SHAKE128, or the permutation argument of section 4 once all its steps are checked |
| `KyberBridge` | libcrux Kyber-1024 as the abstract KEM of the PQ statement | a model of libcrux, with #84 for the coins |
| `KyberDeltaCorrect`, `KyberDeltaCorrectAfterGenerate` | the decryption-failure probability of Kyber-1024, with encapsulation on a state from `P.coins` or on the state that `generate` returns | a proof that the failure mass on the ideal draws is at most δ, from the published analysis and a model of libcrux; for the second, also a description of the state that `generate` returns |
| `AgreementDerived`, `AgreementTotal`, `TorsionFreeTotal`, `DerivedCanonical`, `SignTotal`, `SignVerify`, `VerifyTotal` | X25519 and XEdDSA in `rust/core/src/curve.rs` | #76, from the curve25519-dalek specifications |
| `GenerateTotal` | `KeyPair::generate` of libsignal-core (`rust/core/src/curve.rs`), extracted with its body, which calls items of curve25519-dalek and x25519-dalek that have no body | proved from `ClampIntegerContract` and `X25519SecretContract` (`generateTotal_of_contracts`); `RngTotal` is a premise inside `GenerateTotal` |
| `ClampIntegerContract` | `clamp_integer` of `curve25519-dalek` 5.0.0 | the fork's `clamp_integer_spec`, with clamp idempotence on numbers and the link from our constant to the fork's function |
| `X25519SecretContract` | `StaticSecret`, `PublicKey::from(&StaticSecret)` and `PublicKey::as_bytes` of `x25519-dalek` 3.0.0 | an extraction or a verification of `x25519-dalek` |

## 1. `HkdfSha256RfcContract` and `HkdfSha256Contract`

**Statement.** `HkdfSha256RfcContract H` in `rust/Libsignal/Proofs/Protocol/Crypto/HkdfSha256.lean`.
For every optional salt, every input key material `ikm`, every `info` and every buffer `out` of at
most 255 · 32 = 8,160 bytes, where the salt, `ikm` and `info` satisfy `HkdfSha256Domain`, the call
`crypto.hkdf_sha256 salt ikm info out` returns `Ok(())` and a buffer of the same length. The buffer holds `hkdfSha256Okm H salt ikm info L`, where `L` is the
length of `out`: HKDF-Extract with the salt, followed by HKDF-Expand for `L` bytes (RFC 5869,
Sections 2.2 and 2.3), computed from the MAC interface `H`. A present salt, the empty one included,
is the HMAC key as given. An absent salt is `hkdfDefaultSalt`, 32 zero bytes. The contract does not
say that `H` is HMAC-SHA256.

`HkdfSha256Domain salt ikm info` bounds the input lengths: a present salt has fewer than 2^61 bytes,
`ikm` has fewer than 2^61 - 64 bytes, and `info` has fewer than 2^61 - 97 bytes. On these inputs,
every SHA-256 input of the call has fewer than 2^61 bytes. This is the limit of FIPS 180-4 and of
the `sha2` crate. The bound is uniform in the output length, so it is sufficient for every output
length but not always necessary (see the `info` item below). "Checked here" gives the reason for
each number.

`HkdfSha256Contract H`, in the same file, is the case that PQXDH uses: no salt, a 96-byte buffer, and
`ikm` and `info` in `HkdfSha256Domain`. The buffer is filled with `hkdfSha256Okm96 H none ikm info`.
It is no longer assumed: `hkdfSha256Contract_of_rfc` proves it from `HkdfSha256RfcContract H`,
through `hkdfSha256Okm_ninetySix`, which says that the HKDF output of `hkdfSha256Okm` at 96 bytes is
`hkdfSha256Okm96`. The statements that take `HkdfSha256Contract H` still take it as a hypothesis.
Three theorems about the extracted key derivation also take the domain as a hypothesis:

- `hkdf_sha256_okm96_spec` and `derive_with_label_spec` take `HkdfSha256Domain` with no salt;
- `derive_spec` takes `secret_input.length + 64 < 2 ^ 61`, which gives the domain with the 46-byte
  PQXDH label.

The statements above them call the derivation on at most 192 bytes, and their proofs show the bound
by arithmetic (`deriveKeysTotal` and `kdfInput_derive_ok`).

**Stands for.** The helper `libsignal_protocol::crypto::hkdf_sha256` that
`translation-patches/protocol-crypto-hkdf_sha256.patch` adds. Its body is
`hkdf::Hkdf::<Sha256>::new(salt, input_key_material).expand(info, output)`. Production has no such
helper. Upstream `HandshakeKeys::derive_with_label` (`rust/protocol/src/pqxdh.rs`) makes the same
`Hkdf` call inside `libsignal_core::derive_arrays`.
`translation-patches/protocol-pqxdh-HandshakeKeys-derive_with_label.patch` replaces that call with the
helper on a 96-byte buffer, split into three 32-byte arrays. In the patched copy, the helper also
serves `RootKey::create_chain` (`rust/protocol/src/ratchet/keys.rs`), with the 32-byte root key as
salt and a 64-byte buffer, and `MessageKeys::derive_keys`, inside `derive_arrays`. No statement uses
these two calls yet.

**Checked here.** The review of the 96-byte case without salt read these lines:

- In `hkdf` 0.13.0, a missing salt becomes `Output::<H>::default()`, that is 32 zero bytes
  (`src/lib.rs:46-50`). This is RFC 5869's default salt and the Lean `hkdfDefaultSalt`.
- Extract is the HMAC of `ikm` under the salt (`src/lib.rs:53-64`, `:117-121`).
- `expand_multi_info` (`src/lib.rs:130-166`) computes `T(i) = HMAC(PRK, T(i-1) | info | i)` with a
  one-byte counter `i` from 1. This is `hkdfExpandBlock`. It returns an error only when the output is
  longer than 255 · 32 bytes, so a 96-byte output excludes this error. The loop runs three times. This
  argument bounds only the output. The bound on the input lengths is the domain, below.
- The three `expect` calls on this path cannot fail. HMAC accepts a key of any length
  (`src/hmac_impl.rs`), and the PRK has 32 bytes, at least `HashLen` (`src/lib.rs:60-64`, `from_prk`).
  The counter `u8::try_from(block_n).expect(..) + 1` (`src/lib.rs:155`) sees the block indices 0, 1
  and 2, so the conversion succeeds and the sum is at most 3.
- `derive_arrays` (`rust/core/src/lib.rs:40-66`) fills a `#[repr(C)]` struct of three `[u8; 32]`
  arrays and returns them in order. So the patched split `[..32]`, `[32..64]`, `[64..]` gives the same
  three arrays.

For the general contract, this review read these lines of `hkdf` 0.13.0, `hmac` 0.13.0 and
`digest` 0.11.3:

- A present salt. `GenericHkdfExtract::new` (`hkdf`, `src/lib.rs:46-51`) passes a present salt
  unchanged to `HmacImpl::new_from_slice` (`src/hmac_impl.rs:23-25`). That function calls
  `KeyInit::new_from_slice` of `Hmac<Sha256>` and expects its result. The wrapper passes the key to
  `HmacCore::new_from_slice` (`digest`, `src/buffer_macros/fixed.rs:374-378`), which always
  returns `Ok` (`hmac`, `src/block_api.rs:53-69`). Its `get_der_key` (`hmac`, `src/utils.rs:9-32`)
  pads a key of at most 64 bytes with zeros to one block and hashes a longer key first. So every
  salt gives an HMAC key, the empty one and one longer than 64 bytes included, and the `expect`
  cannot fail. This is HMAC's key rule. In Rust, the empty salt and the absent salt therefore give the
  same PRK. In Lean the contract writes `H.mac [] ikm` for the empty salt and
  `H.mac hkdfDefaultSalt ikm` for the absent one. Both are right when `H` is HMAC-SHA256, but
  `HmacSha256` records only the length of a tag, so Lean cannot show that the two are equal.
- The PRK and the `expect` of `finalize` are as in the 96-byte case: the PRK has 32 bytes whatever
  the salt (`src/lib.rs:60-64`, `:104-112`).
- The output length. `expand_multi_info` returns `InvalidLength` only when the buffer is longer than
  `32 * 255` bytes (`src/lib.rs:137-140`), before it writes anything. Otherwise
  `okm.chunks_mut(32)` (`:142`) splits the buffer into `N = ⌈L / 32⌉` chunks, the last one shorter
  when 32 does not divide `L`. Each chunk receives the first `block.len()` bytes of its block
  (`:159-160`). So the buffer holds the first `L` bytes of `T(1) | … | T(N)`, which is
  `hkdfExpand`, and the call returns `Ok(())` (`:165`). For the lengths that this review traced:
  - 0: no chunk, and the buffer stays empty (`hkdfExpand` gives `[]`);
  - 1 and 31: one chunk with the first byte, or the first 31 bytes, of `T(1)`;
  - 32: one full chunk;
  - 33: `T(1)` and the first byte of `T(2)`;
  - 64 and 96: two and three full chunks;
  - 8,160: 255 full chunks.
- The truncation of the last block changes nothing later: the next block, if any, takes the full
  32-byte output of the block before (`:162`, `:145-147`), as RFC 5869 and `hkdfT` do. The first
  block takes nothing before `info` (`prev` starts as `None`, `:135`), and `hkdfT` starts from the
  empty `T(0)`.
- The counter. `enumerate` gives the block indices 0 to `N - 1`, at most 254. So
  `u8::try_from(block_n)` succeeds, and adding 1 gives at most 255 without overflow (`:155`). This
  is the byte `i + 1` of `hkdfT` for `i` from 0 to 254, where `BitVec.ofNat 8 (i + 1)` does not wrap.
- The buffer. The helper writes into the `&mut [u8]` it is given and never changes its length. The
  extraction returns the new slice, and the contract states that it keeps the length.
- Above 8,160 bytes, on inputs in the domain, the helper returns `Err(InvalidLength)` and writes
  nothing. The contract has the premise `out.length ≤ 255 * hashLen` and says nothing about these
  buffers. It does not state that the call fails there.

The domain. This review read these lines of `sha2` 0.11.0, `hmac` 0.13.0 and `hkdf` 0.13.0, and the
workspace `Cargo.toml`:

- The limit. `sha2` counts the full 64-byte blocks that a hash has received (`src/block_api.rs:36-42`).
  At the end it computes the message length in bits as `8 * (buffer.get_pos() as u64 + bs * self.block_len)`,
  a `u64` (`:64-67`). This product overflows exactly when the hash has received 2^61 bytes or more.
  So every SHA-256 input must have fewer than 2^61 bytes. FIPS 180-4 has the same limit: it defines
  SHA-256 for messages of fewer than 2^64 bits.
- The salt. HMAC hashes a key longer than the 64-byte block (`hmac`, `src/utils.rs:15-18`), so a
  present salt longer than 64 bytes is itself a SHA-256 input. This gives the bound on the salt. A
  salt of at most 64 bytes is not hashed, and the bound holds for it anyway.
- `ikm`. In Extract, HMAC's inner hash receives one 64-byte pad block (`hmac`,
  `src/block_api.rs:53-58`) and then `ikm` (`hkdf`, `src/lib.rs:53-56`, `:117-120`). This gives
  `ikm.length + 64 < 2^61`.
- `info`. In Expand, the inner hash of each block receives the pad block, the 32-byte block before
  (none for the first block), `info` and the counter byte (`hkdf`, `src/lib.rs:142-155`). That is
  at most `info.length + 97` bytes. The exact need depends on the output length `L`: at `L = 0`
  Expand hashes no block and `info` needs no bound; for `1 ≤ L ≤ 32` the only block needs
  `info.length + 65 < 2^61`; for `33 ≤ L ≤ 8,160` the second block needs
  `info.length + 97 < 2^61`. The domain uses the last bound for every output length. It is
  sufficient for each `L`, and it excludes some long `info` that the code accepts at `L ≤ 32`.
- Every other SHA-256 input has at most 96 bytes. HMAC's outer hash receives the 64-byte pad block
  and the 32-byte inner hash (`hmac`, `src/block_api.rs:79-90`). The PRK has 32 bytes, so HMAC
  pads it and does not hash it.
- Extract runs before Expand checks the output length (`hkdf`, `src/lib.rs:94-96`). So the bounds
  on the salt and `ikm` are needed at output length 0 too. Outside the domain, a buffer longer than
  8,160 bytes does not reach the `InvalidLength` check when a build with overflow checks panics in
  Extract.
- Overflow checks. The workspace enables them for release builds (`Cargo.toml:251-252`) and
  disables them for `sha2` and `hmac` (`:257-261`). Outside the domain, a SHA-256 input of the call can reach
  2^61 bytes. When one does, a build with overflow checks panics in `sha2`. The release build of
  this workspace wraps instead. The hash of that input then encodes the bit length modulo 2^64 and
  returns a value, although SHA-256 is not defined on such inputs. What the helper then returns depends on
  the output length `L`. At `L = 0` and above 8,160 bytes, only the hashes of Extract can wrap.
  At `L = 0` the helper still returns `Ok(())` and an empty buffer. Above 8,160 bytes it still
  returns `Err(InvalidLength)` and writes nothing. From 1 to 8,160 bytes, it returns `Ok(())` and
  fills the buffer, and at least part of the buffer depends on a wrapped hash. Aeneas translates Rust arithmetic as
  checked arithmetic (at the Aeneas pin, `UScalar.mul` is `UScalar.tryMk` of the product,
  `Aeneas/Std/Scalar/Ops/Mul.lean:18-19`), so an extraction of `sha2` would also fail there. The contract says nothing
  about these inputs.

**From the source.** That `Hmac<Sha256>` from the `hmac` and `sha2` crates computes HMAC-SHA256
(FIPS 198-1 over FIPS 180-4).

**Gaps.** The contract describes the patched helper. Its link to production is the patches, which
we read. `H` is a parameter: a theorem that assumes `HkdfSha256RfcContract H` holds for every `H`
that the helper matches, and the identification of `H` with HMAC-SHA256 is outside Lean. Lean
cannot show that the empty salt and the absent salt give the same output (see above). This review
did not read the buffer crate `block-buffer` 0.12.1, which `digest` uses to count the bytes of a
partial block. The argument for the limit above assumes, without reading that crate, that this
count stays below 64 and does not overflow.

The domain bounds the inputs in bytes, with the same numbers on every target. On a 32-bit target
every slice has fewer than 2^32 bytes, so every input is in the domain: an Aeneas slice has at most
`Usize.max` elements (`Aeneas/Std/SliceDef.lean:18`), and `Usize.max` is 2^32 - 1 there
(`Aeneas/Std/Scalar/Core.lean:53`, `:97`). On a 64-bit target the type
allows longer slices, and the domain excludes them. The calls that the statements reach are far
below the limit. The PQXDH call has no salt, its input key material has at most 192 bytes
(`deriveKeysTotal` in `Protocols/PQXDH/Kdf.lean`), and its `info` is the fixed 46-byte label
`WhisperText_X25519_SHA-256_CRYSTALS-KYBER-1024`.

**If false.** `hkdfSha256Contract_of_rfc` then gives nothing, and `HkdfSha256Contract H` loses
this proof. The 96-byte contract can still hold, since it is only about the call without salt on a
96-byte buffer. If the helper
returns a wrong output, another length, an error or a fault on the 96-byte call without salt and
with inputs in the domain, `HkdfSha256Contract` fails too.
`derive_spec` and `derive_with_label_spec` take `HkdfSha256Contract H` as the hypothesis `h_hkdf`. If the contract
fails for HMAC-SHA256, this hypothesis fails for that `H`. The two theorems then say nothing about
production: neither that the derivation returns, nor that the root key, the chain key and the pqr key
are bytes 0 to 32, 32 to 64 and 64 to 96 of the HKDF output. The same hypothesis fails in
`deriveKeysTotal` and in every Full statement that takes the contract: `coreCompletion_extracted`,
`jointKeyAgreement_extracted`, both `wrapperAgreement_*`, `fullExp_noLostMass` and the two `_total`
corollaries. The security statements take the fault-or-value form `HkdfSha256Partial` through
`PartialContracts`. If the helper returns anything else (an error, another length or other bytes),
that hypothesis fails too, and the security statements say nothing about production's key derivation.
Each caller passes the result of its own call to `expect`. The `expect` in `derive_with_label`
panics only if its call, with no salt and a 96-byte buffer, returns an error. The `expect` in
`create_chain` panics only if its call, with the 32-byte root key as salt and a 64-byte buffer,
returns an error. The same holds for the `expect` in `MessageKeys::derive_keys` and its call. A
fault in the helper never returns to the caller, so it never reaches an `expect`. The caller
faults with the helper.

**Discharge.** A verified HMAC-SHA256 and HKDF that the extraction can call, or an extraction of the
`hkdf`, `hmac` and `sha2` crates, together with a proof that this code meets
`HkdfSha256RfcContract H` on its whole domain: every optional salt, every output of at most 8,160
bytes and the input lengths of `HkdfSha256Domain`. An extraction alone does not give this
proof. The proof discharges `HkdfSha256Contract` too, by `hkdfSha256Contract_of_rfc`, and
`derive_spec` already proves the extracted key derivation from it. On the domain, the length
computation of `sha2` does not overflow, so checked arithmetic, as in Aeneas, does not block such
a discharge. The identification of
`H` with HMAC-SHA256 stays outside Lean in both cases.

**Fault-or-value form.** `HkdfSha256Partial H`, on the same domain: no salt, a 96-byte buffer, and
`ikm` and `info` in `HkdfSha256Domain`. `hkdfSha256Partial_of_contract`
(`Protocols/PQXDH/Contracts.lean`) proves it from `HkdfSha256Contract H`, so it also follows from
`HkdfSha256RfcContract H`.

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

**If false.** Signing, Kyber encapsulation and Core's `generate` could fault, because `SignTotal`,
`KyberEncapsBackend` and `GenerateTotal` take `RngTotal` as a premise. The completion and agreement
statements and `fullExp_noLostMass` depend on it. The two fault-counting security statements,
`uakeInitiator_secure_dh` and `uakeInitiator_secure_pq`, do not take it: they count faults in `Pr[⊥]`.
The two `_total` corollaries take `RngTotal` for both views of the generator, on a domain that
contains the states from `P.coins` (`Protocols/PQXDH/Security.lean`), so they depend on it.

**Discharge.** The draws from `P.coins` stay a modelling choice for the correctness statements. How
they relate to a caller's generator across sessions belongs to the Full-side security experiment
(#84). For a deterministic generator, such as the ChaCha generator of the tests, `RngTotal` could
be proved from a body.

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
  decapsulation samples the same matrix when it re-encrypts. The source comment (`:90-92`) cites
  ePrint 2023/708 for the claim that needing more than five blocks should be very unlikely. The paper
  derives this for uniformly random input (Section 2) and leaves it open for SHAKE128; what it proves
  for SHAKE128 is termination on every seed, with no useful bound (see "Gaps").
- Panic freedom of libcrux's arithmetic. libcrux carries hax and F* annotations, but `sample_from_xof`
  is marked `verification_status(lax)` (`src/sampling.rs:74`).
- On a 1568-byte ciphertext that does not match the key, Kyber returns a pseudorandom secret, not an
  error (implicit rejection). `KyberDecaps` claims only that some 32-byte secret is returned.

**Gaps.** Termination on every key is a claim about SHAKE128 on every seed, and the adversary chooses
the seed. Under a random-oracle view of SHAKE128 the loop ends with probability 1. For a fixed seed,
ePrint 2023/708 proves that Kyber's sampling, as specified, ends after at most 3 · 2^1600 calls of the
permutation per matrix entry. We know of no such proof for libcrux's code. The route below applies the
paper's argument to it, but this review did not check all its steps. libsignal does not call libcrux's
`validate_public_key`, so encapsulation accepts any 1568 bytes. The contract matches this.

**A possible discharge route for termination (not fully checked).** For a fixed seed, the sampling
loop may end for a deterministic reason. Steps 1 to 4 follow the argument of ePrint 2023/708
(Section 3), which is about Kyber as specified, and locate its premises in libcrux's code. We checked
the first three steps below in `libcrux-sha3` 0.0.10 and in the portable backend of `libcrux-ml-kem`
0.0.10, both pinned in `Cargo.lock`.

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
assumption only if these bytes are uniform when the state comes from `P.coins`. The Full-side
security experiment (#84) is where this question belongs. Two more
differences separate the Lean premise from the usual computational assumption. The premise `hkem` of
`uakeInitiator_secure_pq` bounds the advantage of every `K.IND_CCA_Adversary`, with no resource bound
(#41; see the limits in the module docstring of `Protocols/PQXDH/Security.lean`). And `K`'s key
generation is the law of `P.pqKeygen`, so the premise is about Kyber's own key generation only if
`P.pqKeygen` draws keys as Kyber does. #75 lists `P.pqKeygen` among the ideal draws that nothing
relates yet, but none of its proposed steps relates it to Kyber's key generation. Last, the bridge's
clause on the extracted encapsulation holds on every state, but `K`'s encapsulation draws its state
from `P.coins`. In the wrapper, Alice encapsulates on the state that Core's `generate` returns from a
state drawn from `P.coins`, and no premise relates the law of that state to `P.coins` (section 8).

**If false.** `uakeInitiator_secure_pq` and `uakeInitiator_secure_pq_total` take `KyberBridge P K` as a
hypothesis, next to the IND-CCA premise on `K`. If the bridge fails for a `K`, the statements say
nothing for that `K`, so its IND-CCA premise gives no bound on the extracted Kyber.

**Discharge.** A model of libcrux's Kyber-1024, with #84 for the coins.

## 6. `KyberDeltaCorrect` and `KyberDeltaCorrectAfterGenerate`

**Statements.** Both are in `Protocols/PQXDH/Kem.lean`. `δ` stays symbolic in both.

- `KyberDeltaCorrect P δ`: the correctness error of `kyberKem P` under `rustRuntime` is at most `δ`.
  This is the probability, over a key pair from `P.pqKeygen` and a state from `P.coins`, that
  encapsulation and decapsulation do not return the same secret. Faults and protocol errors count as
  failures.
- `KyberDeltaCorrectAfterGenerate P δ`: the same bound for `kyberKemAfterGenerate P`. Its key
  generation and decapsulation are those of `kyberKem P`. Its encapsulation draws a state from
  `P.coins`, runs Core's `curve.KeyPair.generate` on it, drops the key pair, and encapsulates on the
  state that `generate` returns. Faults of `generate` count as failures too.

**Stands for.** The decryption-failure probability of Kyber-1024 as libcrux implements it.
`KyberDeltaCorrectAfterGenerate` stands for it with encapsulation on Alice's generator after that
generator has drawn her ephemeral key.

**Checked here, `KyberDeltaCorrectAfterGenerate`.**

- In production, `process_prekey_bundle` calls `KeyPair::generate(&mut csprng)`
  (`rust/protocol/src/session.rs:237`) and passes the same generator to `initialize_alice_session`
  (`:262`). That function passes it to `pqxdh_initiate` (`rust/protocol/src/ratchet.rs:55`,
  `rust/protocol/src/pqxdh.rs:48`), which computes three or four agreements and then encapsulates with
  it (`pqxdh.rs:227`). Nothing draws from the generator between `generate` and the encapsulation.
- `kyberKem` and `kyberKemAfterGenerate` share key generation, decapsulation and `kyberEncapsOn`.
  They differ only in encapsulation. `kyberKemAfterGenerate` first runs `generate` on the drawn state.
  If `generate` faults, encapsulation faults without running `kyberEncapsOn`. Otherwise it runs
  `kyberEncapsOn` on the state that `generate` returns. In the wrapper, `initiate`
  (`Protocols/PQXDH/Scheme.lean`) runs the initiator's entry point on the state that `generate`
  returns, which is the state that `kyberKemAfterGenerate` uses.
- Neither contract can be derived in Lean from the other. Both bound an average over the
  encapsulation state, and the two states can have different laws. `GenerateTotal` says only that the
  returned state is in `Dom` (section 8). No Lean lemma relates the two contracts.

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
  encapsulation coins. `KyberDeltaCorrect` is over `P.pqKeygen`, which only `PQKeyPairShape`
  constrains, and over the generator states of `P.coins`. Reusing a published δ needs a proof that the failure mass
  on these draws, counting faults, protocol errors and mismatched secrets, is at most δ. Such a proof
  would also need libcrux to implement the specification. It would not need the wrappers to be free of
  faults: their faults count toward the same mass, so a proof that the wrappers do not fault on these
  draws is one way to bound that part. It does not need the draws to be production's. #75 lists
  `P.pqKeygen` and `P.coins` among the ideal draws that nothing relates yet, but none of its proposed
  steps relates `P.pqKeygen` to Kyber's key generation. No route to the proof is done.
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
- A published δ reaches `KyberDeltaCorrectAfterGenerate` only with a proof that the failure mass is at
  most δ when encapsulation runs on the state that `generate` returns from a state drawn from
  `P.coins`. `KyberDeltaCorrect P δ` does not give this, and no premise describes the law of that
  state (section 8).

**If false.** `jointKeyAgreement_extracted` takes `KyberDeltaCorrect P δ` as a hypothesis, and both
`wrapperAgreement_*` take `KyberDeltaCorrectAfterGenerate P δ`. They conclude that the two parties
agree with probability at least `1 − δ`. If the correctness error of the KEM in the hypothesis is
above the chosen `δ`, the hypothesis fails, and the statement gives no agreement bound for that `δ`.

**Discharge.** For `KyberDeltaCorrect`, a proof that the failure mass on the ideal draws is at most δ,
from the published analysis and a model of libcrux. #75 has no step yet for `P.pqKeygen`. For
`KyberDeltaCorrectAfterGenerate`, the same proof for encapsulation on the state that `generate`
returns, which needs more about that state than `GenerateTotal` says.

## 7. Curve25519 and XEdDSA contracts

All seven are in `Protocols/PQXDH/Contracts.lean`. #76 plans to discharge them from the
curve25519-dalek specifications. This review stands until then.

**Stands for.** `PrivateKey::public_key`, `calculate_agreement` and `calculate_signature` and
`PublicKey::is_torsion_free`, `is_canonical` and `verify_signature_for_multipart_message` in
`rust/core/src/curve.rs`, over `rust/core/src/curve/curve25519.rs`, `x25519-dalek` 3.0.0 and
`curve25519-dalek` 5.0.0. Of these, `PrivateKey::public_key` is extracted with its body
(`rust/Libsignal/Translated/Core/Funs.lean`), and the contracts that name it speak of that definition.
The body calls `clamp_integer` of curve25519-dalek and items of x25519-dalek that have no body in Lean
(section 9). `ClampIntegerContract` and `X25519SecretContract` state facts about these items (sections
10 and 11).

| Contract | Statement | Checked here | From the source |
| --- | --- | --- | --- |
| `AgreementTotal` | agreement returns 32 bytes or `InvalidKeyAgreement` | `calculate_agreement` (`curve.rs:296-309`) runs X25519 and rejects only the all-zero value | assumed: X25519 itself does not panic |
| `AgreementDerived` | on keys with derived public halves, both agreements return the same 32 bytes | `public_key` (`curve.rs:259-267`) and agreement both use the clamped scalar (`curve25519.rs:170-174`); argument 1 below the table | assumed: both values are the u-coordinate of the product of the two clamped scalars with the base point, and that u-coordinate is 0 only for the identity and the point of order 2 |
| `TorsionFreeTotal` | the torsion check returns a Boolean | `is_torsion_free` (`curve.rs:165-174`) has no panic path of its own | assumed: `to_edwards` and `is_torsion_free` of curve25519-dalek do not panic |
| `DerivedCanonical` | a derived public key passes `is_canonical` | `is_canonical` is `is_torsion_free && scalar_is_in_range` (`curve.rs:165-190`) | assumed: a derived key lies in the prime-order subgroup, and its u-coordinate is encoded below `2^255 - 19` |
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

The cells marked "assumed" are not checked. The cells of `AgreementDerived` and `DerivedCanonical`
state properties of X25519 and of the curve, which we did not check in the pinned code. The
`curve25519-dalek` 5.0.0 doc comments that we read (`src/montgomery.rs:227-239` for `to_edwards`,
`src/edwards.rs:1079` for the double-scalar multiplication) say what these functions compute but state
no guarantee that they do not panic. We did not look for such a guarantee for X25519 or SHA-512, and we did not read any of this code for
panics.

**Gaps.** `VerifyTotal` states only that verification returns a Boolean. It does not say which
signatures or keys give `false`.

**If false.** The completion and agreement statements and `fullExp_noLostMass` take `CoreContracts`
and, for the wrapper, `SignatureContracts`. The security statements take the fault-or-value forms.
Both `wrapperAgreement_*`, `fullExp_noLostMass` and the two `_total` corollaries also take
`GenerateTotal` (section 8), and `coreCompletion_extracted` and `jointKeyAgreement_extracted` do not.

**Fault-or-value forms.** `AgreementPartial` and `DerivedCanonicalPartial` follow from the total forms.
The second part of `SignaturePartial` follows from `SignVerify`. The first part says, for every
generator, that a returning call gives a 64-byte signature. `SignTotal` gives this only for generators
that satisfy `RngTotal`, so this part is a separate claim. It holds for the Rust code, which returns a
64-byte array.

## 8. `GenerateTotal`

**Statement.** `GenerateTotal` in `Protocols/PQXDH/Contracts.lean`. When both views of the generator,
`crng.RngCoreInst` and `rng.rand_core_1RngCoreInst`, are total on the same `Dom` and the state is in
`Dom`, Core's `curve.KeyPair.generate` terminates without a panic. It returns a key pair that satisfies
`ECKeyPairValid` and a state in `Dom`. `ECKeyPairValid` (`Protocols/PQXDH/Defs.lean`) says that
`PrivateKey::public_key` on the private half returns `Ok` of the public half. The contract says
nothing about the law of the pair or of the returned state.

**Stands for.** `KeyPair::generate` of libsignal-core (`rust/core/src/curve.rs:327-341`). This is a
function of libsignal-core itself, not of an outside library. The Core extraction gives it and the
three functions of `curve::curve25519` that it calls their bodies
(`rust/Libsignal/Translated/Core/Funs.lean`), so the contract is a statement about these definitions.
It is proved from two contracts on outside crates, with the totality of the generator as its premise: see
"Discharge". The bodies call `clamp_integer` of curve25519-dalek and items of x25519-dalek that have
no body in Lean (section 9). The contract stands for these lines:

- `KeyPair::generate` (`curve.rs:327-341`). It calls `curve25519::PrivateKey::new`, and it stores
  `derive_public_key_bytes()` as the public key and `private_key_bytes()` as the private key.
- `curve25519::PrivateKey::new` (`rust/core/src/curve/curve25519.rs:27-37`). It fills a 32-byte array
  with `fill_bytes`, clamps it with `clamp_integer` and stores it in an `x25519_dalek::StaticSecret`.
- `derive_public_key_bytes` and `private_key_bytes` (`curve25519.rs:161-167`).

`process_prekey_bundle` calls it to draw Alice's ephemeral key (`rust/protocol/src/session.rs:237`).
In the Full realization, `initiate` (`Protocols/PQXDH/Scheme.lean`) calls the extracted
`curve.KeyPair.generate` on Alice's generator state for the same purpose, and `kyberKemAfterGenerate`
calls it before encapsulation (section 6).

**Checked here.** `generateTotal_of_contracts` (`Protocols/PQXDH/KeyGen.lean`) proves the contract in
Lean from `ClampIntegerContract` (section 10) and `X25519SecretContract` (section 11), using the premise
`RngTotal` of the `CryptoRng` view inside `GenerateTotal` (section 3). The proof follows the code:

- `generate_eq_readClampDerive` rewrites `generate` as one `fill_bytes` on a zeroed 32-byte buffer,
  then `clamp_integer`, `StaticSecret::from`, `PublicKey::from`, `as_bytes` and `to_bytes`. On a
  state in `Dom`, `fill_bytes` returns a state in `Dom`, and the two contracts say that each later
  call returns. So `generate` returns, with the state that `fill_bytes` returned.
- The private half holds the clamped bytes `c`, because `to_bytes` gives back the bytes that
  `StaticSecret::from` stored. `public_key_djb_eq` rewrites `PrivateKey::public_key` on `c` as the
  same sequence of calls, which clamps `c` again. `clamp_integer` returns `c` on `c`, so
  `public_key` makes the same calls on the same bytes and returns `Ok` of the same public key:
  `ECKeyPairValid` holds.

The proof uses neither `RngTotal` of the `rand::Rng` view, which `generate` never calls, nor the
part of `RngTotal` that keeps the length of the buffer.

**From the source.** As in sections 10 and 11. In particular, the base-point multiplication of
`curve25519-dalek` 5.0.0 is assumed not to panic (section 11).

**Gaps.**

- No fault-or-value form. `PartialContracts` does not include `GenerateTotal`.
  `uakeInitiator_secure_dh` and `uakeInitiator_secure_pq` run `curve.KeyPair.generate`, and these
  statements take no premise on it (finding 6).
- `ECKeyPairValid` is the only property of the pair. No premise describes the law of Alice's ephemeral
  key, which comes from `generate` and not from `P.ecKeygen`, or the law of the state that `generate`
  returns from a state drawn from `P.coins`. `Protocols/LEDGER.md` records this under "Security
  placeholders". Sections 5 and 6 meet the same gap for the state.
- The statements that use the contract still take it as the hypothesis `hG`. They do not take the two
  contracts in its place.

**If false.** Then, by `generateTotal_of_contracts`, `ClampIntegerContract` or `X25519SecretContract`
is false. Alice's ephemeral draw could fault on honest runs, or give a pair whose public half is
not the one derived from its private half. `fullExp_noLostMass`, the two `_total` corollaries and both
`wrapperAgreement_*` take `GenerateTotal` as the hypothesis `hG`. If it fails, these statements say
nothing about production. `coreCompletion_extracted` and `jointKeyAgreement_extracted` do not take it:
they draw the ephemeral key from `P.ecKeygen` (`coreHonestRun` in `Protocols/PQXDH/Correctness.lean`),
and they do not run `generate`.

**Discharge.** Proved: `generateTotal_of_contracts` derives `GenerateTotal` from
`ClampIntegerContract` and `X25519SecretContract`. What remains is to discharge these two contracts
(sections 10 and 11) and, for each caller, the totality of its generator (section 3).

**Fault-or-value form.** None. `PartialContracts` does not include `GenerateTotal`.

## 9. Opaque declarations reached by the PQXDH statements

The declarations below are all the axioms of the extraction that the frozen closures of
`pqxdh_initiate`, `pqxdh_accept` and the Full statements contain. A closure is frozen when a
`#guard_msgs` check on its `#print axioms` output fixes it, so that `lake build` fails when it
changes. The checks are those of the three spec summaries named under "Scope and conventions". No other
axiom of the extraction is reached. Besides these declarations, the closures contain `propext`,
`Classical.choice` and `Quot.sound`. Five closures in `Protocols/Specs/PQXDH.lean` also contain
`sorryAx`: those of `uakeInitiator_secure_dh`, `uakeInitiator_secure_pq`, their two `_total`
corollaries and `fullExp_noLostMass`. This `sorryAx` comes from the admitted statements that
`Protocols/LEDGER.md` lists under "Security placeholders", not from the extraction.

| Declaration | Covered by |
| --- | --- |
| `crypto.hkdf_sha256` | `HkdfSha256RfcContract`, and `HkdfSha256Contract`, which is proved from it (section 1) |
| `Str.Insts.AllocBorrowToOwnedString.to_owned` | `ToOwnedTotal` (section 2) |
| `kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.encapsulate` | `KyberEncapsBadLength`, `KyberEncapsBackend`, `KyberBridge`, `KyberDeltaCorrect`, `KyberDeltaCorrectAfterGenerate` (sections 4 to 6) |
| `kem.kyber1024.Parameters.Insts.Libsignal_protocolKemParameters.decapsulate` | `KyberDecaps`, `KyberBridge`, `KyberDeltaCorrect`, `KyberDeltaCorrectAfterGenerate` (sections 4 to 6) |
| `curve.PrivateKey.calculate_agreement` | `AgreementDerived`, `AgreementTotal` (section 7) |
| `curve.PrivateKey.calculate_signature` | `SignTotal`, `SignVerify` (section 7) |
| `curve.PublicKey.is_torsion_free` | `TorsionFreeTotal`, and `DerivedCanonical` through `is_canonical` (section 7) |
| `curve.PublicKey.verify_signature_for_multipart_message` | `VerifyTotal`, and `SignVerify` through `verify_signature` (section 7) |
| `curve25519_dalek.scalar.clamp_integer` | `ClampIntegerContract` (section 10); the bodies of `public_key` and `generate` call it, see below |
| `x25519_dalek.x25519.StaticSecret`, `x25519_dalek.x25519.PublicKey`, `x25519_dalek.x25519.StaticSecret.Insts.CoreConvertFromArrayU832.from`, `x25519_dalek.x25519.PublicKey.Insts.CoreConvertFromSharedAStaticSecret.from`, `x25519_dalek.x25519.PublicKey.as_bytes` | `X25519SecretContract` (section 11); the bodies of `public_key` and `generate` call them, see below |
| `x25519_dalek.x25519.StaticSecret.to_bytes` | `X25519SecretContract` (section 11); the body of `generate` calls it, see below |
| `kem.Public.Insts.Libsignal_protocolKemKeyKind.key_length`, `kem.Secret.Insts.Libsignal_protocolKemKeyKind.key_length` | none needed, see below |
| `core.num.niche_types.NonZeroU8Inner`, `core.num.nonzero.NonZero` | none needed, see below |

**Checked here.**

- The contracts constrain the same constants that the entry points and the Full realization call. The
  closures of `CoreContracts`, `SignatureContracts` and `PartialContracts` name the `curve.*`
  declarations of `rust/Libsignal/Translated/Core/FunsExternal.lean`. The closure of `GenerateTotal`
  names none of them: besides `propext`, `Classical.choice` and `Quot.sound`, it contains only the
  seven outside items of the table above.
  `rust/Libsignal/Translated/Protocol/FunsExternal.lean` declares no axiom for the curve functions in
  the table above. `rust/Libsignal/Translated/Core/CurveProvider.lean` makes the Protocol names of
  `calculate_agreement`, `calculate_signature` and `verify_signature_for_multipart_message`
  abbreviations of Core's declarations, such as `libsignal_core.curve.PrivateKey.calculate_agreement`
  for `curve.PrivateKey.calculate_agreement`. For `generate` and `public_key` it goes the other way:
  the Protocol names `libsignal_core.curve.KeyPair.generate` and
  `libsignal_core.curve.PrivateKey.public_key` are Core's definitions, and the names
  `curve.KeyPair.generate` and `curve.PrivateKey.public_key` that the contracts use are abbreviations
  of them. So a Protocol caller of the first three functions reaches the declaration that the
  contracts name, and a caller of `generate` or `public_key` reaches the definition that this name
  abbreviates. `is_torsion_free` has no Protocol name: Core's translated body of `is_canonical`
  (`rust/Libsignal/Translated/Core/Funs.lean`) calls `curve.PublicKey.is_torsion_free`. `initiate`
  and `kyberKemAfterGenerate` call `curve.KeyPair.generate`, the declaration that `GenerateTotal`
  names.
- The seven declarations of `curve25519-dalek` 5.0.0 and `x25519-dalek` 3.0.0 in the table are items
  of these outside crates that the extracted bodies of `PrivateKey::public_key` and
  `KeyPair::generate` call (`rust/Libsignal/Translated/Core/Funs.lean`). `clamp_integer` clamps 32
  bytes to an X25519 scalar. `StaticSecret` and `PublicKey` are the secret-key and public-key types of
  x25519-dalek, declared in `rust/Libsignal/Translated/Core/TypesExternal.lean`.
  `From<[u8; 32]> for StaticSecret`, `StaticSecret::to_bytes`, `From<&StaticSecret> for PublicKey` and
  `PublicKey::as_bytes` build a secret from bytes, return its bytes, derive its public key and return
  that key's bytes. These four and `clamp_integer` are declared in
  `rust/Libsignal/Translated/Core/FunsExternal.lean`. `public_key` calls all of them but `to_bytes`,
  and `generate` calls all seven, `to_bytes` through `private_key_bytes`. So the closures of
  `CoreContracts`, `SignatureContracts`, `PartialContracts`, `coreCompletion_extracted` and
  `jointKeyAgreement_extracted` contain all of them but `StaticSecret.to_bytes`, and the closures of
  the statements that run `generate`, such as the four security statements, `fullExp_noLostMass`,
  both `wrapperAgreement_*`, `GenerateTotal` and `KyberDeltaCorrectAfterGenerate`, contain all
  seven. The closures of `pqxdh_initiate` and `pqxdh_accept` contain none of them.
  `ClampIntegerContract` and `X25519SecretContract` state the facts about them that the proof of
  `GenerateTotal` uses; sections 10 and 11 review them and cite the lines of their source.
- The two `key_length` axioms enter the closures only as the field of the `KeyKind` instances
  (`rust/Libsignal/Translated/Protocol/Funs.lean`). On the PQXDH paths the instance is passed to
  `KeyMaterial`'s `deref`, which ignores it and returns the key bytes. No PQXDH path calls `key_length`.
- The two `NonZero` axioms are opaque types from Rust's `core`. They enter because variants of
  `SignalProtocolError` carry a `ProtocolAddress`, whose `DeviceId` holds a `NonZero<u8>`. An axiom of
  type `Type` claims only that a type exists.

## 10. `ClampIntegerContract`

**Statement.** `ClampIntegerContract` in `Protocols/PQXDH/Contracts.lean`. For every 32-byte array `b`,
the call `curve25519_dalek.scalar.clamp_integer b` returns some array `c`, and the call on `c` returns
`c`. The contract says that the function returns and that it returns its own output unchanged. It
does not say which array `c` is.

**Stands for.** `clamp_integer` of `curve25519-dalek` 5.0.0 (`src/scalar.rs:1407-1412`), which the
extraction declares without a body (`rust/Libsignal/Translated/Core/FunsExternal.lean`).
`curve25519::PrivateKey::new` (`rust/core/src/curve/curve25519.rs:34`) and
`From<[u8; 32]> for curve25519::PrivateKey` (`curve25519.rs:170-174`) call it, so `KeyPair::generate`
and `PrivateKey::public_key` reach it.

**Checked here.**

- `clamp_integer` is a `const fn` on a `[u8; 32]`. It masks byte 0 with `0b1111_1000`, masks byte 31
  with `0b0111_1111`, sets bit 6 of byte 31 with `0b0100_0000`, and returns the array. The two
  indices are constants inside the array, and the operations are bitwise, so the function has no
  panic path and no loop.
- On its own output the function changes no bit: the three low bits of byte 0 and bit 7 of byte 31
  are already clear, and bit 6 of byte 31 is already set.

**From the source.** The fork of curve25519-dalek proves `clamp_integer_spec` for its own Lean
translation of `clamp_integer`: the call returns, and the value of the result, read as a
little-endian number, is the RFC 7748 clamp of the value of the input. We did not check that proof.

**Gaps.** The contract does not give the value of the result. A statement about the law of the
generated key needs that value (#84). Nothing in Lean links our constant
`curve25519_dalek.scalar.clamp_integer` to the fork's definition.

**If false.** `generateTotal_of_contracts` gives nothing, and nothing then supports the hypothesis
`GenerateTotal` of the statements that take it (section 8).

**Discharge.** The curve25519-dalek fork's `clamp_integer_spec`, with clamp idempotence on numbers and
the link from our constant to the fork's function.

**Fault-or-value form.** None of its own. Because a Lean function has one value on each input, the
contract also gives the fault-or-value form: if `clamp_integer b` returns `c`, then `clamp_integer c`,
when it returns, returns `c`.

## 11. `X25519SecretContract`

**Statement.** `X25519SecretContract` in `Protocols/PQXDH/Contracts.lean`, with two clauses. First,
for every 32-byte array `x`, `StaticSecret::from` on `x` returns a secret `s`, and
`StaticSecret::to_bytes` on `s` returns `x`. Second, for every secret `s`,
`PublicKey::from(&StaticSecret)` on `s` returns a public key `pk`, and `PublicKey::as_bytes` on `pk`
returns some 32 bytes. The contract says nothing about which public key or which bytes these are.

**Stands for.** Items of `x25519-dalek` 3.0.0 that the extraction declares without a body
(`rust/Libsignal/Translated/Core/FunsExternal.lean` and `TypesExternal.lean`): the types
`StaticSecret` (`src/x25519.rs:206`) and `PublicKey` (`:32`), `From<[u8; 32]> for StaticSecret`
(`:247-252`), `StaticSecret::to_bytes` (`:235-237`), `From<&StaticSecret> for PublicKey` (`:255-260`)
and `PublicKey::as_bytes` (`:50-52`). In libsignal-core, `curve25519::PrivateKey::new`,
`derive_public_key_bytes`, `private_key_bytes` and `From<[u8; 32]> for curve25519::PrivateKey` call them
(`rust/core/src/curve/curve25519.rs:36`, `:161-174`).

**Checked here.**

- `StaticSecret` is a tuple struct around a `[u8; 32]`. `From<[u8; 32]>` stores the array, and
  `to_bytes` returns the field. Neither has a panic path.
- `PublicKey` is a tuple struct around a `MontgomeryPoint`. `PublicKey::as_bytes` returns
  `self.0.as_bytes()`, and `MontgomeryPoint::as_bytes` returns a reference to the point's 32-byte
  field (`curve25519-dalek` 5.0.0, `src/montgomery.rs:214-216`).
- `From<&StaticSecret> for PublicKey` computes
  `EdwardsPoint::mul_base_clamped(secret.0).to_montgomery()`.

**From the source.** Assumed, not checked: `EdwardsPoint::mul_base_clamped` and
`EdwardsPoint::to_montgomery` of `curve25519-dalek` 5.0.0 do not panic. We did not read them for
panics, as in section 7.

**Gaps.**

- The second clause says only that the derivation returns. A statement about agreement or about
  the law of the public key needs the point it computes.
- In Lean `StaticSecret` is opaque, so the second clause is stated for every value of that type. In
  Rust a `StaticSecret` is 32 bytes.

**If false.** `generateTotal_of_contracts` gives nothing, and nothing then supports the hypothesis
`GenerateTotal` of the statements that take it (section 8). The proof uses the second clause only on
a secret that `StaticSecret::from` returns on the output of `clamp_integer`. A failure of the second
clause only on other values of the opaque type would make the contract false and lose this proof,
but would say nothing against `GenerateTotal`: `generate` makes no call on such a value.

**Discharge.** An extraction or a verification of `x25519-dalek` 3.0.0. The fork of curve25519-dalek
contains the source of x25519-dalek but no Lean translation of it, so a dependency on the fork does
not discharge this contract.

**Fault-or-value form.** None of its own. The first clause also gives the fault-or-value form of the
round trip: if `StaticSecret::from` on `x` returns `s`, then `to_bytes` on `s`, when it returns,
returns `x`.
