# Extraction notes

Each crate is extracted by its own profile (see [`scripts/README.md`](scripts/README.md)): `libsignal-core`, the supported `signal-crypto` operations, and `libsignal-protocol`. Types shared across crates are declared once, by the profile that owns them.

The crypto profile translates AES-GCM constructors, encryption/decryption and tag control flow, GCM state cloning, and MAC update-and-return. The constructors propagate errors and assemble their state; `setup_gcm`, including its key/nonce validation and primitive initialization, remains external. Its existing AES/CTR/GHASH/hash primitive interfaces remain opaque; HPKE remains excluded. Backend declarations reached through opaque-type layout metadata are excluded without hiding additional local operations. The existing concrete `subtle::Choice` and equality models are owned by Crypto and reused by Core and Protocol through an exact trait alias.

PQXDH's optional-prekey accessors, `HandshakeKeys::derive` and `derive_with_label` are translated. The generated code supplies the domain-separation label, calls HKDF-SHA256 for 96 bytes, and copies bytes 0–31, 32–63 and 64–95 into the root, chain and initial PQR keys. HKDF remains the primitive boundary; splitting and key construction are generated.

## Public functions — signal-crypto

Depends on: `libsignal-core`, `aes`, `cbc`, `ctr`, `ghash`, `hmac`, `sha1`, `sha2`, `hkdf`, `hpke-rs`, `subtle`

### Error

- `Error` enum: `UnknownAlgorithm`, `InvalidKeySize`, `InvalidNonceSize`, `InvalidInputSize`, `InvalidTag`

### CryptographicMac

- `new(algo: &str, key: &[u8]) -> Result<Self>` — opaque (calls hmac)
- `update(&mut self, input: &[u8])` — opaque (calls hmac)
- `update_and_get(&mut self, input: &[u8]) -> &mut Self`
- `finalize(&mut self) -> Vec<u8>` — opaque (calls hmac)

### CryptographicHash

- `new(algo: &str) -> Result<Self>` — opaque (calls sha1/sha2)
- `update(&mut self, input: &[u8])` — opaque (calls sha1/sha2)
- `finalize(&mut self) -> Vec<u8>` — opaque (calls sha1/sha2)

### aes_cbc

- `aes_256_cbc_encrypt(ptext: &[u8], key: &[u8], iv: &[u8]) -> Result<Vec<u8>, EncryptionError>` — opaque
- `aes_256_cbc_decrypt(ctext: &[u8], key: &[u8], iv: &[u8]) -> Result<Vec<u8>, DecryptionError>` — opaque

### Aes256Ctr32

- `NONCE_SIZE: usize` (associated constant)
- `new(aes256: Aes256, nonce: &[u8], init_ctr: u32) -> Result<Self>` — opaque
- `from_key(key: &[u8], nonce: &[u8], init_ctr: u32) -> Result<Self>` — opaque
- `process(&mut self, buf: &mut [u8])` — opaque

### aes_gcm (module-level)

- `TAG_SIZE: usize = 16`
- `NONCE_SIZE: usize = 12`

### Aes256GcmEncryption

- `TAG_SIZE: usize` (associated constant)
- `NONCE_SIZE: usize` (associated constant)
- `new(key: &[u8], nonce: &[u8], associated_data: &[u8]) -> Result<Self>`
- `encrypt(&mut self, buf: &mut [u8])`
- `compute_tag(self) -> [u8; TAG_SIZE]`

### Aes256GcmDecryption

- `TAG_SIZE: usize` (associated constant)
- `NONCE_SIZE: usize` (associated constant)
- `new(key: &[u8], nonce: &[u8], associated_data: &[u8]) -> Result<Self>`
- `decrypt(&mut self, buf: &mut [u8])`
- `verify_tag(self, tag: &[u8]) -> Result<()>`

### HPKE (excluded)

Excluded entirely — complex external crypto provider (`hpke-rs`).

- `SimpleHpkeSender` trait
- `SimpleHpkeReceiver` trait
- `SignalHpkeCiphertextType` enum

## Public functions — libsignal-core

Depends on: `curve25519-dalek`, `x25519-dalek`, `sha2`, `uuid`, `zerocopy`, `derive_more`, `rand`

### E164

- `new(number: NonZeroU64) -> Self`
- `to_be_bytes(&self) -> [u8; 8]`
- `from_be_bytes(bytes: [u8; 8]) -> Option<Self>`

### SpecificServiceId

- `from_uuid_bytes(bytes: [u8; 16]) -> Self`
- `service_id_binary(&self) -> Vec<u8>`
- `service_id_fixed_width_binary(&self) -> ServiceIdFixedWidthBinaryBytes`
- ~~`service_id_string(&self) -> String`~~ — excluded (uses `format!`)
- `parse_from_service_id_binary(bytes: &[u8]) -> Option<Self>`
- `parse_from_service_id_fixed_width_binary(bytes: &ServiceIdFixedWidthBinaryBytes) -> Option<Self>`
- `parse_from_service_id_string(input: &str) -> Option<Self>` (calls `ServiceId::parse_from_service_id_string`)

### ServiceId

- `kind(&self) -> ServiceIdKind`
- `service_id_binary(&self) -> Vec<u8>`
- `service_id_fixed_width_binary(&self) -> ServiceIdFixedWidthBinaryBytes`
- ~~`service_id_string(&self) -> String`~~ — excluded (uses `format!`)
- `parse_from_service_id_binary(bytes: &[u8]) -> Option<Self>`
- `parse_from_service_id_fixed_width_binary(bytes: &ServiceIdFixedWidthBinaryBytes) -> Option<Self>`
- `parse_from_service_id_string(input: &str) -> Option<Self>` — `strip_prefix` replaced by `strip_pni_prefix`, a byte-prefix test and `split_at` (patch `core-address-ServiceId-parse_from_service_id_string`); calls `str::{len, as_bytes, split_at}` and `Uuid::try_parse`, which have no model
- `raw_uuid(self) -> Uuid`
- derived `PartialEq` (with the derived `PartialEq` of `SpecificServiceId`), and `PartialEq<SpecificServiceId<KIND>> for ServiceId`
- ~~`to_protocol_address(&self, device_id: DeviceId) -> ProtocolAddress`~~ — excluded (calls `service_id_string`)

### DeviceId

- `new(id: u8) -> Result<Self, InvalidDeviceId>`
- `new_nonzero(id: NonZeroU8) -> Result<Self, InvalidDeviceId>`

### ProtocolAddress

- `new(name: String, device_id: DeviceId) -> Self`
- derived `Clone` (with the derived `Clone` of `DeviceId`)
- `name(&self) -> &str`
- `device_id(&self) -> DeviceId`

### PublicKey

- `deserialize(value: &[u8]) -> Result<Self, CurveError>` — the `log::warn!` for trailing bytes moves into `log_public_key_trailing_bytes`, which stays opaque; calls `split_first` and `split_first_chunk` of `core::slice`, which have no model
- `TryFrom<&[u8]>` (calls `deserialize`)
- `public_key_bytes(&self) -> &[u8]`
- `from_djb_public_key_bytes(bytes: &[u8]) -> Result<Self, CurveError>`
- `serialize(&self) -> Box<[u8]>`
- `verify_signature(&self, message: &[u8], signature: &[u8]) -> bool`
- `verify_signature_for_multipart_message(&self, message: &[&[u8]], signature: &[u8]) -> bool` — opaque (calls curve25519)
- `key_type(&self) -> KeyType`
- `is_canonical(&self) -> bool`
- `PartialEq` (calls `ConstantTimeEq for PublicKey`, `key_data` and the derived `PartialEq` of `KeyType`)

### PrivateKey

- `deserialize(value: &[u8]) -> Result<Self, CurveError>` — calls `scalar::clamp_integer`, which has no model
- `TryFrom<&[u8]>` (calls `deserialize`)
- `serialize(&self) -> Vec<u8>`
- `public_key(&self) -> Result<PublicKey, CurveError>` — extracted with its body (calls `curve25519::PrivateKey::from` and `derive_public_key_bytes`)
- `key_type(&self) -> KeyType`
- `calculate_signature(...)` — opaque (calls curve25519)
- `calculate_signature_for_multipart_message(...)` — opaque (calls curve25519)
- `calculate_agreement(&self, their_key: &PublicKey) -> Result<Box<[u8]>, CurveError>` — opaque (calls curve25519)

### KeyPair

- `generate(csprng: &mut R) -> Self` — extracted with its body (calls `curve25519::PrivateKey::new`, `derive_public_key_bytes` and `private_key_bytes`)
- `new(public_key: PublicKey, private_key: PrivateKey) -> Self`
- `from_public_and_private(public_key: &[u8], private_key: &[u8]) -> Result<Self, CurveError>`
- `calculate_signature(...)` — opaque (calls curve25519)
- `calculate_agreement(&self, their_key: &PublicKey) -> Result<Box<[u8]>, CurveError>` — opaque (calls curve25519)

### curve25519 (submodule)

The core profile does not exclude this module. `KeyPair::generate` and `PrivateKey::public_key` call four of its items, which are extracted with their bodies: `PrivateKey::new`, `derive_public_key_bytes`, `private_key_bytes` and `From<[u8; 32]> for PrivateKey`. Its signer, verifier and agreement are not extracted: their callers in `curve.rs` are opaque, so Charon does not reach them. The module was first excluded because Charon panicked on the `simplify_constants` pass on an array constant in `calculate_signature`. That panic was not tested again. The protocol profile still excludes the module.

These four items call items of two crates outside libsignal. The extraction gives those outside items no body, and no fact about them is stated:

- curve25519-dalek 5.0.0: the function `scalar::clamp_integer` (`curve25519_dalek.scalar.clamp_integer`)
- x25519-dalek 3.0.0: the types `StaticSecret` and `PublicKey`, and the functions `From<[u8; 32]> for StaticSecret`, `StaticSecret::to_bytes`, `From<&StaticSecret> for PublicKey` (the base-point multiplication) and `PublicKey::as_bytes` (`x25519_dalek.x25519.*` in `Core/TypesExternal.lean` and `Core/FunsExternal.lean`)

Contains:
- `AGREEMENT_LENGTH: usize = 32`
- `PRIVATE_KEY_LENGTH: usize = 32`
- `PUBLIC_KEY_LENGTH: usize = 32`
- `SIGNATURE_LENGTH: usize = 64`
- `PrivateKey::new`, `calculate_agreement`, `calculate_signature`, `verify_signature`, `derive_public_key_bytes`, `private_key_bytes`

### Free functions

- `try_scoped(f: impl FnOnce() -> Result<T, E>) -> Result<T, E>`
- `derive_arrays(derive: impl FnOnce(&mut [u8])) -> ([u8; N1], [u8; N2], [u8; N3])` — opaque (uses zerocopy)
- `try_derive_arrays(derive: impl FnOnce(&mut [u8]) -> Result<(), E>) -> Result<(...), E>` — opaque (uses zerocopy)
- `VERSION: &str`

## Source modifications

The committed `rust/` tree is upstream libsignal at `upstream.commit` in `rust/aeneas-config.yml`. Every change made for extraction is a patch in [`translation-patches/`](translation-patches/), applied only to the work copy that Charon reads. Each patch header gives the change, the reason and the effect on the production build. This section indexes the patches. Items that a profile makes opaque or excludes in its YAML need no source change. The YAML lists them with the reason.

The correspondence claims concern protocol values and cryptographic operation order, not identical memory layout or logging locations. To revert a patch, delete it and require clean Charon LLBC, Aeneas generation of the same roots, `lake build Libsignal` and the production Rust build.

### Crate setup and tool attributes

| Patch | Change |
| --- | --- |
| `crypto-Cargo-extraction_feature`, `protocol-Cargo-extraction_feature` | An empty `extraction` feature |
| `crypto-lib-register_tool`, `protocol-lib-register_tool` | Under the feature, `register_tool(charon)`, so that `#[charon::…]` attributes are valid |

### Representation changes

| Patch | Change | Limitation |
| --- | --- | --- |
| `core-address-SpecificServiceId`, `core-address-DeviceId`, `core-e164-E164`, `crypto-aes_ctr-Aes256Ctr32`, `protocol-timestamp-Timestamp` | Tuple struct with one private field → struct with one named field | [aeneas#767](https://github.com/AeneasVerif/aeneas/issues/767) |
| `protocol-kem-Ciphertext`, `protocol-pqxdh-RecipientParameters` | Own the ciphertext (`Box<[u8]>`, `kem::SerializedCiphertext`) instead of borrowing it, so the types have no lifetime parameter; the caller clones the ciphertext it passes (`session_core::start_responder_session`) | Charon fails on a lifetime parameter in a field type |

### Gated out or opaque under the `extraction` feature

| Patch | Items | Limitation |
| --- | --- | --- |
| `protocol-lib-store_api`, `protocol-storage-store_api`, `protocol-storage_traits-store_traits`, `protocol-sealed_sender-store_api`, `protocol-session_management-store_api` | The `#[async_trait]` store traits, their in-memory implementations and the API that takes stores | Charon's hax frontend panics on the async store traits |
| `protocol-handshake-Handshake`, `protocol-pqxdh-Pqxdh-Handshake` | The `Handshake` trait and its impl (excluded); callers use the free functions (`protocol-ratchet-pqxdh_calls`, `protocol-pqxdh-InitiatorAgreement`) | Trait associated type with a lifetime parameter |
| `protocol-kem-DynParameters` | `DynParameters` and its blanket impl (excluded); the three callers dispatch on `KeyType` directly | `dyn` trait dispatch |
| `protocol-error-ApplicationCallbackError` | The variant and its constructor | Not recorded; the variant holds a `Box<dyn Error>` |
| `protocol-state_session-SessionUsabilityRequirements` | `bitflags!` type → a `u32` newtype with the same constants, `all` and `contains` | `bitflags!` generic iterator code |
| `protocol-timestamp-Timestamp-serde`, `protocol-timestamp-Timestamp-Distribution` | The serde derives and the `Distribution` impl of `Timestamp` | Not recorded |
| `crypto-hash-CryptographicMac`, `crypto-hash-CryptographicHash` | The `Clone` derive (gated) and the enum (opaque) | Not recorded |
| `protocol-kem-KeyMaterial` | Explicit `Deref` to `[u8]` instead of `derive_more::Deref` with `forward` | Forwarding dereference gives an Aeneas type mismatch |

### Rewrites of translated code

Each workaround names its limitation in the patch header or in a comment in the patched source.

| Patch | Change | Limitation | Revert when |
| --- | --- | --- | --- |
| `core-address-ServiceId-parse_from_service_id_string` | `input.strip_prefix("PNI:")` → `strip_pni_prefix(input)`, a new function at the end of the file that tests that `input.as_bytes()` starts with `b"PNI:"` (a length check and a slice comparison) and returns the second half of `input.split_at(4)` | `str::strip_prefix` is generic over `core::str::pattern::Pattern`, which the profiles exclude (generic associated types); without the patch Aeneas reports "Could not find: trait_decl_id" at the signature of `strip_prefix` and leaves the parser without a body | `core::str::pattern` translates |
| `core-curve-PublicKey-deserialize-logging` | The `log::warn!` for trailing bytes in `PublicKey::deserialize` moved into `log_public_key_trailing_bytes`, a `#[track_caller]` function called on the line of the old call with `tail.len()`; same level, target, module path, file, line and message, with one extra stack frame (the helper's) while the warning is logged | Aeneas stops with an internal error on the `log!` expansion, then with `Not_found` in `llbc/FunsAnalysis.ml` | `log!` translates inline |
| `protocol-crypto-hkdf_sha256`; callers `protocol-ratchet_keys-MessageKeys-derive_keys`, `protocol-ratchet_keys-RootKey-create_chain`, `protocol-pqxdh-HandshakeKeys-derive_with_label` | Byte-slice HKDF-SHA256 helper, same salt/input/info/output | Charon cannot lift HKDF's generic-array associated types under `--preset=aeneas` | `Hkdf::<Sha256>::expand` translates inline |
| `protocol-crypto-hmac_sha256_parts`; caller `protocol-protocol-SignalMessage-compute_mac` | One HMAC-SHA256 state fed the same three parts in order | Same associated-type limitation, for incremental `Hmac` | Inline `Hmac::update` calls translate |
| `protocol-pqxdh-HandshakeKeys-derive_with_label` | Replace `derive_arrays` with a zeroed 96-byte buffer and three fixed 32-byte copies; retain the same HKDF call, label, error expectation and chain counter zero | Excluded zerocopy traits leave impls that trigger an Aeneas prepass error; retaining them exposes unsupported pointer operations | The original array helper translates with concrete splitting and no added assumptions |
| `protocol-pqxdh-pqxdh_initiate` | `encapsulate(&mut csprng)` → `encapsulate::<R>(&mut *csprng)` | For a `&mut &mut R` argument Aeneas generates an ill-typed RNG state update | The double borrow translates |
| `protocol-double_ratchet-error_messages` | Four literals moved to named `&str` constants with the same bytes | Aeneas loses a literal returned from a `map_err` closure ("no bottoms in the value") | Inline literals translate |
| `protocol-double_ratchet-option_map_closures` | `map(SenderChain::from_pb)` → `map(\|chain\| SenderChain::from_pb(chain))`, same for `to_pb` | Function-item arguments to `Option::map` are not translated | The function-item form translates |
| `protocol-double_ratchet-logging` | The four `log!` calls in `consume_message_key` and `find_receiver_chain_index` moved into `log_duplicate_message`, `log_future_message_limit`, `log_jump_ahead` and `log_corrupt_receiver_chain`, same level and message, called at the same point | As for `protocol-triple_ratchet-logging` | `log!` translates inline |
| `protocol-double_ratchet-take_skipped_key` | `MessageKeyGenerator::from_pb(key_pb).map(Some).map_err(InvalidSessionError)` moved unchanged into `skipped_key_from_pb` | `from_pb` is opaque and returns a `&'static str` error; moving it into `InvalidSessionError` hits the static-borrow defect described for `DecryptionError` | The expression translates inline |
| `protocol-double_ratchet-dh_ratchet_step` | The first statement of `dh_ratchet_step`, `self.sender_chain.as_ref().ok_or(InvalidSessionError("missing sender chain"))?.ratchet_key.private_key`, becomes `let Some(sender_chain) = self.sender_chain.as_ref() else { return Err(InvalidSessionError("missing sender chain").into()); };` followed by the read of `private_key`. The function stays transparent. | From nightly-2026.10.24-74aabd5 on (checked up to nightly-2026.11.10-0d21a9e), Aeneas stops on the original body with `Unreachable` in `interp/InterpExpansion.ml`. The trigger is `.ok_or(E)?` on a borrow of `self`, then the `&mut self` call `take_root_key`, then `?` on `create_chain`, whose error type holds a `&'static str`. The nightlies 2026.09.30-0855ce1 and 2026.10.15-cd41995 translate the original | The original `?` form translates |
| `protocol-triple_ratchet-error_messages` | Five literals (`"version does not fit in u8"`, `"encrypt"`, `"decrypt"`, `"invalid sender/receiver chain message keys"`) moved to named `&str` constants with the same bytes | As in `double_ratchet.rs`, for literals returned from closures and early returns | Inline literals translate |
| `protocol-triple_ratchet-logging` | The `log::error!` in `encrypt` and the `log::warn!` in `decrypt` moved into `log_sender_chain_corrupt` / `log_receiver_chain_corrupt`, same level and message, called at the same point; log records now give the helper's line | Aeneas stops with an internal error on `log!` expansions | `log!` translates inline |
| `protocol-triple_ratchet-address_pair` | `local_address.map(\|addr\| (addr, remote_address))` → a helper whose body is the equivalent `match` | A closure returning two borrows cannot be ended; the same `match` inline fails to join its branches | Either inline form translates |
| `protocol-triple_ratchet-decrypt-aes_cbc_errors` | `Err(BadKeyOrIv)` / `Err(BadCiphertext(msg))` arms → `Err(e) if is_bad_key_or_iv(&e)` / `Err(e)`; the message is built by `decrypt_failure_message(e)`, which matches `BadCiphertext(msg)` and formats as before. Its `BadKeyOrIv` arm is `unreachable!`, because the guard handles that variant first. | `BadCiphertext(&'static str)` comes from an opaque call; Aeneas has no loan for that static borrow, so expanding the variant or copying the field fails | Matching the variants inline translates |
| `protocol-triple_ratchet-decrypt-spqr_errors` | `match e { StateDecode => …, _ => … }` → `if is_state_decode(&e) { … } else { … }` with the same two results | `spqr::Error` has an `InvalidParams(&'static str)` variant; matching it hits the same static-borrow defect (a crash in Aeneas's translation pass) | Same |
| `protocol-triple_ratchet-from_session_state` | Parameter `state` renamed `session_state` | A parameter named like the `state` module shadows it in the generated Lean ([aeneas#1098](https://github.com/AeneasVerif/aeneas/issues/1098)) | Aeneas avoids the clash |
| `protocol-protocol-SignalMessage-verify_mac_with_addresses` | The two `log::warn!` calls in `SignalMessage::verify_mac_with_addresses` moved into `log_invalid_local_addresses` / `log_address_mismatch`, same level and message, called at the same point | As for `protocol-triple_ratchet-logging` | `log!` translates inline |
| `protocol-state_session-promote_matching_session` | The search loop of `SessionRecord::promote_matching_session` moves into the new method `find_previous_session`, an index loop that decodes each stored session inline; the local `state` is renamed `promoted` | At nightly-2026.10.30-de16f3c Aeneas stops on the original `for` loop over `previous_session_states().enumerate()` with an internal error (`interp/InterpReduceCollapse.ml`), and the closure impls of `previous_session_states` fail a prepass (see the YAML). A local named `state` hides the `state` module in the generated Lean ([aeneas#1098](https://github.com/AeneasVerif/aeneas/issues/1098)) | The original loop translates |
| `protocol-state_session-set_unacknowledged_kyber_pre_key_id` | `as_mut().expect(..)` → `take().expect(..)`, then the updated value is stored back with `Some(pending)` | For `expect` on an `Option<&mut T>` Aeneas generates a write-back function, but its model of `Option::expect` returns the value only, so the Lean does not type-check | The model of `expect` has the write-back |
| `protocol-session_core-prekey_steps`; callers `protocol-session-process_prekey`, `protocol-session-process_prekey_bundle` | The stretches of code of the `async` callers `process_prekey`, `process_prekey_impl` and `process_prekey_bundle` between two store calls move into the functions of the new module `session_core`. The callers keep every store call in its place and call the functions in the original order. The functions cover the trust answer, the two signature checks, the initiator's key choice, session set-up (up to `ratchet::initialize_alice_session`) and pending prekey IDs, and the responder's session lookup, version check, Kyber checks and session set-up (up to `ratchet::initialize_bob_session`). The `log::info!` call of `process_prekey_bundle` stays in the caller | Charon cannot translate the `async` store traits, so the extraction leaves out the `session` module | Charon translates the `async` store traits |
| `protocol-protocol-PreKeySignalMessage-kyber_ciphertext` | `self.kyber_payload.as_ref().map(\|kyber\| &kyber.ciphertext)` → a `match` on `&self.kyber_payload` that returns `Some(&kyber.ciphertext)` or `None` | At nightly-2026.10.30-de16f3c Aeneas cannot translate the closure, which returns a borrow of a field of its argument ("Can't end abstraction 3 as it is set as non-endable") | The closure form translates |
| `protocol-state_session-archive_current_state_inner` | `self.previous_sessions.insert(0, …)` → `push` when the list is empty, `insert(0, …)` otherwise; the session is encoded first, as before | The pinned library model of `Vec::insert` fails at index `len`, where Rust appends (see [Known model defects](#known-model-defects)) | The library models `insert` at index `len` as an append |

### Outside `rust/`

The root `Cargo.toml` adds `exclude = [".aeneas"]`, so Cargo does not treat the work copy in `.aeneas/work/` as part of the repository's workspace.

The helper `log_public_key_trailing_bytes` (in core's `curve.rs`) is marked opaque in `aeneas-config.core.yml`, and `Core/FunsExternal.lean` defines it as `ok ()`. The helpers `log_*` (in `double_ratchet.rs`, `triple_ratchet.rs` and `protocol.rs`), `skipped_key_from_pb`, `is_bad_key_or_iv`, `decrypt_failure_message` and `is_state_decode` are marked opaque in `aeneas-config.protocol.yml`, because their bodies contain the constructs listed above. `Protocol/FunsExternal.lean` gives Lean definitions for all of them except `decrypt_failure_message` (see [Lean model choices](#lean-model-choices)), so only that message formatting stays external.

## Lean model choices

`Protocol/TypesExternal.lean` and `Protocol/FunsExternal.lean` start from the Aeneas templates. A declaration that an imported Shared/Core/Crypto module already provides is dropped and replaced by a `(dropped axiom …)` line. The remaining choices are:

| Declaration | Model | Reason |
| --- | --- | --- |
| `prost::Message::{encode, encode_to_vec, decode}` defaults; `GenericSignedPreKey::deserialize` default | `@[trait_default]` definition that calls an external indexed by the types (`….external`) | `impl_def` must unfold a default to close a trait instance; an axiom taking the instance itself cannot be unfolded. Rust coherence allows one impl per type, so indexing by types loses nothing compared with one external per impl. These bodies were already opaque on `main`. |
| `rand_core::TryRngCore::unwrap_err` default | `fun self => ok self` | rand_core 0.9.5 returns `UnwrapErr(self)`, and Aeneas models `UnwrapErr<R>` as `R` |
| `FnOnce::call_once` for `Into::into` used as a function value | `fun f x => f x` | The template prints the type without parentheses; calling a function item applies it |
| `core::num::error::TryFromIntError` (`Shared/Core.lean`) | Alias of the backend's `Aeneas.Std.core.num.error.TryFromIntError` | The backend now defines it, so a separate opaque type made the two incompatible |
| `u8::try_from(u32)` | `core.num.tryFromUScalar .U8` from the backend | The backend's checked conversion is the same operation |
| `signal_crypto::aes_cbc::{aes_256_cbc_encrypt, aes_256_cbc_decrypt}` and their error types | Reuse the crypto profile's externals and types | Protocol and Crypto share one AES-CBC model. Exact-match tweaks remove Protocol's duplicate error types and fail if their generated shape changes. |
| `spqr::{initial_state, send, recv}` | Externals | The SPQR v1.6.0 interface libsignal consumes; SPQR itself is extracted and verified in SPQR-verify |
| `triple_ratchet::{is_state_decode, is_bad_key_or_iv}` | `ok (match error with \| .StateDecode => true \| _ => false)` and the same for `BadKeyOrIv` | Exact transcription of the `matches!` bodies; the Lean inductive has no borrow problem |
| The `log_*` helpers in `double_ratchet`, `triple_ratchet` and `protocol`, and `curve::log_public_key_trailing_bytes` in Core | `ok ()` | Logging affects neither protocol state nor results |
| `Option::default` | `fun T => ok none` | The derived `Default` of `SessionStructure`, which `decode` takes as an argument, calls it. The Aeneas library does not model it |
| `String::clone` (`Core/FunsExternal.lean`) | `fun s => ok s` | The clone holds the same characters. Core's derived `Clone` of `ProtocolAddress` clones the name with it, and `session_core::require_trusted_identity` calls that `Clone` for the `UntrustedIdentity` error; Protocol uses Core's definition |
| `uuid::fmt::Hyphenated::LENGTH` (`Core/FunsExternal.lean`) | `ok 36#usize` | uuid 1.23.4 declares `pub const LENGTH: usize = 36`. `ServiceId::parse_from_service_id_string` compares the input length with it; `Uuid::try_parse`, `str::len`, `str::as_bytes` and `str::split_at` stay external |
| `PartialEq for uuid::Uuid` (`Core/FunsExternal.lean`) | `ok (decide (self.bytes = other.bytes))` | uuid 1.23.4 declares `struct Uuid([u8; 16])` with a derived `PartialEq`, which compares the 16 bytes. Core's derived equality of `ServiceId` calls it |
| `PublicKey::verify_signature` | Dropped; Core's definition is used | `session_core::verify_bundle_signatures` calls it. Core defines it over the root axiom `curve.PublicKey.verify_signature_for_multipart_message`, so no Protocol-side verifier axiom enters the closure |
| `KeyPair::generate`, `PrivateKey::public_key` | Dropped; Core's generated definitions `libsignal_core.curve.KeyPair.generate` and `libsignal_core.curve.PrivateKey.public_key` have the names that the Protocol code calls. `Core/CurveProvider.lean` makes the root names `curve.KeyPair.generate` and `curve.PrivateKey.public_key` aliases of these definitions | Core extracts both functions with their bodies. There is one constant for each Rust function, and the PQXDH statements, which use the root names, speak of the extracted definitions |
| `PrivateKey::{calculate_signature, calculate_signature_for_multipart_message}`, `PublicKey::verify_signature_for_multipart_message` | Dropped; `Core/CurveProvider.lean` makes each Protocol name an alias of Core's root axiom (`curve.PrivateKey.calculate_signature` and so on) | Core has no body for them. With the alias there is one constant for each Rust function, so a contract on Core's constant also covers the Protocol callers |
| `double_ratchet::skipped_key_from_pb` | `MessageKeyGenerator::from_pb` followed by the same `map` and `map_err` | Transcription; `InvalidSessionError` translates to `Str` |
| `Iterator::position` for slice iterators | Transcription of the loop in core's `slice/iter/macros.rs`: apply the predicate in order, stop at the first `true`, consume that element | It was an axiom, so nothing fixed which receiver chain or skipped key `find_receiver_chain_index` and `take_skipped_key` select |
| `subtle::Choice` | Structure with one `U8` field, owned by Crypto and imported by Protocol | Rust defines `struct Choice(u8)`, holding 0 or 1 |
| `subtle::ConstantTimeEq` for `u8` and `[T]`; `From<Choice> for bool` (owned by Crypto, reused by Core and Protocol) | `u8`: 1 when the bytes are equal, 0 otherwise. `[T]`: transcription of the loop (0 on different lengths, else the AND of the elementwise results). `bool`: `val != 0` | The values computed by `subtle` 2.6.1; constant-time execution is outside the model. `ConstantTimeEq for i32`, which `ConstantTimeEq for PublicKey` calls as `0.ct_eq(&1)` when the key types differ, has no model (`Core/FunsExternal.lean`) |
| `core::slice::{first_chunk, split_last_chunk}` | Definitions with `List.take` and `List.drop` | The Aeneas library does not model them; the definitions follow the core library's documented results |
| `<Box<T, A> as AsRef<T>>::as_ref` | `fun x => ok x` | The `alloc` body returns `self`, a borrow of the boxed value with no failing path, and Aeneas models both `Box<T, A>` and `&T` as `T`. The allocator type parameter stays in the signature |
| `<Vec<T, A> as AsRef<[T]>>::as_ref` | `fun v => ok (alloc.vec.Vec.deref v)` | The `alloc` body returns `self`, deref-coerced to the slice of the elements; the library's `Vec.deref` gives that slice |
| `<Box<[T], A> as Clone>::clone` | `BoxSlice.cloneElems`, a private helper in the same file, clones the elements from the first to the last and returns the first failure | The `alloc` body clones the allocator, then clones the elements from the first to the last into a new box (`to_vec_in`, `into_boxed_slice`), so the first failing clone ends it. The library's `Slice.clone` runs the clones from the last element to the first, so the definition does not use it. For a type with a trivial clone, such as `u8`, `to_vec_in` copies the elements instead, which gives the same values. Aeneas models `Box<[T], A>` as `Slice T` with no allocator value, so only the element clones are modelled, with their failures. The `Clone` instance of `A` stays in the signature, unused |
| `<PhantomData<T> as Clone>::clone` | `fun x => ok x` | The `core` body returns `*self` |
| `triple_ratchet::decrypt_failure_message` | External | String formatting, as for `format!` elsewhere |

`OutgoingTripleRatchet::{from_session_state, encrypt}` and `TripleRatchet::{from_session_state, decrypt}` are transparent. Their Lean bodies contain the SPQR calls, the mixing of chain and SPQR keys, MAC verification, AES-CBC, error classification, and the order in which ratchet and SPQR state is committed. `SignalMessage::{compute_mac, verify_mac, verify_mac_with_addresses}` are transparent as well, so the MAC is computed and compared in translated code; HMAC-SHA256 (`hmac_sha256_parts`) is the remaining external. `RatchetState::{consume_message_key, take_skipped_key, find_receiver_chain_index}`, which `decrypt` calls, are transparent; `MessageKeyGenerator::from_pb` stays external.

## Own code without a body

This section lists functions of libsignal's own code that the extraction keeps without a body, with the reason. The list is not complete: the configuration comments give the reasons for the other opaque items.

| Item | Configuration | Reason | Layer | Translator revisions |
| --- | --- | --- | --- | --- |
| `crypto::hkdf_sha256`, the helper that `protocol-crypto-hkdf_sha256` adds | `opaque` | Its body is one call, `hkdf::Hkdf::<Sha256>::new(salt, input_key_material).expand(info, output)`, into the outside crate `hkdf`, whose generic-array associated types Charon cannot lift under `--preset=aeneas` (patch header). It is the HKDF-SHA256 primitive boundary | `charon` | not recorded |
| `impl prost::Message` for `SessionStructure` and the messages it contains (`Chain`, `ChainKey`, `MessageKey`, `PendingPreKey`, `PendingKyberPreKey`), generated by `prost-build` from `proto/storage.proto` | `opaque`, through the four `proto` Message patterns | With `include` lines on their methods, Aeneas fails: first "Unimplemented" on the `FnOnce` instance of `<u32 as Default>::default`, which the generated code passes as a function value, then "Internal error: please file an issue" | `aeneas` | Aeneas `de16f3cf877976e966906dc890f63dcb418884fa`, Charon `373d84044d80f6eb44285c2c349bae1453f5b6ca` |

## Known model defects

### `Vec::insert` at the end of a vector

The pinned Aeneas library models `Vec::insert(i, x)` as failing with `arrayOutOfBounds` when `i = len`; Rust appends in that case, and its index check panics only when `i > len` ([aeneas#1288](https://github.com/AeneasVerif/aeneas/issues/1288), still open after the partial fix in #1302). `insert` first rejects an index greater than `len`. For a valid index it then grows a full vector, and that can still panic with "capacity overflow", or call `handle_alloc_error` when the allocator fails. `RatchetState::store_skipped_key` inserts at index 0, so its Lean model fails on an empty vector, for the first skipped message key of a receiver chain, where Rust succeeds. Proofs about that path need the corrected model. In-order delivery does not call `store_skipped_key`.

`SessionRecord::archive_current_state_inner` inserts at index 0 as well, so without the patch its Lean model fails when the record has a current session and no previous sessions, where Rust succeeds. That case is reached through `promote_state`, which `process_prekey_impl` (called by `process_prekey`) and `process_prekey_bundle` call for each new session, through `promote_old_session` when it promotes the only stored session, and through `archive_current_state`. The translation patch `protocol-state_session-archive_current_state_inner` calls `push` in that case, so its Lean model agrees with Rust.

## Known warnings

### `inout::inout::InOut` — region parameter warning

Aeneas warns: "Found an unknown type declaration with region parameters: as we can not know whether the regions are used in mutable borrows or not the extracted code may be incorrect."

`InOut<'inp, 'out, T>` is from the RustCrypto `inout` crate, used by the `cipher` crate for in-place block cipher operations. It appears in the LLBC because `ctr::Ctr32BE<Aes256>` (wrapped by our `Aes256Ctr32`) implements `cipher::BlockBackend`, whose `proc_block` method signature references `InOut`.

Currently all functions that use `InOut` are opaque, so the warning is harmless — Aeneas never needs to model its borrow semantics. It cannot be excluded from the LLBC without breaking the cipher trait chain.

When we later want transparent functions that use `InOut`, this will need to be resolved upstream in Aeneas (either by supporting region analysis for foreign types, or by allowing manual annotation of region usage).
