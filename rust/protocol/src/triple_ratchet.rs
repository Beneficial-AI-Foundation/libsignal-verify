//
// Copyright 2026 Signal Messenger, LLC.
// SPDX-License-Identifier: AGPL-3.0-only
//

//! The Triple Ratchet: Double Ratchet + SPQR combined into a single
//! encrypt/decrypt interface.
//!
//! Handles MAC computation/verification and AES-CBC encryption/decryption.
//!
//! The session management layer treats this as an opaque box: give it
//! plaintext, get ciphertext; give it ciphertext, get plaintext. Identity
//! checking, session selection, pre-key handling, and storage are NOT
//! this layer's concern.

use rand::{CryptoRng, Rng};

use crate::double_ratchet::RatchetState;
use crate::ratchet::ChainKey;
use crate::session_management::CurrentOrPrevious;
use crate::state::SessionState;
use crate::{
    CiphertextMessageType, IdentityKey, KeyPair, ProtocolAddress, Result, SignalMessage,
    SignalProtocolError,
};

// Named messages: Aeneas loses a string literal returned from a closure or an
// early return ("There should be no bottoms in the value").
const VERSION_DOES_NOT_FIT_IN_U8: &str = "version does not fit in u8";
const ENCRYPT_OPERATION: &str = "encrypt";
const DECRYPT_OPERATION: &str = "decrypt";
const INVALID_SENDER_CHAIN_MESSAGE_KEYS: &str = "invalid sender chain message keys";
const INVALID_RECEIVER_CHAIN_MESSAGE_KEYS: &str = "invalid receiver chain message keys";

// Logging helpers: Aeneas fails on `log!` expansions, so the extraction treats
// these as opaque effects. Level and message are unchanged.
fn log_sender_chain_corrupt(remote_address: &ProtocolAddress) {
    log::error!("session state corrupt for {remote_address}");
}

fn log_receiver_chain_corrupt(
    current_or_previous: CurrentOrPrevious,
    sender_address: &ProtocolAddress,
) {
    log::warn!("{current_or_previous} session state corrupt for {sender_address}");
}

// Pair the addresses in a helper: Aeneas cannot end the borrows of a closure
// returning two references, nor join the branches of an inline match.
fn address_pair<'a>(
    local_address: Option<&'a ProtocolAddress>,
    remote_address: &'a ProtocolAddress,
) -> Option<(&'a ProtocolAddress, &'a ProtocolAddress)> {
    match local_address {
        Some(addr) => Some((addr, remote_address)),
        None => None,
    }
}

// Inspect `DecryptionError` only in helpers: its `BadCiphertext(&'static str)`
// field comes from an opaque call, and Aeneas has no loan for that static
// borrow when the variant is expanded or the field copied.
fn is_bad_key_or_iv(error: &signal_crypto::DecryptionError) -> bool {
    matches!(error, signal_crypto::DecryptionError::BadKeyOrIv)
}

// Callers pass only `BadCiphertext` (the other variant is tested first).
fn decrypt_failure_message(error: signal_crypto::DecryptionError) -> String {
    match error {
        signal_crypto::DecryptionError::BadCiphertext(msg) => format!("failed to decrypt: {msg}"),
        signal_crypto::DecryptionError::BadKeyOrIv => {
            unreachable!("callers pass only BadCiphertext")
        }
    }
}

// Test the variant in a helper: matching `spqr::Error` expands its
// `InvalidParams(&'static str)` variant, which Aeneas cannot translate.
fn is_state_decode(error: &spqr::Error) -> bool {
    matches!(error, spqr::Error::StateDecode)
}

/// Sender-side Triple Ratchet session.
///
/// This is intentionally narrower than [`TripleRatchet`]: encrypt only
/// depends on the current sender chain, SPQR state, identities, and metadata.
/// It does not deserialize receiver chains, so corrupt cold receiver-chain
/// state does not block sending.
///
/// # Ownership contract
///
/// [`from_session_state`](Self::from_session_state) **moves** the PQ ratchet
/// state out of the session (via [`SessionState::take_pq_ratchet_state`]),
/// leaving it temporarily invalid. The caller must either call
/// [`apply_to_session_state`](Self::apply_to_session_state) on success, or
/// discard the `SessionState` entirely.
pub(crate) struct OutgoingTripleRatchet {
    sender_ratchet_key: KeyPair,
    sender_chain_key: ChainKey,
    previous_counter: u32,
    pqr_state: spqr::SerializedState,
    session_version: u8,
    local_identity_key: IdentityKey,
    remote_identity_key: IdentityKey,
}

impl OutgoingTripleRatchet {
    // `session_state`, not `state`: a parameter named like the `state` module
    // shadows it in the generated Lean (aeneas#1098).
    pub(crate) fn from_session_state(session_state: &mut SessionState) -> Result<Self> {
        let sender_ratchet_key = KeyPair {
            public_key: session_state.sender_ratchet_key()?,
            private_key: session_state.sender_ratchet_private_key()?,
        };
        let sender_chain_key = session_state.get_sender_chain_key()?;
        let pqr_state = session_state.take_pq_ratchet_state();
        let session_version: u8 = session_state.session_version()?.try_into().map_err(|_| {
            SignalProtocolError::InvalidSessionStructure(VERSION_DOES_NOT_FIT_IN_U8)
        })?;
        let local_identity_key = session_state.local_identity_key()?;
        let remote_identity_key = session_state.remote_identity_key()?.ok_or(
            SignalProtocolError::InvalidSessionStructure("missing remote identity key"),
        )?;

        Ok(Self {
            sender_ratchet_key,
            sender_chain_key,
            previous_counter: session_state.previous_counter(),
            pqr_state,
            session_version,
            local_identity_key,
            remote_identity_key,
        })
    }

    pub(crate) fn apply_to_session_state(self, state: &mut SessionState) {
        state.set_sender_chain_key(&self.sender_chain_key);
        state.set_pq_ratchet_state(self.pqr_state);
    }

    pub(crate) fn encrypt<R: Rng + CryptoRng>(
        &mut self,
        plaintext: &[u8],
        local_address: Option<&ProtocolAddress>,
        remote_address: &ProtocolAddress,
        csprng: &mut R,
    ) -> Result<SignalMessage> {
        let spqr::Send {
            state: new_pqr_state,
            key: pqr_key,
            msg: pqr_msg,
        } = spqr::send(&self.pqr_state, csprng).map_err(|e| {
            SignalProtocolError::InvalidState(
                ENCRYPT_OPERATION,
                format!("post-quantum ratchet send error: {e}"),
            )
        })?;

        let message_keys = self.sender_chain_key.message_keys().generate_keys(pqr_key);

        let ctext = signal_crypto::aes_256_cbc_encrypt(
            plaintext,
            message_keys.cipher_key(),
            message_keys.iv(),
        )
        .map_err(|_| {
            log_sender_chain_corrupt(remote_address);
            SignalProtocolError::InvalidSessionStructure(INVALID_SENDER_CHAIN_MESSAGE_KEYS)
        })?;

        let addresses = address_pair(local_address, remote_address);

        let message = SignalMessage::new(
            self.session_version,
            message_keys.mac_key(),
            addresses,
            self.sender_ratchet_key.public_key,
            self.sender_chain_key.index(),
            self.previous_counter,
            &ctext,
            &self.local_identity_key,
            &self.remote_identity_key,
            &pqr_msg,
        )?;

        self.sender_chain_key = self.sender_chain_key.next_chain_key();
        self.pqr_state = new_pqr_state;

        Ok(message)
    }

    pub(crate) fn session_version(&self) -> u8 {
        self.session_version
    }

    pub(crate) fn local_identity_key(&self) -> &IdentityKey {
        &self.local_identity_key
    }
}

/// A Triple Ratchet session combining Double Ratchet and SPQR.
///
/// Constructed from a [`SessionState`], this extracts the cryptographic
/// state needed for decrypt into typed fields. After a successful
/// operation, call [`apply_to_session_state`](Self::apply_to_session_state)
/// to write the updated state back.
///
/// # Ownership contract
///
/// [`from_session_state`](Self::from_session_state) **moves** the receiver
/// chains and PQ ratchet state out of the session, leaving it temporarily invalid.
/// The caller must either:
/// - Call [`apply_to_session_state`](Self::apply_to_session_state) on success, or
/// - Discard the `SessionState` (e.g., it was a clone for trial decrypt).
pub(crate) struct TripleRatchet {
    ratchet: RatchetState,
    pqr_state: spqr::SerializedState,
    local_identity_key: IdentityKey,
    remote_identity_key: IdentityKey,
}

impl TripleRatchet {
    /// Construct from a [`SessionState`] by extracting crypto state.
    ///
    /// This moves receiver chains and PQ ratchet state out of `state`.
    /// See the [ownership contract](Self#ownership-contract) for details.
    ///
    /// Fails if the session is missing required fields (root key, identity
    /// keys, etc.). The caller should map the error appropriately for the
    /// context (e.g., "no session available to decrypt").
    // `session_state`, not `state`: see `OutgoingTripleRatchet::from_session_state`.
    pub(crate) fn from_session_state(
        session_state: &mut SessionState,
        self_session: bool,
    ) -> Result<Self> {
        let ratchet = session_state.take_ratchet_state(self_session)?;
        let pqr_state = session_state.take_pq_ratchet_state();
        let local_identity_key = session_state.local_identity_key()?;
        let remote_identity_key = session_state.remote_identity_key()?.ok_or(
            SignalProtocolError::InvalidSessionStructure("missing remote identity key"),
        )?;

        Ok(Self {
            ratchet,
            pqr_state,
            local_identity_key,
            remote_identity_key,
        })
    }

    /// Write the updated crypto state back to a [`SessionState`].
    ///
    /// Only call this after a successful decrypt — this is how we ensure
    /// no state pollution on failure.
    pub(crate) fn apply_to_session_state(self, state: &mut SessionState) {
        state.apply_ratchet_state(self.ratchet);
        state.set_pq_ratchet_state(self.pqr_state);
    }

    // -- Decrypt -------------------------------------------------------

    /// Decrypt a [`SignalMessage`] to plaintext.
    ///
    /// Performs DR chain key derivation, SPQR key derivation, MAC
    /// verification, and AES-CBC decryption. Ratchet and SPQR state are
    /// only committed on success — a failed MAC or decryption leaves this
    /// session unchanged.
    ///
    /// `original_message_type` is used for error classification only
    /// (PreKey vs Whisper).
    pub(crate) fn decrypt<R: Rng + CryptoRng>(
        &mut self,
        sender_address: &ProtocolAddress,
        recipient_address: &ProtocolAddress,
        ciphertext: &SignalMessage,
        original_message_type: CiphertextMessageType,
        current_or_previous_for_logging: CurrentOrPrevious,
        csprng: &mut R,
    ) -> Result<Vec<u8>> {
        // DR: ensure we have a receiver chain, then consume the message key
        let their_ephemeral = ciphertext.sender_ratchet_key();
        let counter = ciphertext.counter();
        let chain_key = self
            .ratchet
            .ensure_receiver_chain(their_ephemeral, csprng)?;
        let message_key_gen = self.ratchet.consume_message_key(
            their_ephemeral,
            chain_key,
            counter,
            original_message_type,
            &sender_address.to_string(),
        )?;

        // SPQR recv — compute key but don't commit state yet
        let spqr::Recv {
            state: new_pqr_state,
            key: pqr_key,
        } = spqr::recv(&self.pqr_state, ciphertext.pq_ratchet()).map_err(|e| {
            if is_state_decode(&e) {
                SignalProtocolError::InvalidState(
                    DECRYPT_OPERATION,
                    format!("post-quantum ratchet error: {e}"),
                )
            } else {
                SignalProtocolError::InvalidMessage(
                    original_message_type,
                    format!("post-quantum ratchet error: {e}"),
                )
            }
        })?;

        // Derive final message keys by mixing DR chain key with SPQR key
        let message_keys = message_key_gen.generate_keys(pqr_key);

        // MAC verification
        let mac_valid = ciphertext.verify_mac_with_addresses(
            sender_address,
            recipient_address,
            &self.remote_identity_key,
            &self.local_identity_key,
            message_keys.mac_key(),
        )?;
        if !mac_valid {
            return Err(SignalProtocolError::InvalidMessage(
                original_message_type,
                "MAC verification failed".to_owned(),
            ));
        }

        // AES-CBC decrypt
        let ptext = match signal_crypto::aes_256_cbc_decrypt(
            ciphertext.body(),
            message_keys.cipher_key(),
            message_keys.iv(),
        ) {
            Ok(ptext) => ptext,
            // The guard tests the variant without expanding the error here.
            Err(decryption_error) if is_bad_key_or_iv(&decryption_error) => {
                log_receiver_chain_corrupt(current_or_previous_for_logging, sender_address);
                return Err(SignalProtocolError::InvalidSessionStructure(
                    INVALID_RECEIVER_CHAIN_MESSAGE_KEYS,
                ));
            }
            Err(decryption_error) => {
                return Err(SignalProtocolError::InvalidMessage(
                    original_message_type,
                    decrypt_failure_message(decryption_error),
                ));
            }
        };

        // Commit SPQR state only after all verification passed
        self.pqr_state = new_pqr_state;

        Ok(ptext)
    }
}
