//
// Copyright 2020-2022 Signal Messenger, LLC.
// SPDX-License-Identifier: AGPL-3.0-only
//

//! Interfaces in [traits] and reference implementations in [inmem] for various mutable stores.

#![warn(missing_docs)]

// The async store traits + their in-memory impls are gated out during extraction:
// charon's hax frontend panics on the `#[async_trait]` store traits when
// `--start-from-pub` roots them. Direction/IdentityChange are plain enums that kept
// code (sealed_sender crypto) depends on, so they stay.
#[cfg(not(feature = "extraction"))]
mod inmem;
mod traits;

#[cfg(not(feature = "extraction"))]
pub use inmem::{
    InMemIdentityKeyStore, InMemKyberPreKeyStore, InMemPreKeyStore, InMemSenderKeyStore,
    InMemSessionStore, InMemSignalProtocolStore, InMemSignedPreKeyStore,
};
pub use traits::{Direction, IdentityChange};
#[cfg(not(feature = "extraction"))]
pub use traits::{
    IdentityKeyStore, KyberPreKeyStore, PreKeyStore, ProtocolStore, SenderKeyStore, SessionStore,
    SignedPreKeyStore,
};
