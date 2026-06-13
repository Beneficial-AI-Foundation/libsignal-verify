-- [libsignal_protocol]: external types.
import Aeneas
import Translation.Shared
import Translation.Core.Funs
import Translation.Crypto.Funs
open Aeneas Aeneas.Std Result ControlFlow Error
set_option linter.dupNamespace false
set_option linter.hashCommand false
set_option linter.unusedVariables false
set_option linter.style.longLine false
set_option linter.style.setOption false
set_option linter.style.whitespace false

/- You can set the `maxHeartbeats` value with the `-max-heartbeats` CLI option -/
set_option maxHeartbeats 1000000

/- You can set the `maxRecDepth` value with the `-max-recdepth` CLI option -/
set_option maxRecDepth 2048

-- (dropped axiom core.num.error.TryFromIntError; provided by an imported sibling lib)

/-- [core::time::Duration]
    Source: '/rustc/library/core/src/time.rs', lines 81:0-81:19
    Name pattern: [core::time::Duration]
    Visibility: public -/
@[rust_type "core::time::Duration"]
axiom core.time.Duration : Type

/-- [std::path::PathBuf]
    Source: '/rustc/library/std/src/path.rs', lines 1214:0-1214:18
    Name pattern: [std::path::PathBuf]
    Visibility: public -/
@[rust_type "std::path::PathBuf"]
axiom std.path.PathBuf : Type

/-- [std::path::Path]
    Source: '/rustc/library/std/src/path.rs', lines 2357:0-2357:15
    Name pattern: [std::path::Path]
    Visibility: public -/
@[rust_type "std::path::Path"]
axiom std.path.Path : Type

/-- [std::path::Display]
    Source: '/rustc/library/std/src/path.rs', lines 3727:0-3727:22
    Name pattern: [std::path::Display]
    Visibility: public -/
@[rust_type "std::path::Display"]
axiom std.path.Display : Type

/-- [std::time::SystemTime]
    Source: '/rustc/library/std/src/time.rs', lines 250:0-250:21
    Name pattern: [std::time::SystemTime]
    Visibility: public -/
@[rust_type "std::time::SystemTime"]
axiom std.time.SystemTime : Type

/-- [std::time::SystemTimeError]
    Source: '/rustc/library/std/src/time.rs', lines 272:0-272:26
    Name pattern: [std::time::SystemTimeError]
    Visibility: public -/
@[rust_type "std::time::SystemTimeError"]
axiom std.time.SystemTimeError : Type

/-- [alloc::collections::vec_deque::iter::Iter]
    Source: '/rustc/library/alloc/src/collections/vec_deque/iter.rs', lines 13:0-13:26
    Name pattern: [alloc::collections::vec_deque::iter::Iter]
    Visibility: public -/
@[rust_type "alloc::collections::vec_deque::iter::Iter"]
axiom alloc.collections.vec_deque.iter.Iter (T : Type) : Type

/-- [alloc::collections::vec_deque::VecDeque]
    Source: '/rustc/library/alloc/src/collections/vec_deque/mod.rs', lines 104:0-107:1
    Name pattern: [alloc::collections::vec_deque::VecDeque]
    Visibility: public -/
@[rust_type "alloc::collections::vec_deque::VecDeque"]
axiom alloc.collections.vec_deque.VecDeque (T : Type) (A : Type) : Type

/-- [bytes::buf::uninit_slice::UninitSlice]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/bytes-1.11.1/src/buf/uninit_slice.rs', lines 22:0-22:22
    Name pattern: [bytes::buf::uninit_slice::UninitSlice]
    Visibility: public -/
@[rust_type "bytes::buf::uninit_slice::UninitSlice"]
axiom bytes.buf.uninit_slice.UninitSlice : Type

-- (dropped axiom libsignal_core.address.SpecificServiceId; provided by an imported sibling lib)

-- (dropped axiom libsignal_core.address.DeviceId; provided by an imported sibling lib)

-- (dropped axiom libsignal_core.address.ProtocolAddress; provided by an imported sibling lib)

-- (dropped axiom libsignal_core.curve.PublicKey; provided by an imported sibling lib)

-- (dropped axiom libsignal_core.curve.PrivateKey; provided by an imported sibling lib)

/-- [prost::error::DecodeError]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/prost-0.14.1/src/error.rs', lines 17:0-17:22
    Name pattern: [prost::error::DecodeError]
    Visibility: public -/
@[rust_type "prost::error::DecodeError"]
axiom prost.error.DecodeError : Type

/-- [prost::error::EncodeError]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/prost-0.14.1/src/error.rs', lines 90:0-90:22
    Name pattern: [prost::error::EncodeError]
    Visibility: public -/
@[rust_type "prost::error::EncodeError"]
axiom prost.error.EncodeError : Type

/-- [rand_core#1::os::OsError]
    Source: '/cargo/registry/src/index.crates.io-1949cf8c6b5b557f/rand_core-0.9.3/src/os.rs', lines 51:0-51:18
    Name pattern: [rand_core#1::os::OsError]
    Visibility: public -/
@[rust_type "rand_core#1::os::OsError"]
axiom rand_core_1.os.OsError : Type

-- (dropped axiom uuid.Uuid; provided by an imported sibling lib)

/-- [libsignal_protocol::state::session::{libsignal_protocol::state::session::SessionRecord}::previous_session_states::closure]
    Source: 'rust/protocol/src/state/session.rs', lines 816:42-820:9 -/
axiom state.session.SessionRecord.previous_session_states.closure : Type
