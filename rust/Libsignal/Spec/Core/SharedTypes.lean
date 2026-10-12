import Libsignal.Translated.Core.Types
import Libsignal.Translated.Protocol.Types

example (Self : Type) : libsignal_core.rand.rng.Rng Self = _root_.rand.rng.Rng Self := rfl

example (T : Type) : libsignal_core.derive_more.convert.try_from.TryFromReprError T =
    _root_.derive_more.convert.try_from.TryFromReprError T := rfl

example (Self : Type) : libsignal_protocol.rand_1.rng.Rng Self = _root_.rand.rng.Rng Self := rfl
