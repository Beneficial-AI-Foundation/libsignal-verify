import Aeneas
import Libsignal.Translated.Crypto.Types
open Aeneas Aeneas.Std Result ControlFlow Error
open signal_crypto

axiom aes_cbc.aes_256_cbc_encrypt :
  Slice Std.U8 → Slice Std.U8 → Slice Std.U8 →
  Result (core.result.Result (alloc.vec.Vec Std.U8) aes_cbc.EncryptionError)

axiom aes_cbc.aes_256_cbc_decrypt :
  Slice Std.U8 → Slice Std.U8 → Slice Std.U8 →
  Result (core.result.Result (alloc.vec.Vec Std.U8) aes_cbc.DecryptionError)
