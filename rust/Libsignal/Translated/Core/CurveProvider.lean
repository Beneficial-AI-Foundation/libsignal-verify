import Libsignal.Translated.Core.Funs

open Aeneas Aeneas.Std

noncomputable abbrev libsignal_core.curve.PrivateKey.calculate_agreement :=
  _root_.curve.PrivateKey.calculate_agreement

-- Core defines these two functions; the root names are aliases of them.
noncomputable abbrev _root_.curve.KeyPair.generate :=
  @libsignal_core.curve.KeyPair.generate

noncomputable abbrev _root_.curve.PrivateKey.public_key :=
  libsignal_core.curve.PrivateKey.public_key

noncomputable abbrev libsignal_core.curve.PrivateKey.calculate_signature :=
  @_root_.curve.PrivateKey.calculate_signature

noncomputable abbrev libsignal_core.curve.PrivateKey.calculate_signature_for_multipart_message :=
  @_root_.curve.PrivateKey.calculate_signature_for_multipart_message

noncomputable abbrev libsignal_core.curve.PublicKey.verify_signature_for_multipart_message :=
  _root_.curve.PublicKey.verify_signature_for_multipart_message
