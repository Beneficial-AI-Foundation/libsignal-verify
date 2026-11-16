import Verso
import VersoManual
import VersoBlueprint
import LibsignalVerifyBlueprint.Code
import Protocols.ToVCVio.CryptoFoundations.AKE.UAKE.Defs
import VCVio.OracleComp.OracleSpec
import ToMathlib.MeasureTheory.Measure.Bool
import Cslib.Foundations.Data.PFunctor.Free

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "Spike" =>

::::definition "uake_scheme" (lean := "AKE.UAKE.Scheme")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.Scheme -docstrings
Let $`m` be a monad. A UAKE scheme over $`m` consists of a round count, a setup
computation that samples long-term keys for the parties $`U` and $`T`, and the
two parties.
:::
::::

::::definition "oracle_spec_to_pfunctor" (lean := "OracleSpec.toPFunctor")
:::LibsignalVerifyBlueprint.pair OracleSpec.toPFunctor -docstrings
An oracle specification is a family of answer types $`R : I \to \mathrm{Type}`,
indexed by the queries $`I`. Its polynomial functor is
$`P(X) = \sum_{i : I} X^{R(i)}`.
:::
::::

::::definition "free_monad" (lean := "PFunctor.FreeM")
:::LibsignalVerifyBlueprint.pair PFunctor.FreeM -docstrings
The free monad on a polynomial functor $`P` is the least solution of
$`T(X) \cong X + P(T(X))`.
:::
::::

::::definition "bool_bias" (lean := "MeasureTheory.Measure.boolBias")
:::LibsignalVerifyBlueprint.pair MeasureTheory.Measure.boolBias -docstrings
Let $`\mu` be a measure on the Booleans. Its bias is
$`|\mu\{\mathrm{true}\} - \mu\{\mathrm{false}\}|`.
:::
::::
