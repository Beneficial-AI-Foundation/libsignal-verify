import Verso
import VersoManual
import VersoBlueprint
import LibsignalVerifyBlueprint.Code
import Protocols.ToVCVio.CryptoFoundations.AKE.UAKE.Party
import Protocols.ToVCVio.CryptoFoundations.AKE.UAKE.Transcript
import Protocols.ToVCVio.CryptoFoundations.AKE.UAKE.Defs
import Protocols.ToVCVio.CryptoFoundations.AKE.UAKE.Runtime
import Protocols.ToVCVio.CryptoFoundations.AEAD
import Protocols.ToVCVio.CryptoFoundations.HardnessAssumptions.DiffieHellman
import Protocols.ToVCVio.CryptoFoundations.JointSignatureAlg
import Protocols.ToVCVio.CryptoFoundations.KEMCorrectness
import VCVio.CryptoFoundations.PRF
import VCVio.CryptoFoundations.KeyEncapMech

open Verso.Genre Verso.Genre.Manual Informal

#doc (Manual) "UAKE and the primitives" =>
%%%
tag := "uake"
%%%

The PQXDH theorems of the next chapter state that PQXDH is a secure unilaterally
authenticated key exchange (UAKE). Their hypotheses are security notions for the primitives
that PQXDH uses: a signature scheme, a Diffie-Hellman group, an AEAD scheme, a pseudorandom
function and a KEM. This chapter states the UAKE model and these notions. Each box states a
definition or a theorem as the Lean formalises it, beside the Lean code. After the box we
explain the encoding, give the definition from the literature, and list the points where the
two differ.

The UAKE model of this chapter, the AEAD definitions and the gap Diffie-Hellman definitions
come from Galois's
[libsignal-docs-and-models](https://github.com/GaloisInc/libsignal-docs-and-models)
(Galois Inc., author Ben Hamlin), at commit `e82e566`. Galois's documentation of their
model is at [galoisinc.github.io/libsignal-docs-and-models](https://galoisinc.github.io/libsignal-docs-and-models/).
This repository changes some of the ported definitions. For example, well-formedness also
asks that the outputs of a party be pure, and the IND-CPA challenge takes two messages of the
same length. The four AEAD reduction theorems are restated and proved here. The conditions
of honest completion, coherence and admissibility, and the theorem that the canonical
runtime is coherent, come from Devon Tuma's
[VCV-io pull request #476](https://github.com/Verified-zkEVM/VCVio/pull/476). The PRF and
KEM definitions come from VCV-io, except the KEM correctness error, which comes from the
Beneficial AI Foundation's
[secure-messaging](https://github.com/Beneficial-AI-Foundation/secure-messaging). The joint
signature game is new in this repository.

The chapter uses the following sources:

* Y. Dodis and D. Fiore, [Unilaterally-Authenticated Key Exchange](https://eprint.iacr.org/2017/109),
  Financial Cryptography 2017. We cite it as DF.
* D. Boneh and V. Shoup, [A Graduate Course in Applied Cryptography](https://crypto.stanford.edu/~dabo/cryptobook/BonehShoup_0_6.pdf),
  version 0.6. Page numbers are the printed page numbers.
* R. Fiedler and F. Günther, [Security Analysis of Signal's PQXDH Handshake](https://doi.org/10.1007/978-3-031-91823-0_5),
  PKC 2025. Page numbers refer to version 2.1 of the full version.
* J. Brendel, M. Fischlin, F. Günther and C. Janson,
  [PRF-ODH: Relations, Instantiations, and Impossibility Results](https://eprint.iacr.org/2017/517),
  CRYPTO 2017.

One difference holds for every notion in this chapter. A definition in the literature
quantifies over efficient adversaries and bounds their running time and number of queries.
The Lean games quantify over all adversaries and count neither. A hypothesis that bounds the
advantage of every adversary is therefore much stronger than the assumption in the
literature. For every correct instantiation, the computational hypotheses of the PQXDH
theorems hold only with bounds close to $`1`, so the bounds that these theorems state are
trivial.
[Issue #41](https://github.com/Beneficial-AI-Foundation/libsignal-verify/issues/41) tracks this.

# Unilaterally authenticated key exchange

A UAKE protocol runs between two parties. The party $`T` holds a long-term secret key and is
authenticated. The party $`U` holds only the public key of $`T` and is not authenticated.
At the end of a run, each party outputs a session key or the symbol $`\bot`.

## Parties

A party of a protocol receives an input, may send a first message, and then answers each
message it receives until it stops. We model it as a state machine whose effects live in a
monad, so that the same definition covers probabilistic parties and other semantics.

::::definition "uake_party" (lean := "AKE.UAKE.Party")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.Party -docstrings
Let $`m` be a monad, and let $`\mathrm{In}`, $`W` and $`\mathrm{Out}` be types. A _party_
with inputs in $`\mathrm{In}`, messages in $`W` and outputs in $`\mathrm{Out}` consists of
a type $`S` of states and three maps:

* an initialisation $`\mathrm{init} : \mathrm{In} \to m(S \times (W + \{\ast\}))`, which
  gives a first state and either a first message or the value $`\ast`, if the party waits
  for the other party to speak first;
* a step map
  $`\mathrm{step} : S \times W \to m\big((S \times W \times \{0, 1\}) + S + \{\mathsf{rej}\}\big)`.
  On a message $`w` in state $`s`, the party either accepts $`w`, replies with a message
  $`w'` and moves to a state $`s'`, with a flag $`\mathrm{done}` that is $`1` if this is its
  last step; or completes and moves to a state $`s'` without a reply; or rejects $`w`;
* an output map $`\mathrm{output} : S \to m(\mathrm{Out} + \{\ast\})`, where the value
  $`\ast` means that the party has no output yet.
:::
::::

In Lean, the results of `init` and `step` are the inductive types `Party.InitResult`, with
the constructors `speakFirst` and `waitForMsg`, and `Party.StepResult`, with the
constructors `acceptAndSend`, `complete` and `reject`. The flag $`\mathrm{done}` is a
Boolean. The value $`\ast` of `init` and of `output` is `none`. A party of a UAKE scheme
has `Out = Option K` for a type `K` of session keys, so `output` returns a value of type
`Option (Option K)`: the outer `none` is $`\ast`, and the inner `none` is the output
$`\bot`.

DF model a party as an interactive algorithm (DF, Section 3, pp. 7 and 8). The definition
above makes a party a Mealy machine with an output map: the reply to a message depends on
the current state and on the message.

Two conditions make the output of a party well behaved. The output should appear exactly
when the party finishes, and reading it should have no effect. The first condition speaks
about the possible results of a computation, so it needs a monad with a support.

::::definition "uake_outputs_only_at_completion" (lean := "AKE.UAKE.Party.OutputsOnlyAtCompletion") (uses := "uake_party")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.Party.OutputsOnlyAtCompletion -docstrings
Let $`m` be a monad with a support, which assigns to each computation $`x` in $`m` the set
$`\mathrm{supp}(x)` of its possible results, and let $`P` be a party over $`m`. We say that
$`P` _outputs only at completion_ if the following three conditions hold.

1. For every input $`i` and every $`(s, w_0) \in \mathrm{supp}(\mathrm{init}(i))`, every
   element of $`\mathrm{supp}(\mathrm{output}(s))` is $`\ast`.
2. For all states $`s`, $`s'` and every message $`w` such that the completion with state
   $`s'` lies in $`\mathrm{supp}(\mathrm{step}(s, w))`, no element of
   $`\mathrm{supp}(\mathrm{output}(s'))` is $`\ast`.
3. For all states $`s`, $`s'`, messages $`w`, $`w'` and $`\mathrm{done} \in \{0, 1\}` such
   that the acceptance $`(s', w', \mathrm{done})` lies in
   $`\mathrm{supp}(\mathrm{step}(s, w))`, every element $`o` of
   $`\mathrm{supp}(\mathrm{output}(s'))` satisfies $`o \neq \ast` if and only if
   $`\mathrm{done} = 1`.
:::
::::

In Lean, the support is `support`, which VCV-io takes from the class `MonadAttach`. The
condition does not speak about reachable states: it constrains every state that a single
call to `init` or `step` can return, from any state.

::::definition "uake_pure_output" (lean := "AKE.UAKE.Party.PureOutput") (uses := "uake_party")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.Party.PureOutput -docstrings
Let $`P` be a party over a monad $`m`, with outputs in $`\mathrm{Out}`. We say that $`P`
has _pure output_ if for every state $`s` there is a value
$`o \in \mathrm{Out} + \{\ast\}` with $`\mathrm{output}(s) = \mathrm{pure}(o)`.
:::
::::

The correctness experiment below reads both outputs after an honest run. The security
experiment reads the output of $`T` when a session finishes, and the output of $`U` after
the challenge phase. Pure outputs make these readings agree.

An honest run lets two parties exchange messages with no adversary in between. A bound on
the number of steps makes the run finite.

::::definition "uake_run_honest" (lean := "AKE.UAKE.Party.runHonest") (uses := "uake_party")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.Party.runHonest -docstrings
Let $`P` and $`Q` be parties over a monad $`m`, with messages in the same type $`W`, let
$`x` and $`y` be inputs of $`P` and $`Q`, and let $`n \in \mathbb{N}`. We define the
_honest run_ $`\mathrm{run}(P, Q, x, y, n)` to be the following computation in $`m`.

1. Run $`P.\mathrm{init}(x)` and then $`Q.\mathrm{init}(y)`. If $`P` has a first message
   $`w`, then $`P` is the sender and $`Q` the receiver of $`w`. Otherwise, if $`Q` has a
   first message $`w`, then $`Q` is the sender and $`P` the receiver. In both cases $`w`
   is sent with flag $`0`. Otherwise no message is sent and the run goes to step 3.
2. Repeat the following at most $`n` times. The receiver steps on $`w`. If it rejects, its
   state does not change and the run stops. If it completes, it moves to the new state
   and the run stops. If it accepts with reply $`w'` and flag $`\mathrm{done}`, it moves
   to the new state, and $`w'` is sent with flag $`\mathrm{done}`. If $`w` was sent with
   flag $`1`, the run stops. Otherwise $`w'` is the next message and the two parties swap
   roles.
3. Output $`P.\mathrm{output}` and $`Q.\mathrm{output}` of the final states of $`P` and
   $`Q`, and the list of all messages sent, in order.
:::
::::

In Lean, `runHonest` calls `runHonestStart`, which picks the first sender, and
`runHonestLoop`, which keeps the list of messages in reverse order. The bound $`n` is the
argument `fuel`. After a step with $`\mathrm{done} = 1` the sender is never stepped
again, just as the security experiment refuses every message to a session of $`T` whose
key is set.

## Transcripts and matching

A global clock counts the messages of an execution. Every message that a party sends or
receives gets the current time as a timestamp, and a session keeps the list of its
messages with their timestamps.

::::definition "uake_transcript" (lean := "AKE.UAKE.Transcript")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.Transcript -docstrings
Let $`W` be a type of messages. A _transcript_ with messages in $`W` is a finite list
$`\langle (M_1, t_1), \dots, (M_n, t_n) \rangle` of pairs of a message $`M_i \in W` and a
timestamp $`t_i \in \mathbb{N}`.
:::
::::

In Lean, the list is the field `entries`. The security experiment appends a pair to a
transcript with `recordOne`, which also advances the clock by one. DF define the transcript
of a session in the same way, as the list of its messages, sent and received, with their
timestamps (DF, Definition 2, p. 6).

Two sessions match when one relays the messages of the other, unchanged and in order. The
timestamps then alternate between the two transcripts.

::::definition "uake_matching" (lean := "AKE.UAKE.Matching") (uses := "uake_transcript")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.Matching -docstrings
Let $`\tau = \langle (M_1, t_1), \dots, (M_n, t_n) \rangle` and
$`\tau^* = \langle (M^*_1, t^*_1), \dots, (M^*_k, t^*_k) \rangle` be transcripts, and let
$`\beta \in \{0, 1\}`. We say that $`\tau` _matches_ $`\tau^*` with first-speaker bit
$`\beta` if $`n = k`, if $`M_i = M^*_i` for $`1 \le i \le n`, and if the sequence
$`(u_1, u'_1, u_2, u'_2, \dots, u_n, u'_n)` is strictly increasing, where
$`(u_i, u'_i) = (t_i, t^*_i)` if $`i + \beta` is even and
$`(u_i, u'_i) = (t^*_i, t_i)` otherwise.
:::
::::

For $`\beta = 1` the condition on the timestamps reads
$$`t_1 < t^*_1 < t^*_2 < t_2 < t_3 < t^*_3 < \dots,`
so the party of $`\tau` speaks first and every message is received at a later time than it
is sent. For $`\beta = 0` it reads
$$`t^*_1 < t_1 < t_2 < t^*_2 < t^*_3 < t_3 < \dots,`
and the party of $`\tau^*` speaks first. This is DF, Definition 3, p. 6. The relation is not
symmetric. In Lean, $`\beta` is the Boolean `oracleLeadsFirst`, and the function
`interleave` builds the sequence of the $`u_i` and $`u'_i`.

The security theorems for PQXDH in the next chapter do not use this matching. They use a
partnered experiment, defined there, in which two sessions are partners if they hold the same
associated data and the same key material.

::::definition "uake_ping_pong" (lean := "AKE.UAKE.pingPong") (uses := "uake_matching")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.pingPong -docstrings
Let $`\beta \in \{0, 1\}`, let $`\tau_1, \dots, \tau_q` be a list of transcripts, and let
$`\tau^*` be a transcript. We define $`\mathrm{pingPong}_\beta(\tau_1, \dots, \tau_q; \tau^*)`
to be $`1` if $`\tau_j` matches $`\tau^*` with first-speaker bit $`\beta` for some $`j`, and
$`0` otherwise.
:::
::::

In the security experiment below, $`\tau^*` is the transcript of the challenge session
with $`U`, and $`\tau_1, \dots, \tau_q` are the transcripts of the sessions that the
adversary opens with copies of $`T`. DF call an adversary _ping-pong_ if some $`\tau_i`
matches $`\tau^*` (DF, Definition 4, p. 7). A ping-pong adversary has relayed every
message of the challenge session between $`U` and one copy of $`T`, unchanged and in
order.

## Schemes and correctness

A scheme fixes the key material of the two parties and their behaviour. The party $`U`
receives the public key of $`T`, and $`T` receives its own key pair.

::::definition "uake_scheme" (lean := "AKE.UAKE.Scheme") (uses := "uake_party")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.Scheme -docstrings
Let $`m` be a monad and let $`K`, $`\mathrm{UK}`, $`\mathrm{TK}` and $`W` be types. A
_UAKE scheme_ over $`m` with key space $`K`, key inputs in $`\mathrm{UK}` and
$`\mathrm{TK}`, and messages in $`W` consists of

* a number $`r \in \mathbb{N}`,
* a computation $`\mathrm{Setup}` in $`m(\mathrm{UK} \times \mathrm{TK})`,
* a party $`U` with inputs in $`\mathrm{UK}`, messages in $`W` and outputs in
  $`K + \{\bot\}`, and
* a party $`T` with inputs in $`\mathrm{TK}`, messages in $`W` and outputs in
  $`K + \{\bot\}`.
:::
::::

In Lean, the four components are the fields `rounds`, `setup`, `U` and `T`, and the output
type $`K + \{\bot\}` is `Option K`, with `none` for $`\bot`. The definition does not tie
$`r` to the parties. The condition of well-formedness below asks that every honest run
sends exactly $`r` messages, and the security experiment reads the first speaker from the
parity of $`r`.

DF define a UAKE protocol as three algorithms (DF, Section 3, pp. 7 and 8). A setup
algorithm outputs a key pair $`(\mathrm{uk}, \mathrm{tk})` and defines the space $`K` of
session keys. The party $`U` runs on $`\mathrm{uk}`, and the party $`T` runs on
$`\mathrm{tk}`. DF assume without loss of generality that $`T` speaks last.

::::definition "uake_correct_exp" (lean := "AKE.UAKE.CorrectExp") (uses := "uake_scheme, uake_run_honest")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.CorrectExp -docstrings
Let $`\Pi = (r, \mathrm{Setup}, U, T)` be a UAKE scheme over a monad $`m` with key space
$`K`. We define the _correctness experiment_ $`\mathsf{Corr}(\Pi)` to be the following
computation in $`m` with output in $`\{0, 1\}`. Run $`\mathrm{Setup}` to get
$`(\mathrm{uk}, \mathrm{tk})`, and let $`o_U` and $`o_T` be the two outputs of
$`\mathrm{run}(U, T, \mathrm{uk}, \mathrm{tk}, r + 1)`. Output $`1` if
$`o_U \in \{\ast, \bot\}`, or $`o_T \in \{\ast, \bot\}`, or $`o_U = o_T`, and output $`0`
otherwise.
:::
::::

In Lean, `uOut.join` is `none` both when $`o_U = \ast` and when $`o_U = \bot`, and the same
holds for $`o_T`. The experiment returns `true` for $`1`.

::::definition "uake_perfectly_correct" (lean := "AKE.UAKE.PerfectlyCorrect") (uses := "uake_correct_exp, prob_comp_runtime")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.PerfectlyCorrect -docstrings
Let $`\Pi` be a UAKE scheme over a monad $`m`, and let $`R` be a runtime for $`m`. We
call $`\Pi` _perfectly correct_ under $`R` if $`\Pr_R[\mathsf{Corr}(\Pi) = 1] = 1`.
:::
::::

A scheme in which both parties always output $`\bot` is perfectly correct. Honest
completion is a separate condition, below. DF call a protocol _correct_ if, for all key
pairs from setup and all runs with outputs $`K_U` and $`K_T`, the equality $`K_U = K_T`
holds with all but negligible probability when $`K_U \neq \bot` and $`K_T \neq \bot` (DF,
Definition 7, p. 8). The definition above differs from DF Definition 7 in two points. It
asks for probability $`1`, where DF allow a negligible error. Also, a party that has not
finished after $`r + 1` steps counts as a party with output $`\bot`, so such a run is
correct. In both definitions a run with output $`\bot` is correct.
[Issue #72](https://github.com/Beneficial-AI-Foundation/libsignal-verify/issues/72) tracks
the correctness of the production PQXDH handshake, which this notion does not cover.

## Admissible schemes

Three further conditions describe a scheme that runs as intended. DF have none of them as
a separate definition. The security theorems for PQXDH take none of them as a hypothesis.
The next chapter proves the first condition, and perfect correctness, for the PQXDH model.

::::definition "uake_well_formed" (lean := "AKE.UAKE.Scheme.WellFormed") (uses := "uake_scheme, uake_outputs_only_at_completion, uake_pure_output, uake_run_honest")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.Scheme.WellFormed -docstrings
Let $`\Pi = (r, \mathrm{Setup}, U, T)` be a UAKE scheme over a monad $`m` with a support.
We call $`\Pi` _well formed_ if

* $`U` and $`T` output only at completion,
* $`U` and $`T` have pure output, and
* for every $`(\mathrm{uk}, \mathrm{tk}) \in \mathrm{supp}(\mathrm{Setup})` and every
  $`(o_U, o_T, \mathit{ms})` in the support of
  $`\mathrm{run}(U, T, \mathrm{uk}, \mathrm{tk}, r + 1)`, the list $`\mathit{ms}` of
  messages has length $`r`.
:::
::::

The condition does not ask that $`T` speaks last.

::::definition "uake_honestly_completes" (lean := "AKE.UAKE.Scheme.HonestlyCompletes") (uses := "uake_scheme, uake_run_honest, prob_comp_runtime")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.Scheme.HonestlyCompletes -docstrings
Let $`\Pi = (r, \mathrm{Setup}, U, T)` be a UAKE scheme over a monad $`m` with key space
$`K`, and let $`R` be a runtime for $`m`. Let $`\mathsf{Compl}(\Pi)` be the computation in
$`m` that runs $`\mathrm{Setup}` to get $`(\mathrm{uk}, \mathrm{tk})`, lets $`o_U` and
$`o_T` be the two outputs of $`\mathrm{run}(U, T, \mathrm{uk}, \mathrm{tk}, r + 1)`, and
outputs $`1` if
$`o_U \in K` and $`o_T \in K`, and $`0` otherwise. We say that $`\Pi` _completes honestly_
under $`R` if $`\Pr_R[\mathsf{Compl}(\Pi) = 1] = 1`.
:::
::::

In Lean, $`\mathsf{Compl}(\Pi)` is `HonestCompletionExp`.

The model is generic in the monad $`m`, and a runtime gives the probability semantics of
$`m` (see the first chapter). The monad also carries its own measure semantics and its own
support. Coherence asks that the runtime agrees with them.

::::definition "uake_runtime_coherent" (lean := "AKE.UAKE.RuntimeCoherent") (uses := "prob_comp_runtime, eval_dist")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.RuntimeCoherent -docstrings
Let $`m` be a monad with a support $`\mathrm{supp}` and a measure semantics
$`\mathcal{D}_m`, and let $`\mathcal{D}` be the measure semantics of probabilistic
computations. Let $`R` be a runtime for $`m`, with semantics $`\mathcal{D}_R` and monad
morphism $`\iota : \mathrm{ProbComp} \to m`. We call $`R` _coherent_ if the following five
conditions hold.

1. The support is lawful. The support gives, for every type $`\alpha` and every
   $`x \in m(\alpha)`, a computation $`\tilde{x} \in m(\mathrm{supp}(x))`. For
   $`S \subseteq \alpha`, let $`j_S : S \to \alpha` be the inclusion. Then
   $`m(j_{\mathrm{supp}(x)})(\tilde{x}) = x` for every $`x \in m(\alpha)`, and
   $`\mathrm{supp}(m(j_S)(y)) \subseteq S` for every $`S \subseteq \alpha` and every
   $`y \in m(S)`.
2. The semantics $`\mathcal{D}_m` is lawful: $`\mathcal{D}_m(\mathrm{pure}(a))` is the
   Dirac measure at $`a`, and $`\mathcal{D}_m(x \mathbin{>\!\!>\!\!=} f)` is the measure
   $`S \mapsto \int \mathcal{D}_m(f(a))(S) \, d\mathcal{D}_m(x)(a)` for every $`f` such
   that $`a \mapsto \mathcal{D}_m(f(a))` is measurable.
3. For every computation $`x` in $`m`, $`\mathcal{D}_R(x) = \mathcal{D}_m(x)`.
4. For every probabilistic computation $`x`, $`\mathcal{D}_m(\iota(x)) = \mathcal{D}(x)`.
5. For every computation $`x \in m(\alpha)` with $`\alpha` discrete,
   $`\mathcal{D}_m(x)`-almost every $`a` lies in $`\mathrm{supp}(x)`.
:::
::::

In Lean, the five conditions are the fields `lawfulAttach`, `lawful`, `evalDist_eq`,
`lift_evalDist_eq` and `ae_mem_support`. The support is `support` from the class
`MonadAttach`, and $`\tilde{x}` is `MonadAttach.attach x`, whose results carry a proof that
they lie in the support. Condition 1 is the class `LawfulMonadAttach` of the Lean core
library: its two parts are `map_attach` and `canReturn_map_imp`.
The semantics $`\mathcal{D}_m` is `𝒟[·]` from the class `EvalDistSemantics`, and condition 2
is the class `LawfulEvalDistSemantics`. Condition 5 is stated only for output spaces with
the discrete σ-algebra.

::::theorem "uake_runtime_coherent_prob_comp" (lean := "AKE.UAKE.runtimeCoherent_probComp") (uses := "uake_runtime_coherent, prob_comp_runtime_canonical")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.runtimeCoherent_probComp (part := "signature") -docstrings
The canonical runtime for probabilistic computations is coherent.
:::
::::

In Lean, the canonical runtime is `ProbCompRuntime.probComp`, and the theorem has no
hypothesis.

::::definition "uake_admissible" (lean := "AKE.UAKE.Scheme.Admissible") (uses := "uake_runtime_coherent, uake_well_formed, uake_perfectly_correct, uake_honestly_completes")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.Scheme.Admissible -docstrings
Let $`\Pi` be a UAKE scheme over a monad $`m` with a support and a measure semantics, and
let $`R` be a runtime for $`m`. We call $`\Pi` _admissible_ under $`R` if $`R` is coherent,
and $`\Pi` is well formed, perfectly correct under $`R` and completes honestly under $`R`.
:::
::::

No condition of admissibility involves an adversary. Admissibility does not imply that the
security experiment below loses no mass against an adversary. Under a runtime that loses
mass, the lost mass lowers the probability of output $`1`. The advantage can then be large
with no attack, or small against an attack that always wins.
[Issue #29](https://github.com/Beneficial-AI-Foundation/libsignal-verify/issues/29) tracks
this. The PQXDH theorems use `ProbCompRuntime.probComp`, which loses no mass.

## The security experiment

The security experiment combines authenticity and key secrecy, as in DF. The adversary
runs one challenge session with $`U` and can open any number of sessions with copies of
$`T`. It talks to the parties through oracles, and the experiment keeps the state of every
session.

::::definition "uake_oracle_spec" (lean := "AKE.UAKE.oracleSpec") (uses := "oracle_spec")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.oracleSpec -docstrings
Let $`K` and $`W` be types. The _UAKE oracle interface_ with keys in $`K` and messages in
$`W` has the following queries, with the following types of answers:

* $`\mathrm{openT}`, with answers in $`\mathbb{N} \times (W + \{\ast\})`;
* $`\mathrm{stepT}(i, w)` for $`i \in \mathbb{N}` and $`w \in W`, with answers in
  $`W + \{\ast\}`;
* $`\mathrm{revealT}(i)` for $`i \in \mathbb{N}`, with answers in $`K + \{\bot\}`;
* $`\mathrm{stepChallenge}(w)` for $`w \in W`, with answers in $`W + \{\ast\}`.
:::
::::

In Lean, the queries are the constructors of the inductive type `AKE.UAKE.Op W`. The value
$`\ast` is `none` in the answer to $`\mathrm{openT}` and `inr ()` in the answer to a step
query, and $`\bot` is `none`.

::::definition "uake_op_impl" (lean := "AKE.UAKE.opImpl") (uses := "uake_oracle_spec, uake_scheme, uake_transcript, query_impl")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.opImpl -docstrings
Let $`\Pi = (r, \mathrm{Setup}, U, T)` be a UAKE scheme over a monad $`m` with key space
$`K` and messages in $`W`, and let $`\mathrm{tk}` be a key input of $`T`. The _oracles of
the security experiment_ answer the queries of the UAKE oracle interface in $`m`, with a
state that consists of

* a clock $`c \in \mathbb{N}`;
* the challenge session: a state of $`U`, a transcript $`\tau^*`, and a flag that says
  whether the session is closed;
* a list of sessions with $`T`. Session $`i` has a state $`s_i` of $`T`, a transcript
  $`\tau_i`, a key $`\kappa_i \in K + \{\bot\} + \{\ast\}`, where $`\ast` means that the
  session has no key yet, and a flag that says whether its key was revealed.

The queries are answered as follows. To record a message $`w` in a transcript means to
append $`(w, c)` to it and to increase $`c` by one.

1. $`\mathrm{openT}`: run $`T.\mathrm{init}(\mathrm{tk})` to get a state $`s` and
   $`w_0 \in W + \{\ast\}`. Start a transcript, and record $`w_0` in it if
   $`w_0 \neq \ast`. Append a session with state $`s`, this transcript, key $`\ast` and
   flag "not revealed". Answer $`(i, w_0)`, where $`i` is the number of sessions before
   the query.
2. $`\mathrm{stepT}(i, w)`: if there is no session $`i`, or $`\kappa_i \neq \ast`, answer
   $`\ast`. Otherwise run $`T.\mathrm{step}(s_i, w)`.
   * On rejection, answer $`\ast` and change nothing.
   * On acceptance with $`(s', w', \mathrm{done})`, record $`w` and then $`w'` in
     $`\tau_i`, and set $`s_i = s'`. If $`\mathrm{done} = 1`, set $`\kappa_i` to the
     result of $`T.\mathrm{output}(s')`. Answer $`w'`.
   * On completion with state $`s'`, record $`w` in $`\tau_i`, set $`s_i = s'`, and set
     $`\kappa_i` to the result of $`T.\mathrm{output}(s')`. Answer $`\ast`.
3. $`\mathrm{revealT}(i)`: if there is no session $`i`, or $`\kappa_i = \ast`, answer
   $`\bot`. Otherwise mark session $`i` as revealed and answer $`\kappa_i`.
4. $`\mathrm{stepChallenge}(w)`: if the challenge session is closed, answer $`\ast`.
   Otherwise step $`U` on $`w` from the state of the challenge session.
   * On rejection, answer $`\ast` and change nothing.
   * On acceptance with $`(s', w', \mathrm{done})`, record $`w` and then $`w'` in
     $`\tau^*`, move to $`s'`, and close the session if $`\mathrm{done} = 1`. Answer $`w'`.
   * On completion with state $`s'`, record $`w` in $`\tau^*`, move to $`s'`, and close the
     session. Answer $`\ast`.
:::
::::

In Lean, the state is a value of the structure `Env`, and session $`i` is a value of
`TSession`. The key $`\kappa_i` has type `Option (Option K)`, with the outer `none` for
$`\ast`. A rejected message does not enter the transcript, and the session stays open. The
answer $`\bot` to $`\mathrm{revealT}(i)` has two meanings: session $`i` has no key yet,
or $`T` output $`\bot` in it. In the second case the session is marked as revealed. The
function `oracleImpl` adds the uniform-sampling oracle, which it answers through the monad
morphism of the runtime.

::::definition "uake_adversary" (lean := "AKE.UAKE.Adversary") (uses := "uake_oracle_spec, oracle_comp")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.Adversary -docstrings
Let $`\Pi` be a UAKE scheme with key space $`K`, key inputs of $`U` in $`\mathrm{UK}` and
messages in $`W`. An _adversary_ against $`\Pi` consists of a type $`S` of states and two
oracle computations, each with access to uniform sampling and to the UAKE oracle
interface with keys in $`K` and messages in $`W`:

* $`\mathcal{A}_1`, which takes $`\mathrm{uk} \in \mathrm{UK}` and
  $`w_0 \in W + \{\ast\}` and outputs a state in $`S`;
* $`\mathcal{A}_2`, which takes a state in $`S` and a key in $`K + \{\bot\}` and outputs
  a bit.
:::
::::

In Lean, $`\mathcal{A}_1` and $`\mathcal{A}_2` are the fields `challenge` and `post`, and
$`\bot` is `none`.

::::definition "uake_exp" (lean := "AKE.UAKE.Exp") (uses := "uake_adversary, uake_op_impl, uake_ping_pong, simulate_q")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.Exp -docstrings
Let $`\Pi = (r, \mathrm{Setup}, U, T)` be a UAKE scheme over a monad $`m` whose key space
$`K` is finite and nonempty, let $`\iota` be a monad morphism from probabilistic
computations to $`m`, and let $`\mathcal{A} = (\mathcal{A}_1, \mathcal{A}_2)` be an
adversary against $`\Pi`. Put $`\beta = 1` if $`r` is odd and $`\beta = 0` otherwise. We
define the _security experiment_ $`\mathsf{Exp}(\mathcal{A})` to be the computation in $`m` with output in
$`\{0, 1\}` given by the following steps. Every uniform choice in it, including those of
the adversary, is made through $`\iota`. The adversary has access to uniform sampling and
to the oracles of the security experiment for $`\Pi` and the key input $`\mathrm{tk}` of
step 1.

1. Run $`\mathrm{Setup}` to get $`(\mathrm{uk}, \mathrm{tk})`, and draw a uniform bit
   $`b`.
2. Run $`U.\mathrm{init}(\mathrm{uk})`, and record its first message $`w_0`, if there is
   one, at time $`0` in the challenge transcript $`\tau^*`. Run
   $`\mathcal{A}_1(\mathrm{uk}, w_0)` with the oracles, starting with no session with
   $`T`. Let $`K_0` be the output of $`U` in the final state of the challenge session, with $`\ast` read as $`\bot`.
3. If $`K_0 = \bot`, put $`K_1 = \bot` and go to step 6.
4. If no session with $`T` has a transcript that matches $`\tau^*` with first-speaker bit
   $`\beta`, output $`1`.
5. Draw $`K_1` uniformly from $`K`.
6. Close the challenge session. Run $`\mathcal{A}_2` on its state and on $`K_b`, with the
   same oracles, and let $`b'` be its output.
7. If some session with $`T` that the adversary has revealed has a transcript that matches
   $`\tau^*` with first-speaker bit $`\beta`, output a uniform bit. Otherwise output $`1` if
   $`b' = b` and $`0` if $`b' \neq b`.
:::
::::

In Lean, `challengeSession` runs step 2, `isPingPong` is the test of step 4, and `finalize`
runs steps 6 and 7. The test of step 7 is `fullPingPong`, which keeps only the revealed
sessions with $`T`. The monad morphism $`\iota` is the argument `lift`. Step 4 reads the
transcripts at the end of step 2, and step 7 reads them at the end of step 6. Output $`1`
is `true`. In place of "finite and nonempty", the key space carries an instance of
`SampleableType`, which gives the uniform draw of step 5.

The first chapter defines the advantage of $`\mathcal{A}` under a runtime $`R` for $`m` as
$`\mathrm{Adv}_R(\mathcal{A}) = |\Pr_R[\mathsf{Exp}(\mathcal{A}) = 1] - \tfrac{1}{2}|`,
where the experiment uses the monad morphism of $`R`. This section only gives definitions:
it assumes nothing and proves nothing. The security theorems of the next chapter bound the
advantage in a partnered experiment, defined there, which changes two tests of this one.

DF define the experiment as follows (DF, Section 3, p. 8). The adversary runs one
challenge session with $`U` and can open any number of sessions with copies of $`T`.
After $`T` sends its last message in a session, the adversary may ask $`T` to reveal its
key. If it does so in a session that matches the challenge session, DF call it
_full-ping-pong_.

1. Run setup to get $`(\mathrm{uk}, \mathrm{tk})`, and draw a uniform bit $`b`.
2. Run $`U(\mathrm{uk})` against $`\mathcal{A}(\mathrm{uk})`, where $`\mathcal{A}` has
   oracle access to copies of $`T(\mathrm{tk})`. Let $`K_0` be the output of $`U`.
3. If $`K_0 = \bot`, set $`K_1 = \bot`.
4. Otherwise, if $`\mathcal{A}` is not ping-pong, output $`1`. The adversary has made $`U`
   accept without relaying, and so it has broken authenticity.
5. Otherwise, draw $`K_1` uniformly from $`K`.
6. Give $`K_b` to $`\mathcal{A}`, which keeps its oracle access to $`T`, and let $`b'` be
   its guess.
7. If $`\mathcal{A}` is full-ping-pong, output a uniform bit. Otherwise output $`1` if
   $`b' = b`, and $`0` otherwise.

DF call the protocol secure if every efficient adversary has negligible advantage (DF,
Definition 8, p. 9). The definition above follows these steps one by one. It differs
from DF in the following points.

* DF do not say what happens to a message that a party rejects. The Lean model drops the
  message from the transcript and keeps the session open.
* DF assume that $`T` speaks last. The Lean model does not enforce this. The ping-pong
  test reads the first speaker from the parity of $`r`, under the assumption that $`T`
  speaks last. A well-formed scheme in which $`T` does not speak last is trivially
  insecure, as soon as $`U` accepts in an honest run.
* The model does not represent schemes with a single message.
* DF give a party as an interactive algorithm, and the Lean model gives it as a state
  machine with an output map.
* The conditions of well-formedness, honest completion and runtime coherence are new.

# Signatures

In PQXDH, Bob signs his prekeys with his identity key. This section gives the syntax of a
signature scheme and its completeness, and then the unforgeability game that the PQXDH
theorems use.

## Signature schemes

::::definition "sig_scheme" (lean := "SignatureAlg") (uses := "prob_comp")
:::LibsignalVerifyBlueprint.pair SignatureAlg -docstrings -comments
Let $`m` be a monad and let $`M`, $`\mathrm{PK}`, $`\mathrm{SK}` and $`S` be types. A
_signature scheme_ over $`m` with messages in $`M`, public keys in $`\mathrm{PK}`, secret
keys in $`\mathrm{SK}` and signatures in $`S` is a triple
$`\Sigma = (\mathrm{KeyGen}, \mathrm{Sign}, \mathrm{Verify})` of

* a computation $`\mathrm{KeyGen}` in $`m` with output in $`\mathrm{PK} \times \mathrm{SK}`,
* for each $`\mathrm{pk} \in \mathrm{PK}`, $`\mathrm{sk} \in \mathrm{SK}` and $`\mu \in M`, a
  computation $`\mathrm{Sign}(\mathrm{pk}, \mathrm{sk}, \mu)` in $`m` with output in $`S`,
* for each $`\mathrm{pk} \in \mathrm{PK}`, $`\mu \in M` and $`\sigma \in S`, a computation
  $`\mathrm{Verify}(\mathrm{pk}, \mu, \sigma)` in $`m` with output in $`\{0, 1\}`.
:::
::::

In Lean, the three components are `keygen`, `sign` and `verify`, and the output $`1` of
$`\mathrm{Verify}` is `true`. Boneh and Shoup define a signature scheme as a triple of
efficient algorithms $`(G, S, V)` over a message space and a signature space (Definition 13.1,
pp. 528 and 529). Their signing algorithm takes the secret key and the message, and their
verification algorithm is deterministic. In the definition above, signing also takes the
public key, and all three algorithms are computations in $`m`, so verification may be
randomised. No resource is bounded. The PQXDH theorems of the next chapter assume that
verification is deterministic, as a separate hypothesis.

::::definition "sig_perfectly_complete" (lean := "SignatureAlg.PerfectlyComplete") (uses := "sig_scheme, prob_comp_runtime")
:::LibsignalVerifyBlueprint.pair SignatureAlg.PerfectlyComplete -docstrings -comments
Let $`\Sigma = (\mathrm{KeyGen}, \mathrm{Sign}, \mathrm{Verify})` be a signature scheme over
a monad $`m` with messages in $`M`, and let $`R` be a runtime for $`m`. We call $`\Sigma`
_perfectly complete_ under $`R` if for every $`\mu \in M`,
$$`\begin{aligned}\Pr_R\big[&(\mathrm{pk}, \mathrm{sk}) \leftarrow \mathrm{KeyGen};\\ &\sigma \leftarrow \mathrm{Sign}(\mathrm{pk}, \mathrm{sk}, \mu)\\ &: \mathrm{Verify}(\mathrm{pk}, \mu, \sigma) = 1\big] = 1.\end{aligned}`
:::
::::

Boneh and Shoup require that for all key pairs output by $`G` and all messages $`m`, the
verification accepts a signature generated by $`S` with probability $`1` (Definition 13.1,
p. 529). The Lean condition takes the probability over the key pair, the signing and the
verification together. An average of probabilities is $`1` only if every outcome of positive
probability has value $`1`, so the two conditions agree on every key pair that
$`\mathrm{KeyGen}` can output. The Lean development does not state this equivalence. Perfect
completeness is a hypothesis of both correctness theorems of the next chapter.

## Joint unforgeability

In PQXDH, the identity key of a party signs its prekeys and also takes part in
Diffie-Hellman agreement. An adversary may see the results of both uses of the secret key.
The joint game below gives the forger an oracle for the second use.

::::definition "sig_joint_adversary" (lean := "SignatureAlg.JointAdversary") (uses := "oracle_comp")
:::LibsignalVerifyBlueprint.pair SignatureAlg.JointAdversary -docstrings
Let $`\mathrm{PK}`, $`\mathrm{SK}`, $`M`, $`S`, $`X` and $`Y` be types. Let
$`\Sigma = (\mathrm{KeyGen}, \mathrm{Sign}, \mathrm{Verify})` be a signature scheme with
public keys in $`\mathrm{PK}`, secret keys in $`\mathrm{SK}`, messages in $`M` and
signatures in $`S`: $`\mathrm{KeyGen}` is a probabilistic computation with values in
$`\mathrm{PK} \times \mathrm{SK}`, and for all $`\mathrm{pk} \in \mathrm{PK}`,
$`\mathrm{sk} \in \mathrm{SK}`, $`\mu \in M` and $`\sigma \in S`,
$`\mathrm{Sign}(\mathrm{pk}, \mathrm{sk}, \mu)` is a probabilistic computation with values
in $`S` and $`\mathrm{Verify}(\mathrm{pk}, \mu, \sigma)` is a probabilistic computation
with values in $`\{0, 1\}`. Let $`\mathrm{agree} : \mathrm{SK} \times X \to Y` be a map.
A _joint adversary_ against $`(\Sigma, \mathrm{agree})` is an oracle computation
$`\mathcal{A}` that takes $`\mathrm{pk} \in \mathrm{PK}` and outputs a pair in
$`M \times S`, with access to three oracles:

* uniform sampling;
* a signing oracle, which takes $`\mu \in M` and answers with an element of $`S`;
* an agreement oracle, which takes $`x \in X` and answers with an element of $`Y`.
:::
::::

In Lean, the oracles are those of `SignatureAlg.JointSpec`, and the adversary is the field
`main`.

::::definition "sig_joint_exp" (lean := "SignatureAlg.jointUnforgeableExp") (uses := "sig_joint_adversary, simulate_q")
:::LibsignalVerifyBlueprint.pair SignatureAlg.jointUnforgeableExp -docstrings
Let $`\Sigma = (\mathrm{KeyGen}, \mathrm{Sign}, \mathrm{Verify})` be a signature scheme
with public keys in $`\mathrm{PK}`, secret keys in $`\mathrm{SK}`, messages in $`M` and
signatures in $`S`, let $`\mathrm{agree} : \mathrm{SK} \times X \to Y` be a map, and let
$`\mathcal{A}` be a joint adversary against $`(\Sigma, \mathrm{agree})`. The _joint
unforgeability game_ $`\mathsf{JUF}(\mathcal{A})` is the probabilistic computation with
output in $`\{0, 1\}` given by the following steps.

1. Run $`\mathrm{KeyGen}` to get $`(\mathrm{pk}, \mathrm{sk})`, and start with an empty
   list $`L`.
2. Run $`\mathcal{A}(\mathrm{pk})`, and answer its queries as follows. Answer a
   uniform-sampling query with a uniform draw. Answer a signing query $`\mu` with a result
   of $`\mathrm{Sign}(\mathrm{pk}, \mathrm{sk}, \mu)`, and append $`\mu` to $`L`. Answer
   an agreement query $`x` with $`\mathrm{agree}(\mathrm{sk}, x)`. Let
   $`(\mu^*, \sigma^*)` be the output of $`\mathcal{A}`.
3. Run $`\mathrm{Verify}(\mathrm{pk}, \mu^*, \sigma^*)` to get a bit $`v`. Output $`1`
   if $`v = 1` and $`\mu^* \notin L`, and $`0` otherwise.
:::
::::

In Lean, `SignatureAlg.jointImpl` answers the queries and keeps $`L` as its state. The game
does not record the agreement queries, so they put no condition on the forgery.

::::definition "sig_joint_advantage" (lean := "SignatureAlg.JointAdversary.advantage") (uses := "sig_joint_exp, eval_dist")
:::LibsignalVerifyBlueprint.pair SignatureAlg.JointAdversary.advantage -docstrings
Let $`\Sigma` be a signature scheme with secret keys in $`\mathrm{SK}`, let $`X` and
$`Y` be types, let $`\mathrm{agree} : \mathrm{SK} \times X \to Y` be a map, and let
$`\mathcal{A}` be a joint adversary against $`(\Sigma, \mathrm{agree})`. The _advantage_
of $`\mathcal{A}` is $`\Pr[\mathsf{JUF}(\mathcal{A}) = 1] \in [0, \infty]`.
:::
::::

In Lean, $`[0, \infty]` is `ℝ≥0∞`, the type of the probabilities of VCV-io.

The joint game is defined in this repository. Without the agreement oracle it is the
EUF-CMA game of Boneh and Shoup (Attack Game 13.1, pp. 529 and 530). There the challenger
draws a key pair $`(\mathrm{pk}, \mathrm{sk})` and gives $`\mathrm{pk}` to the adversary.
The adversary asks for signatures on messages of its choice and outputs a pair
$`(\mu^*, \sigma^*)`. It wins if $`\sigma^*` is a valid signature on $`\mu^*` and $`\mu^*`
is not one of the signed messages, and its advantage is the probability that it wins.

Both PQXDH theorems of the next chapter assume a bound on the advantage of every joint
adversary. They also assume that verification is deterministic, which the definition of a
signature scheme above does not ask.

# The gap Diffie-Hellman problem

The model writes the Diffie-Hellman group additively, as a vector space over a field of
scalars. The gap problem asks the adversary to compute a Diffie-Hellman value while an
oracle tells it which triples are Diffie-Hellman triples.

::::definition "dh_is_dh" (lean := "DiffieHellman.IsDH")
:::LibsignalVerifyBlueprint.pair DiffieHellman.IsDH -docstrings
Let $`F` be a field, let $`G` be a vector space over $`F`, and let $`g \in G`. For
$`x \in F` we write $`x \cdot g` for the scalar multiple of $`g`. We call a triple
$`(X, Y, Z) \in G^3` a _Diffie-Hellman triple_ for $`g` if there are $`x, y \in F` with
$`X = x \cdot g`, $`Y = y \cdot g` and $`Z = (xy) \cdot g`.
:::
::::

In Lean, the predicate is `IsDH g X Y Z`. The vector space $`G` is arbitrary: the model
does not ask that $`G` is cyclic, or that $`g` is nonzero.

::::definition "dh_gap_adversary" (lean := "DiffieHellman.GapDHAdversary") (uses := "oracle_comp")
:::LibsignalVerifyBlueprint.pair DiffieHellman.GapDHAdversary -docstrings
Let $`F` be a field, and let $`G` be a vector space over $`F`. A _gap Diffie-Hellman
adversary_ is an oracle computation that takes three elements of $`G` and outputs an
element of $`G`, with access to uniform sampling and to an oracle that takes a triple in
$`G^3` and answers with a bit.
:::
::::

In Lean, the type `GapDHAdversary F G` names the field $`F` but does not use it: an
adversary is a function of three elements of $`G`. The game below runs it on $`g`,
$`a \cdot g` and $`b \cdot g`.

::::definition "dh_ddh_oracle" (lean := "DiffieHellman.ddhOracle") (uses := "dh_is_dh, query_impl")
:::LibsignalVerifyBlueprint.pair DiffieHellman.ddhOracle -docstrings
Let $`F` be a field, let $`G` be a vector space over $`F`, and let $`g \in G`. The
_decision oracle_ for $`g` answers a triple $`(X, Y, Z) \in G^3` with $`1` if it is a
Diffie-Hellman triple for $`g`, and with $`0` otherwise. It answers a uniform-sampling query with a uniform draw.
:::
::::

In Lean, the oracle decides `IsDH` with classical logic, so it need not be computable.

::::definition "dh_gap_exp" (lean := "DiffieHellman.gapDHExp") (uses := "dh_gap_adversary, dh_ddh_oracle, simulate_q")
:::LibsignalVerifyBlueprint.pair DiffieHellman.gapDHExp -docstrings
Let $`F` be a finite field, let $`G` be a vector space over $`F`, let $`g \in G`, and let
$`\mathcal{A}` be a gap Diffie-Hellman adversary. The _gap Diffie-Hellman game_
$`\mathsf{GDH}(\mathcal{A})` is the probabilistic computation that draws $`a` and $`b`
uniformly and independently from $`F`, runs $`\mathcal{A}(g, a \cdot g, b \cdot g)` with the decision oracle for $`g` to
get $`h \in G`, and outputs $`1` if $`h = (ab) \cdot g` and $`0` otherwise.
:::
::::

In Lean, the class `SampleableType F` gives the uniform distribution on $`F`, and the
game draws with `$ᵗ F`. The scalars $`a` and $`b` may be $`0`.

::::definition "dh_gap_advantage" (lean := "DiffieHellman.gapDHAdvantage") (uses := "dh_gap_exp, eval_dist")
:::LibsignalVerifyBlueprint.pair DiffieHellman.gapDHAdvantage -docstrings
Let $`F` be a finite field, let $`G` be a vector space over $`F`, let $`g \in G`, and let
$`\mathcal{A}` be a gap Diffie-Hellman adversary. The _advantage_ of $`\mathcal{A}` is the
real number $`\mathrm{Adv}^{\mathrm{gdh}}(\mathcal{A}) := \Pr[\mathsf{GDH}(\mathcal{A}) = 1]`.
:::
::::

Boneh and Shoup state the interactive computational Diffie-Hellman problem for a cyclic
group (Attack Game 12.3 and Definition 12.4, pp. 479 and 480). In that game the oracle
decides only triples whose first component is the fixed element $`a \cdot g`. The oracle of
the Lean game decides arbitrary triples, so the Lean assumption is stronger. The Lean group
is a vector space over a field, and the scalars are drawn from the whole field.

The classical PQXDH theorem of the next chapter assumes a bound on the advantage of every
gap Diffie-Hellman adversary. The post-quantum theorem does not use this game.

# Authenticated encryption

The model uses authenticated encryption with associated data and without nonces. Its
security is ciphertext integrity: no adversary can produce a new ciphertext that decrypts.

::::definition "aead_scheme" (lean := "AEAD.Scheme")
:::LibsignalVerifyBlueprint.pair AEAD.Scheme -docstrings
Let $`\mathcal{K}`, $`\mathcal{M}`, $`\mathrm{AD}` and $`\mathcal{C}` be types of keys,
messages, associated data and ciphertexts, and let $`m` be a monad. An _AEAD scheme_ over
$`m` is a pair $`(E, D)` of

* an encryption algorithm $`E`, which for $`k \in \mathcal{K}`, $`d \in \mathrm{AD}` and
  $`\mu \in \mathcal{M}` gives a computation $`E(k, d, \mu)` in $`m` with values in
  $`\mathcal{C}`;
* a decryption map
  $`D : \mathcal{K} \times \mathrm{AD} \times \mathcal{C} \to \mathcal{M} + \{\mathsf{rej}\}`.
:::
::::

In Lean, $`\mathsf{rej}` is `none`. Decryption is a function, so it is deterministic. All
games below take $`m` to be the monad of probabilistic computations.

::::definition "aead_perfectly_correct" (lean := "AEAD.PerfectlyCorrect") (uses := "aead_scheme, eval_dist")
:::LibsignalVerifyBlueprint.pair AEAD.PerfectlyCorrect -docstrings
Let $`(E, D)` be an AEAD scheme over probabilistic computations, with $`\mathcal{K}`
finite and nonempty. We call $`(E, D)` _perfectly correct_ if for every
$`\mu \in \mathcal{M}` and every $`d \in \mathrm{AD}`,
$$`\begin{aligned}\Pr\big[&k \leftarrow \mathcal{K};\ c \leftarrow E(k, d, \mu)\\ &: D(k, d, c) = \mu\big] = 1,\end{aligned}`
where $`k` is drawn uniformly.
:::
::::

In Lean, the experiment inside the probability is `AEAD.CorrectExp`, and the class
`SampleableType` gives the uniform distribution on keys. Boneh and Shoup define a cipher
with associated data and no nonces as a pair $`(E, D)` (Section 9.6, p. 380). They write
the encryption as $`E(k, m, d)` and the decryption as $`D(k, c, d)`, and they require
$`\Pr[D(k, E(k, m, d), d) = m] = 1`, without saying how $`k` is chosen. The Lean condition
draws $`k` uniformly. Every key then has positive probability, so the Lean condition holds
if and only if the equation holds for every key. The Lean development does not state this
equivalence.

## Ciphertext integrity

In the ciphertext integrity game, the adversary sees encryptions of messages of its choice.
It tries to produce a new pair of associated data and ciphertext that decrypts.

::::definition "aead_int_ctxt_adversary" (lean := "AEAD.INT_CTXT_Adversary") (uses := "aead_scheme, oracle_comp")
:::LibsignalVerifyBlueprint.pair AEAD.INT_CTXT_Adversary -docstrings
Let $`(E, D)` be an AEAD scheme over probabilistic computations, with keys in
$`\mathcal{K}`, messages in $`\mathcal{M}`, associated data in $`\mathrm{AD}` and
ciphertexts in $`\mathcal{C}`. An _INT-CTXT adversary_ against $`(E, D)` is an oracle
computation $`\mathcal{A}` that outputs a pair in $`\mathrm{AD} \times \mathcal{C}`, with
access to uniform sampling and to an encryption oracle, which takes
$`(d, \mu) \in \mathrm{AD} \times \mathcal{M}` and answers with an element of
$`\mathcal{C}`.
:::
::::

::::definition "aead_int_ctxt_game" (lean := "AEAD.INT_CTXT_Game") (uses := "aead_int_ctxt_adversary, simulate_q")
:::LibsignalVerifyBlueprint.pair AEAD.INT_CTXT_Game -docstrings
Let $`(E, D)` be an AEAD scheme over probabilistic computations, with $`\mathcal{K}`
finite and nonempty, and let $`\mathcal{A}` be an INT-CTXT adversary against $`(E, D)`.
The _ciphertext integrity game_ $`\mathsf{CTXT}(\mathcal{A})` is the probabilistic
computation with output in $`\{0, 1\}` given by the following steps.

1. Draw $`k` uniformly from $`\mathcal{K}`, and start with an empty list $`L`.
2. Run $`\mathcal{A}`. Answer a uniform-sampling query with a uniform draw. Answer an
   encryption query $`(d, \mu)` with a result $`c` of $`E(k, d, \mu)`, and append
   $`(d, c)` to $`L`. Let $`(d^*, c^*)` be the output of $`\mathcal{A}`.
3. Output $`1` if $`D(k, d^*, c^*) \neq \mathsf{rej}` and $`(d^*, c^*) \notin L`, and
   $`0` otherwise.
:::
::::

In Lean, `AEAD.ctxtImpl` answers the encryption queries and keeps the list $`L`. The
condition $`(d^*, c^*) \notin L` is part of the winning condition, so a forgery that the
oracle returned does not win.

::::definition "aead_int_ctxt_advantage" (lean := "AEAD.INT_CTXT_Advantage") (uses := "aead_int_ctxt_game, eval_dist")
:::LibsignalVerifyBlueprint.pair AEAD.INT_CTXT_Advantage -docstrings
Let $`(E, D)` be an AEAD scheme over probabilistic computations, with $`\mathcal{K}`
finite and nonempty, and let $`\mathcal{A}` be an INT-CTXT adversary against $`(E, D)`.
The _advantage_ of $`\mathcal{A}` is the real number
$`\mathrm{Adv}^{\mathrm{ctxt}}(\mathcal{A}) := \Pr[\mathsf{CTXT}(\mathcal{A}) = 1]`.
:::
::::

This is Attack Game 9.1 of Boneh and Shoup (pp. 358 and 359), with associated data added
as in Attack Game 9.3 (p. 379). Attack Game 9.3 is for ciphers with nonces. For ciphers
with associated data and no nonces, Boneh and Shoup define only CCA security (Section 9.6,
p. 380), and they do not state this game.

The PQXDH theorems use a variant in which the adversary also has a decryption oracle. It
wins as soon as one of its decryption queries is a new pair that decrypts.

::::definition "aead_int_ctxt_d_adversary" (lean := "AEAD.INT_CTXT_D_Adversary") (uses := "aead_scheme, oracle_comp")
:::LibsignalVerifyBlueprint.pair AEAD.INT_CTXT_D_Adversary -docstrings
Let $`(E, D)` be an AEAD scheme over probabilistic computations, with keys in
$`\mathcal{K}`, messages in $`\mathcal{M}`, associated data in $`\mathrm{AD}` and
ciphertexts in $`\mathcal{C}`. An _INT-CTXT-D adversary_ against $`(E, D)` is an oracle
computation $`\mathcal{B}` with no output, with access to uniform sampling, to an
encryption oracle, which takes $`(d, \mu) \in \mathrm{AD} \times \mathcal{M}` and answers
with an element of $`\mathcal{C}`, and to a decryption oracle, which takes
$`(d, c) \in \mathrm{AD} \times \mathcal{C}` and answers with an element of
$`\mathcal{M} + \{\mathsf{rej}\}`.
:::
::::

::::definition "aead_int_ctxt_d_game" (lean := "AEAD.INT_CTXT_D_Game") (uses := "aead_int_ctxt_d_adversary, simulate_q")
:::LibsignalVerifyBlueprint.pair AEAD.INT_CTXT_D_Game -docstrings
Let $`(E, D)` be an AEAD scheme over probabilistic computations, with $`\mathcal{K}`
finite and nonempty, and let $`\mathcal{B}` be an INT-CTXT-D adversary against
$`(E, D)`. The _decryption game_ $`\mathsf{CTXT\text{-}D}(\mathcal{B})` is the
probabilistic computation with output in $`\{0, 1\}` given by the following steps.

1. Draw $`k` uniformly from $`\mathcal{K}`. Start with an empty list $`L` and a flag
   $`\mathrm{won} = 0`.
2. Run $`\mathcal{B}`. Answer a uniform-sampling query with a uniform draw. Answer an
   encryption query $`(d, \mu)` with a result $`c` of $`E(k, d, \mu)`, and append
   $`(d, c)` to $`L`. Answer a decryption query $`(d, c)` with $`D(k, d, c)`. If
   $`D(k, d, c) \neq \mathsf{rej}` and $`(d, c) \notin L` at the time of the query, set
   $`\mathrm{won} = 1`.
3. Output $`\mathrm{won}`.
:::
::::

In Lean, `AEAD.ctxtDecImpl` answers the queries and keeps $`L` and the flag. A decryption
query wins if its pair is not in $`L` at the time of the query, even if the encryption
oracle returns the same pair later. Boneh and Shoup do not have this game.

::::definition "aead_int_ctxt_d_advantage" (lean := "AEAD.INT_CTXT_D_Advantage") (uses := "aead_int_ctxt_d_game, eval_dist")
:::LibsignalVerifyBlueprint.pair AEAD.INT_CTXT_D_Advantage -docstrings
Let $`(E, D)` be an AEAD scheme over probabilistic computations, with $`\mathcal{K}`
finite and nonempty, and let $`\mathcal{B}` be an INT-CTXT-D adversary against $`(E, D)`.
The _advantage_ of $`\mathcal{B}` is the real number
$`\mathrm{Adv}^{\mathrm{ctxt\text{-}d}}(\mathcal{B}) := \Pr[\mathsf{CTXT\text{-}D}(\mathcal{B}) = 1]`.
:::
::::

The two games are related in both directions. In the first direction, the forgery of an
INT-CTXT adversary becomes a decryption query.

::::theorem "aead_int_ctxt_le_int_ctxt_d" (lean := "AEAD.INT_CTXT_Advantage_le_INT_CTXT_D_Advantage") (uses := "aead_int_ctxt_advantage, aead_int_ctxt_d_advantage")
:::LibsignalVerifyBlueprint.pair AEAD.INT_CTXT_Advantage_le_INT_CTXT_D_Advantage (part := "signature") -docstrings
Let $`(E, D)` be an AEAD scheme over probabilistic computations, with $`\mathcal{K}`
finite and nonempty, and let $`\mathcal{A}` be an INT-CTXT adversary against $`(E, D)`.
Let $`\mathcal{B}` be the INT-CTXT-D adversary that runs $`\mathcal{A}`, forwards its
uniform-sampling and encryption queries, and then sends the output of $`\mathcal{A}` as a decryption query.
Then
$$`\mathrm{Adv}^{\mathrm{ctxt}}(\mathcal{A}) \le \mathrm{Adv}^{\mathrm{ctxt\text{-}d}}(\mathcal{B}).`
:::
::::

In Lean, $`\mathcal{B}` is `ctxtToDec A`. The theorem is proved, with no hypothesis. The
lemma `INT_CTXT_D_Advantage_ctxtToDec` shows that the two advantages are equal.

In the other direction, the reduction guesses which decryption query wins. The bound
therefore has a factor $`v`, the number of decryption queries.

::::theorem "aead_int_ctxt_d_le_mul_int_ctxt" (lean := "AEAD.INT_CTXT_D_Advantage_le_mul_INT_CTXT_Advantage") (uses := "aead_int_ctxt_advantage, aead_int_ctxt_d_advantage, aead_perfectly_correct")
:::LibsignalVerifyBlueprint.pair AEAD.INT_CTXT_D_Advantage_le_mul_INT_CTXT_Advantage (part := "signature") -docstrings
Let $`(E, D)` be a perfectly correct AEAD scheme over probabilistic computations, with
$`\mathcal{K}` finite and nonempty. Let $`(\bar d, \bar c) \in \mathrm{AD} \times \mathcal{C}`,
and let $`v \in \mathbb{N}`. Let $`\mathcal{B}` be an INT-CTXT-D adversary that makes at
most $`v` decryption queries in every run. Let $`\mathcal{B}'` be the following INT-CTXT
adversary. It draws $`i` uniformly from $`\{0, \dots, v - 1\}` (from $`\{0\}` if
$`v = 0`) and runs $`\mathcal{B}`, forwarding its uniform-sampling queries.

* Until it has captured a pair, it forwards each encryption query $`(d, \mu)` of
  $`\mathcal{B}` to its own oracle, returns the answer $`c`, and records the triple
  $`(d, \mu, c)`. After it has captured a pair, it answers every encryption query with
  $`\bar c`.
* It answers a decryption query $`(d, c)` with the message of the first recorded triple
  of the form $`(d, \cdot, c)`, or with $`\mathsf{rej}` if there is none. The decryption
  queries are numbered from $`0`, and the pair of query number $`i` is the captured pair.
* At the end it outputs the captured pair, or $`(\bar d, \bar c)` if $`\mathcal{B}` made at
  most $`i` decryption queries.

Then
$$`\mathrm{Adv}^{\mathrm{ctxt\text{-}d}}(\mathcal{B}) \le v \cdot \mathrm{Adv}^{\mathrm{ctxt}}(\mathcal{B}').`
:::
::::

In Lean, $`\mathcal{B}'` is `decToCtxt fallback v B` with `fallback` the pair
$`(\bar d, \bar c)`, and the recorded triples are looked up with `AEAD.logLookup`. The
bound on decryption queries is the hypothesis `hv`, stated with `IsQueryBoundP`. The theorem is
proved. Because it takes a pair `fallback`, it says nothing when there is no pair of
associated data and ciphertext.

The Lean development also defines a third game, `AEAD.INT_CTXT_VF_Game`, with an oracle
that only says whether a pair decrypts, and two similar theorems for it. The reductions
count encryption and decryption queries, but not running time. Both PQXDH theorems of the
next chapter assume a bound on the advantage of every INT-CTXT-D adversary directly, and
use none of these four theorems. They do not assume that the AEAD scheme is perfectly
correct.

## Indistinguishability

The repository also defines IND-CPA security as a reference notion. No PQXDH theorem uses
it.

::::definition "aead_ind_cpa_adversary" (lean := "AEAD.IND_CPA_Adversary") (uses := "aead_scheme, oracle_comp")
:::LibsignalVerifyBlueprint.pair AEAD.IND_CPA_Adversary -docstrings
Let $`(E, D)` be an AEAD scheme over probabilistic computations, with keys in
$`\mathcal{K}`, messages in $`\mathcal{M}`, associated data in $`\mathrm{AD}` and
ciphertexts in $`\mathcal{C}`, and let $`\ell : \mathcal{M} \to \mathbb{N}` be a length
map. An _IND-CPA adversary_ for $`(E, D)` and $`\ell` is an oracle computation
$`\mathcal{A}` with output in $`\{0, 1\}`, with access to uniform sampling and to a
challenge oracle, which takes a triple
$`(d, \mu_0, \mu_1) \in \mathrm{AD} \times \mathcal{M} \times \mathcal{M}` with
$`\ell(\mu_0) = \ell(\mu_1)` and answers with an element of $`\mathcal{C}`.
:::
::::

In Lean, a challenge query has type `AEAD.EqualLengthChallenge`, which carries a proof of
$`\ell(\mu_0) = \ell(\mu_1)`. A message type of fixed length takes $`\ell = 0`.

::::definition "aead_ind_cpa_game" (lean := "AEAD.IND_CPA_Game") (uses := "aead_ind_cpa_adversary, simulate_q")
:::LibsignalVerifyBlueprint.pair AEAD.IND_CPA_Game -docstrings
Let $`(E, D)` be an AEAD scheme over probabilistic computations, with $`\mathcal{K}`
finite and nonempty, let $`\ell : \mathcal{M} \to \mathbb{N}` be a length map, and let
$`\mathcal{A}` be an IND-CPA adversary for $`(E, D)` and $`\ell`. The _IND-CPA game_
$`\mathsf{CPA}(\mathcal{A})` draws $`k` uniformly from $`\mathcal{K}` and a uniform
bit $`b`, and runs $`\mathcal{A}`. It answers a uniform-sampling query with a uniform draw,
and a challenge query $`(d, \mu_0, \mu_1)` with a result of $`E(k, d, \mu_b)`. It outputs
$`1` if the output $`b'` of $`\mathcal{A}` equals $`b`, and $`0` otherwise.
:::
::::

In Lean, the challenge oracle of the game is `AEAD.cpaImpl`.

::::definition "aead_ind_cpa_advantage" (lean := "AEAD.IND_CPA_Advantage") (uses := "aead_ind_cpa_game, eval_dist")
:::LibsignalVerifyBlueprint.pair AEAD.IND_CPA_Advantage -docstrings
Let $`(E, D)` be an AEAD scheme over probabilistic computations, with $`\mathcal{K}`
finite and nonempty, let $`\ell : \mathcal{M} \to \mathbb{N}` be a length map, and let
$`\mathcal{A}` be an IND-CPA adversary for $`(E, D)` and $`\ell`. The _advantage_ of
$`\mathcal{A}` is the real number
$`\mathrm{Adv}^{\mathrm{cpa}}(\mathcal{A}) := \big|\Pr[\mathsf{CPA}(\mathcal{A}) = 1] - \tfrac{1}{2}\big|`.
:::
::::

Boneh and Shoup define the advantage as $`|\Pr[W_0] - \Pr[W_1]|`, where $`W_b` is the event
that the adversary outputs $`1` in the experiment with bit $`b` (Attack Game 5.2,
pp. 181 and 182). The bit-guessing form is half of this value (their equation (5.4)).
Attack Game 5.2 has no associated data. Boneh and Shoup add associated data to CPA security
only for ciphers with nonces (Definition 9.7, p. 378). The production message encryption
is deterministic, so it cannot satisfy this notion.

# Pseudorandom functions

Both PQXDH theorems of the next chapter assume that the key derivation of PQXDH is a
pseudorandom function (PRF): they bound the advantage of every PRF adversary against it.
The two theorems view the key derivation as a PRF in two different ways, which the next
chapter gives.

::::definition "prf_scheme" (lean := "PRFScheme") (uses := "prob_comp")
:::LibsignalVerifyBlueprint.pair PRFScheme -docstrings
Let $`\mathcal{K}`, $`X` and $`Y` be types. A _PRF scheme_ with key space $`\mathcal{K}`,
domain $`X` and range $`Y` is a pair $`(\mathrm{KeyGen}, F)` of a probabilistic computation
$`\mathrm{KeyGen}` with output in $`\mathcal{K}` and a map
$`F : \mathcal{K} \times X \to Y`.
:::
::::

In Lean, `keygen` is $`\mathrm{KeyGen}` and `eval` is $`F`. Since `eval` is a function,
evaluation is deterministic once the key is fixed.

::::definition "prf_uniform_key" (lean := "PRFScheme.UniformKey") (uses := "prf_scheme")
:::LibsignalVerifyBlueprint.pair PRFScheme.UniformKey -docstrings
Let $`(\mathrm{KeyGen}, F)` be a PRF scheme whose key space $`\mathcal{K}` is finite and
nonempty. We say that it has a _uniform key_ if $`\mathrm{KeyGen}` is the computation that
draws an element of $`\mathcal{K}` uniformly.
:::
::::

In Lean the condition is the equality of computations `prf.keygen = $ᵗ K`, where `$ᵗ K`
is the uniform sampler of the type. This is stronger than an equality of distributions: a
key generation with the uniform distribution that is written as a different computation
does not satisfy it.

::::definition "prf_adversary" (lean := "PRFScheme.PRFAdversary") (uses := "oracle_comp")
:::LibsignalVerifyBlueprint.pair PRFScheme.PRFAdversary -docstrings
Let $`X` and $`Y` be types. A _PRF adversary_ for domain $`X` and range $`Y` is an oracle
computation $`\mathcal{A}` with output in $`\{0, 1\}`, with access to uniform sampling and
to a function oracle that takes $`x \in X` and answers with an element of $`Y`.
:::
::::

The output $`1` means that $`\mathcal{A}` guesses that it talks to the scheme.

::::definition "prf_real_exp" (lean := "PRFScheme.prfRealExperiment") (uses := "prf_scheme, prf_adversary, simulate_q")
:::LibsignalVerifyBlueprint.pair PRFScheme.prfRealExperiment -docstrings
Let $`(\mathrm{KeyGen}, F)` be a PRF scheme with domain $`X` and range $`Y`, and let
$`\mathcal{A}` be a PRF adversary for $`X` and $`Y`. The _real experiment_
$`\mathsf{Real}(\mathcal{A})` runs $`\mathrm{KeyGen}` to get a key $`k`, and then runs
$`\mathcal{A}`. It answers a uniform-sampling query with a uniform draw and a function query
$`x` with $`F(k, x)`. It outputs the output of $`\mathcal{A}`.
:::
::::

::::definition "prf_ideal_exp" (lean := "PRFScheme.prfIdealExperiment") (uses := "prf_adversary, simulate_q")
:::LibsignalVerifyBlueprint.pair PRFScheme.prfIdealExperiment -docstrings
Let $`X` be a type, let $`Y` be a finite nonempty type, and let $`\mathcal{A}` be a PRF
adversary for $`X` and $`Y`. The _ideal experiment_ $`\mathsf{Ideal}(\mathcal{A})` runs
$`\mathcal{A}` with a table of answers, which is empty at the start. It answers a
uniform-sampling query with a uniform draw. It answers a function query $`x` with the entry
for $`x` if the table has one. Otherwise it draws $`y` uniformly from $`Y`, stores $`y` as
the entry for $`x`, and answers $`y`. It outputs the output of $`\mathcal{A}`.
:::
::::

In Lean, the oracle of the ideal experiment is the lazy random oracle `romImpl` of VCV-io,
run from the empty cache. The equality test on inputs needs `DecidableEq D`.

::::definition "prf_advantage" (lean := "PRFScheme.prfAdvantage") (uses := "prf_real_exp, prf_ideal_exp, eval_dist")
:::LibsignalVerifyBlueprint.pair PRFScheme.prfAdvantage -docstrings
Let $`(\mathrm{KeyGen}, F)` be a PRF scheme whose range is finite and nonempty, and let
$`\mathcal{A}` be a PRF adversary for its domain and range. The _advantage_ of
$`\mathcal{A}` is
$$`\begin{aligned}\mathrm{Adv}^{\mathrm{prf}}(\mathcal{A}) := \big|&\Pr[\mathsf{Real}(\mathcal{A}) = 1]\\ &- \Pr[\mathsf{Ideal}(\mathcal{A}) = 1]\big| \in [0, \infty],\end{aligned}`
where $`|a - b| := (a \mathbin{\dot-} b) + (b \mathbin{\dot-} a)` for
$`a, b \in [0, \infty]`, with $`\dot-` truncated subtraction.
:::
::::

In Lean the advantage is `boolDist` of the two output measures: the absolute difference of
their masses on `true`, in the extended non-negative reals.

Boneh and Shoup define PRF security for a function $`F : \mathcal{K} \times X \to Y` with
two experiments (Attack Game 4.2 and equation (4.21), pp. 132 and 133). Experiment 0 draws
a uniform key $`k` and answers a query $`x` with $`F(k, x)`. Experiment 1 answers with a
uniform function $`f : X \to Y`. The advantage is $`|\Pr[W_0] - \Pr[W_1]|`, where $`W_b` is
the event that the adversary outputs $`1` in Experiment $`b`. The definition above has the
form of equation (4.21), with two differences. The key of the real experiment comes from
$`\mathrm{KeyGen}`, which may be any computation, and the uniform key is a separate
hypothesis. The ideal experiment uses a lazy table in place of a uniform function. When
$`X` is finite, the two oracles give the same distribution of answers, but no Lean
statement in this chapter states that fact.

# Key encapsulation

The post-quantum part of PQXDH uses a key encapsulation mechanism (KEM).

::::definition "kem_scheme" (lean := "KEMScheme")
:::LibsignalVerifyBlueprint.pair KEMScheme -docstrings
Let $`m` be a monad, and let $`K`, $`\mathrm{PK}`, $`\mathrm{SK}` and $`\mathcal{C}` be
types. A _KEM_ over $`m` with key space $`K`, public-key space $`\mathrm{PK}`, secret-key
space $`\mathrm{SK}` and ciphertext space $`\mathcal{C}` is a triple
$`\Lambda = (\mathrm{KeyGen}, \mathrm{Encaps}, \mathrm{Decaps})` of

1. a computation $`\mathrm{KeyGen}` in $`m` with output in $`\mathrm{PK} \times \mathrm{SK}`,
2. for each $`\mathrm{pk} \in \mathrm{PK}`, a computation $`\mathrm{Encaps}(\mathrm{pk})` in
   $`m` with output in $`\mathcal{C} \times K`, and
3. for each $`\mathrm{sk} \in \mathrm{SK}` and $`c \in \mathcal{C}`, a computation
   $`\mathrm{Decaps}(\mathrm{sk}, c)` in $`m` with output in $`K + \{\bot\}`.
:::
::::

In Lean, $`\bot` is `none`. Decapsulation is a computation in $`m`, so it may be randomised
and, when $`m` is a monad of oracle computations, it may make oracle queries.

::::definition "kem_correctness_exp" (lean := "KEMScheme.correctnessExperiment") (uses := "kem_scheme")
:::LibsignalVerifyBlueprint.pair KEMScheme.correctnessExperiment -docstrings
Let $`\Lambda = (\mathrm{KeyGen}, \mathrm{Encaps}, \mathrm{Decaps})` be a KEM over a monad
$`m`. The _correctness experiment_ $`\mathsf{Corr}(\Lambda)` is the computation in $`m` that
runs $`\mathrm{KeyGen}` to get $`(\mathrm{pk}, \mathrm{sk})`, runs
$`\mathrm{Encaps}(\mathrm{pk})` to get $`(c, k)`, runs $`\mathrm{Decaps}(\mathrm{sk}, c)` to get $`k'`, and outputs $`1` if
$`k' = k` and $`0` otherwise.
:::
::::

::::definition "kem_perfectly_correct" (lean := "KEMScheme.PerfectlyCorrect") (uses := "kem_correctness_exp, prob_comp_runtime")
:::LibsignalVerifyBlueprint.pair KEMScheme.PerfectlyCorrect -docstrings
Let $`\Lambda` be a KEM over a monad $`m`, and let $`R` be a runtime for $`m`. We call
$`\Lambda` _perfectly correct_ under $`R` if $`\Pr_R[\mathsf{Corr}(\Lambda) = 1] = 1`.
:::
::::

::::definition "kem_correctness_error" (lean := "KEMScheme.correctnessError") (uses := "kem_correctness_exp, prob_comp_runtime")
:::LibsignalVerifyBlueprint.pair KEMScheme.correctnessError -docstrings
Let $`\Lambda` be a KEM over a monad $`m`, and let $`R` be a runtime for $`m`. The
_correctness error_ of $`\Lambda` under $`R` is
$$`\varepsilon_R(\Lambda) := 1 \mathbin{\dot-} \Pr_R[\mathsf{Corr}(\Lambda) = 1] \in [0, \infty],`
where $`\dot-` is truncated subtraction.
:::
::::

The error counts both the runs that output $`0` and the mass that the runtime loses. The
subtraction is truncated at $`0`, as in the extended non-negative reals.

::::definition "kem_delta_correct" (lean := "KEMScheme.deltaCorrect") (uses := "kem_correctness_error")
:::LibsignalVerifyBlueprint.pair KEMScheme.deltaCorrect -docstrings
Let $`\Lambda` be a KEM over a monad $`m`, let $`R` be a runtime for $`m`, and let
$`\delta \in [0, \infty]`. We call $`\Lambda` _$`\delta`-correct_ under $`R` if
$`\varepsilon_R(\Lambda) \le \delta`.
:::
::::

::::theorem "kem_correctness_error_eq_zero_iff" (lean := "KEMScheme.correctnessError_eq_zero_iff_perfectlyCorrect") (uses := "kem_correctness_error, kem_perfectly_correct")
:::LibsignalVerifyBlueprint.pair KEMScheme.correctnessError_eq_zero_iff_perfectlyCorrect (part := "signature") -docstrings
Let $`\Lambda` be a KEM over a monad $`m`, and let $`R` be a runtime for $`m`. Then
$`\varepsilon_R(\Lambda) = 0` if and only if $`\Lambda` is perfectly correct under $`R`.
:::
::::

The theorem is proved, and it has no hypothesis on $`R`: the runtime may lose mass.

Fiedler and Günther call a KEM $`\delta`-correct if, for every key pair and every
encapsulation, decapsulation fails to return the key with probability at most $`\delta`
(Definition 3.1, p. 7). They bound the error for every key pair and every encapsulation,
while the definition above averages over both. Under a runtime that loses no mass, their
notion implies the one above. The definition above allows key pairs with a large error, as
long as the average error is at most $`\delta`.

::::definition "kem_ind_cca_adversary" (lean := "KEMScheme.IND_CCA_Adversary") (uses := "kem_scheme, oracle_comp")
:::LibsignalVerifyBlueprint.pair KEMScheme.IND_CCA_Adversary -docstrings
Let $`O` be an oracle specification, and let
$`\Lambda = (\mathrm{KeyGen}, \mathrm{Encaps}, \mathrm{Decaps})` be a KEM over oracle
computations for $`O`. An _IND-CCA adversary_ against $`\Lambda` is a triple
$`\mathcal{A} = (S, \mathcal{A}_1, \mathcal{A}_2)` of a type $`S` of states and two
oracle computations: $`\mathcal{A}_1(\mathrm{pk})` for $`\mathrm{pk} \in \mathrm{PK}`,
with output in $`S`, and $`\mathcal{A}_2(\sigma, c, k)` for $`\sigma \in S`,
$`c \in \mathcal{C}` and $`k \in K`, with output in $`\{0, 1\}`. Both have access to the
oracles of $`O` and to a
decapsulation oracle, which takes $`c \in \mathcal{C}` and answers with an element of
$`K + \{\bot\}`.
:::
::::

In Lean, $`S` is the field `State`, and $`\mathcal{A}_1` and $`\mathcal{A}_2` are
`preChallenge` and `postChallenge`.

::::definition "kem_ind_cca_game" (lean := "KEMScheme.IND_CCA_Game") (uses := "kem_ind_cca_adversary, simulate_q, prob_comp_runtime")
:::LibsignalVerifyBlueprint.pair KEMScheme.IND_CCA_Game -docstrings
Let $`O` be an oracle specification, let
$`\Lambda = (\mathrm{KeyGen}, \mathrm{Encaps}, \mathrm{Decaps})` be a KEM over oracle
computations for $`O` whose key space $`K` is finite and nonempty, let $`m` be the monad
of oracle computations for $`O`, and let $`R` be a runtime for $`m`, with monad morphism
$`\iota : \mathrm{ProbComp} \to m`. Let
$`\mathcal{A} = (S, \mathcal{A}_1, \mathcal{A}_2)` be an IND-CCA adversary against
$`\Lambda`. The _IND-CCA game_ $`\mathsf{CCA}(\mathcal{A})` is the following oracle
computation for $`O` with output in $`\{0, 1\}`. Every query of $`\mathcal{A}` to $`O` is
passed on to $`O`.

1. Run $`\mathrm{KeyGen}` to get $`(\mathrm{pk}, \mathrm{sk})`.
2. Run $`\mathcal{A}_1(\mathrm{pk})`, and answer each decapsulation query $`c` with a result
   of $`\mathrm{Decaps}(\mathrm{sk}, c)`. Let $`\sigma` be its output.
3. Run $`\iota` applied to the uniform draw of a bit, to get $`b`.
4. Run $`\mathrm{Encaps}(\mathrm{pk})` to get $`(c^*, k_{\mathrm{real}})`, and run
   $`\iota` applied to the uniform draw from $`K`, to get $`k_{\mathrm{rand}}`. Let
   $`k^* = k_{\mathrm{real}}` if $`b = 1` and $`k^* = k_{\mathrm{rand}}` if $`b = 0`.
5. Run $`\mathcal{A}_2(\sigma, c^*, k^*)`. Answer the decapsulation query $`c^*` with
   $`\bot`, and each other decapsulation query $`c` with a result of
   $`\mathrm{Decaps}(\mathrm{sk}, c)`. Let $`b'` be its output.
6. Output $`1` if $`b' = b`, and $`0` otherwise.
:::
::::

In Lean, the decapsulation oracle is `IND_CCA_preChallengeImpl` in step 2 and
`IND_CCA_postChallengeImpl` in step 5. The bit $`1` is `true`.

::::definition "kem_ind_cca_advantage" (lean := "KEMScheme.IND_CCA_Advantage") (uses := "kem_ind_cca_game, bool_bias")
:::LibsignalVerifyBlueprint.pair KEMScheme.IND_CCA_Advantage -docstrings
Let $`O` be an oracle specification, let $`\Lambda` be a KEM over oracle computations for
$`O` whose key space $`K` is finite and nonempty, let $`R` be a runtime for the monad of
oracle computations for $`O`, and let $`\mathcal{A}` be an IND-CCA adversary against
$`\Lambda`. The _advantage_ of $`\mathcal{A}` under $`R` is
$$`\begin{aligned}\mathrm{Adv}^{\mathrm{cca}}_R(\mathcal{A}) := \big|&\Pr_R[\mathsf{CCA}(\mathcal{A}) = 1]\\ &- \Pr_R[\mathsf{CCA}(\mathcal{A}) = 0]\big| \in [0, \infty],\end{aligned}`
the bias of the output of $`\mathsf{CCA}(\mathcal{A})` under $`R`. Here
$`|a - b| := (a \mathbin{\dot-} b) + (b \mathbin{\dot-} a)` for $`a, b \in [0, \infty]`,
with $`\dot-` truncated subtraction.
:::
::::

In the IND-CCA game of Fiedler and Günther, the challenger draws a key pair, a bit $`b`, an
encapsulation $`(c^*, k_0)` and a uniform key $`k_1`. It gives $`(\mathrm{pk}, c^*, k_b)`
to the adversary at once. The adversary may ask for decapsulations of any ciphertext other
than $`c^*`, and it outputs a guess $`b'`. The advantage is $`|\Pr[b' = b] - \tfrac{1}{2}|`,
and they state security for adversaries with bounded time and number of queries
(Definition 3.3 and Figure 4, p. 7).

The game above differs from the game of Fiedler and Günther in three points. It has two
stages, and in the first stage the adversary may decapsulate any ciphertext. The bit $`1`
selects the real key. The advantage is the bias, so when the game loses no mass it is twice
the advantage of Fiedler and Günther, as the first chapter explains
([issue #30](https://github.com/Beneficial-AI-Foundation/libsignal-verify/issues/30)). We
do not claim that the two-stage game is equivalent to the one-stage game.

The post-quantum PQXDH theorem of the next chapter assumes that the KEM is perfectly
correct under the canonical runtime, and a bound on the IND-CCA advantage of every
adversary under that runtime. Both PQXDH theorems also assume a bound on the probability
that key generation outputs any given public key.

# The oracle Diffie-Hellman premise

The classical-security statement for the production handshake uses one more premise, about
the key derivation of PQXDH. The model theorem of the next chapter assumes instead that the
key derivation is a PRF. The premise is an assumption: this chapter states it in prose,
without a Lean card, and the repository does not prove it.

The premise adapts the PRF-ODH assumptions of Brendel, Fischlin, Günther and Janson. In
their lrPRF-ODH game (Definition 2.1), the adversary receives $`g^u` and, at the challenge,
$`g^v`. It names an input $`x^*` and receives either $`\mathrm{PRF}(g^{uv}, x^*)` or a
random value. Depending on $`l` and $`r`, it has an oracle that answers $`(S, x)` with
$`\mathrm{PRF}(S^u, x)` and an oracle that answers $`(T, x)` with $`\mathrm{PRF}(T^v, x)`.
After the challenge, the first oracle refuses $`(g^v, x^*)` and the second refuses
$`(g^u, x^*)`. Their advantage is $`2\,|\Pr[b' = b] - \tfrac{1}{2}|`.

Let $`\mathrm{agree}` be the X25519 agreement and let $`\mathrm{KDF}` be the PQXDH key
derivation, which maps an input string to three keys. The PQXDH premise is the following
game.

1. Draw two key pairs $`(a, A)` and $`(b, B)`, and give $`A` and $`B` to the adversary.
2. The adversary has an oracle on templates. A template fills the slots DH1 to DH3, an
   optional slot DH4, and the KEM secret. Each DH slot holds a 32-byte string,
   $`\mathrm{agree}(a, Y)` or $`\mathrm{agree}(b, Y)` for a point $`Y` of the adversary's
   choice. The KEM secret is a 32-byte string. The oracle forms the input and returns its
   $`\mathrm{KDF}` value.
3. The adversary names two strings $`d_1, d_2`, an optional point $`Y_4` and a KEM secret
   $`s`. The challenge input is
   $$`\mathrm{inp}^* = \mathtt{FF}^{32} \,\|\, d_1 \,\|\, d_2 \,\|\, \mathrm{agree}(a, B) \,\|\, [\mathrm{agree}(a, Y_4)] \,\|\, s.`
4. In the real world the adversary receives $`\mathrm{KDF}(\mathrm{inp}^*)`, and in the
   random world three uniform keys. After this point, the oracle refuses the input
   $`\mathrm{inp}^*`.
5. The game outputs the guess of the adversary, or false if the adversary queried
   $`\mathrm{inp}^*` before the challenge.

If an input cannot be formed, because an agreement does not return 32 bytes, the oracle
answers nothing, and at the challenge the adversary receives nothing in both worlds. The
advantage is the difference of the probabilities of output true in the two worlds. The
oracle refuses by complete input and not by point, because X25519 reads only the
u-coordinate of a point, so two encodings of a point give the same agreement.

The game differs from lrPRF-ODH in three ways. The oracle uses both secret keys $`a` and
$`b`, and a template can hold several agreements. The challenge input contains the
agreement $`\mathrm{agree}(a, B)` of the two secret keys together with strings that the
adversary chooses. The refusal is by complete input. Theorem 3.3 of Brendel, Fischlin,
Günther and Janson derives mmPRF-ODH security from a Diffie-Hellman assumption in the
random-oracle model. It does not cover this game, and the repository has no reduction from
a standard assumption to it.

A later chapter on the Rust-facing statements gives the Lean statement of this premise
([issue #79](https://github.com/Beneficial-AI-Foundation/libsignal-verify/issues/79)). The
remark on unbounded adversaries at the start of this chapter applies to it as well.
