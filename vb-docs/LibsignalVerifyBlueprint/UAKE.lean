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
function and a KEM. This chapter states the UAKE model and these notions. For each notion we
first give the definition from the literature, then the Lean definition, and then the
points where the two differ.

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
literature. It can hold only with a bound close to $`1`, so the bounds of the theorems that
assume it are trivial.
[Issue #41](https://github.com/Beneficial-AI-Foundation/libsignal-verify/issues/41) tracks this.

# Unilaterally authenticated key exchange

A UAKE protocol runs between two parties. The party $`T` holds a long-term secret key and is
authenticated. The party $`U` holds only the public key of $`T` and is not authenticated.
At the end of a run, each party outputs a session key or the symbol $`\bot`.

## Parties

DF model a party as an interactive algorithm (DF, Section 3, pp. 7 and 8). The Lean model
uses a state machine. Let $`m` be a monad and let $`\mathrm{In}`, $`W` and $`\mathrm{Out}`
be types of inputs, messages and outputs. We define a _party_ to consist of a type $`S` of
states and three maps.

* The map $`\mathrm{init} : \mathrm{In} \to m(S \times (W + 1))` gives a first state and,
  if the party speaks first, a first message.
* The map $`\mathrm{step} : S \times W \to m(R)` reads a message. The result in $`R` is one
  of three kinds. The party accepts the message and sends a reply, with a new state and a
  flag $`\mathrm{done}` that says whether this was its last step. Or the party completes
  with a new state and sends nothing. Or the party rejects the message.
* The map $`\mathrm{output} : S \to m(\mathrm{Out} + 1)` gives the output of the party, or
  nothing if the party has not finished.

In a UAKE scheme, $`\mathrm{Out} = K + \{\bot\}` for a type $`K` of session keys. Such a
party is a Mealy machine with an output map: the reply to a message depends on the current
state and on the message.

::::definition "uake_party" (lean := "AKE.UAKE.Party") (uses := "prob_comp")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.Party -docstrings
The results of `init` and `step` are the inductive types `Party.InitResult`, with the
constructors `speakFirst` and `waitForMsg`, and `Party.StepResult`, with the constructors
`acceptAndSend`, `complete` and `reject`. A UAKE party has `Out = Option K`, so
`output` returns a value of type `Option (Option K)`. The outer `none` means that the party
has not finished, and the inner `none` stands for $`\bot`.
:::
::::

Two conditions make the output of a party well behaved. We say that a party _outputs only
at completion_ if, on every reachable state, the output is defined exactly when the party
has finished. After $`\mathrm{init}` the output is not defined. After a step that completes,
or that accepts with $`\mathrm{done} = \mathrm{true}`, the output is defined. After a step
that accepts with $`\mathrm{done} = \mathrm{false}`, it is not defined.

::::definition "uake_outputs_only_at_completion" (lean := "AKE.UAKE.Party.OutputsOnlyAtCompletion") (uses := "uake_party")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.Party.OutputsOnlyAtCompletion -docstrings
The Lean definition reads "reachable" as "in the support of a call to `init` or `step`".
The three clauses quantify over such states.
:::
::::

We say that a party has _pure output_ if $`\mathrm{output}(s)` is a fixed value for each
state $`s`, with no effect in $`m`.

::::definition "uake_pure_output" (lean := "AKE.UAKE.Party.PureOutput") (uses := "uake_party")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.Party.PureOutput -docstrings
The condition is that for each state `st` there is a value `out` with
`P.output st = pure out`.
:::
::::

## Transcripts and matching

A global clock counts the messages of an execution. Every message that a party sends or
receives gets the current time as a timestamp. We define the _transcript_ of a session to be
the list of pairs $`(M_i, t_i)` of the messages of the session, sent and received, with
their timestamps (DF, Definition 2, p. 6).

::::definition "uake_transcript" (lean := "AKE.UAKE.Transcript")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.Transcript -docstrings
The field `entries` holds the list of pairs of type `W × ℕ`.
:::
::::

Let $`T = \langle (M_1, t_1), \dots, (M_n, t_n) \rangle` and
$`T^* = \langle (M^*_1, t^*_1), \dots, (M^*_n, t^*_n) \rangle` be two transcripts. We say
that $`T` _matches_ $`T^*` if $`M_i = M^*_i` for every $`i` and the two timestamp sequences
alternate (DF, Definition 3, p. 6). If the party of $`T` speaks first, the condition is
$$`t_1 < t^*_1 < t^*_2 < t_2 < t_3 < \dots`
and if the party of $`T^*` speaks first, it is
$$`t^*_1 < t_1 < t_2 < t^*_2 < t^*_3 < \dots`
In words, every message that one party sends is received by the other party at a later
time. The relation is not symmetric.

::::definition "uake_matching" (lean := "AKE.UAKE.Matching") (uses := "uake_transcript")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.Matching -docstrings
The Boolean argument says which party speaks first. The Lean definition asks that the two
lists of messages are equal and that the interleaved list of timestamps is strictly
increasing.
:::
::::

In the security experiment below, $`T^*` is the transcript of the challenge session with
$`U`, and $`T_1, \dots, T_Q` are the transcripts of the sessions that the adversary opens
with copies of $`T`. We call the adversary _ping-pong_ if some $`T_j` matches $`T^*` (DF,
Definition 4, p. 7). A ping-pong adversary has relayed every message of the challenge
session between $`U` and one copy of $`T`, unchanged and in order.

::::definition "uake_ping_pong" (lean := "AKE.UAKE.pingPong") (uses := "uake_matching")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.pingPong -docstrings
The first argument says which party speaks first. The second is the list of oracle
transcripts, and the third is the challenge transcript.
:::
::::

## Schemes and correctness

DF define a UAKE protocol as three algorithms (DF, Section 3, pp. 7 and 8). A setup
algorithm outputs a key pair $`(\mathrm{uk}, \mathrm{tk})` and defines the space $`K` of
session keys. The party $`U` runs on $`\mathrm{uk}`, and the party $`T` runs on
$`\mathrm{tk}`. DF assume without loss of generality that $`T` speaks last.

We define a _UAKE scheme_ to consist of a number $`r` of messages in an honest run, a setup
computation in $`m(\mathrm{UK} \times \mathrm{TK})`, a party $`U` with input type
$`\mathrm{UK}`, and a party $`T` with input type $`\mathrm{TK}`. Both parties output a key
in $`K` or $`\bot`.

::::definition "uake_scheme" (lean := "AKE.UAKE.Scheme") (uses := "uake_party")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.Scheme -docstrings
The field `rounds` is the number $`r`. The security experiment reads the first speaker from
its parity, as the docstring of the field explains.
:::
::::

DF call a protocol _correct_ if, for all key pairs from setup and all runs with outputs
$`K_U` and $`K_T`, the equality $`K_U = K_T` holds with all but negligible probability when
$`K_U \neq \bot` and $`K_T \neq \bot` (DF, Definition 7, p. 8). The Lean model states the
probability-one case. We define the _correctness experiment_ to run setup, run $`U` and
$`T` honestly against each other for at most $`r + 1` steps, and output true if one of the
parties has no key or the two keys are equal.

::::definition "uake_correct_exp" (lean := "AKE.UAKE.CorrectExp") (uses := "uake_scheme")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.CorrectExp -docstrings
The honest run is `Party.runHonest` with $`r + 1` steps. The value `uOut.join` is `none`
both when $`U` has not finished and when $`U` output $`\bot`, and the same holds for
$`T`.
:::
::::

We call a scheme _perfectly correct_ under a runtime if the correctness experiment outputs
true with probability $`1`.

::::definition "uake_perfectly_correct" (lean := "AKE.UAKE.PerfectlyCorrect") (uses := "uake_correct_exp, prob_comp_runtime")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.PerfectlyCorrect -docstrings
A scheme in which both parties always output $`\bot` satisfies this definition. Honest
completion is a separate condition, below.
:::
::::

The Lean definition differs from DF Definition 7 in two points. It asks for probability
$`1`, where DF allow a negligible error. Also, a party that has not finished after
$`r + 1` steps counts as a party with output $`\bot`, so such a run is correct. In both
definitions a run with output $`\bot` is correct.
[Issue #72](https://github.com/Beneficial-AI-Foundation/libsignal-verify/issues/72) tracks
the correctness of the production PQXDH handshake, which this notion does not cover.

## Admissible schemes

Three further conditions restrict the schemes that the PQXDH theorems consider. DF have
none of them as a separate definition.

We call a scheme _well formed_ if both parties output only at completion and have pure
output, and if every honest run from setup sends exactly $`r` messages.

::::definition "uake_well_formed" (lean := "AKE.UAKE.Scheme.WellFormed") (uses := "uake_scheme, uake_outputs_only_at_completion, uake_pure_output")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.Scheme.WellFormed -docstrings
The condition does not ask that $`T` speaks last.
:::
::::

We say that a scheme _completes honestly_ under a runtime if, with probability $`1`, an
honest run from setup ends with a key at both parties.

::::definition "uake_honestly_completes" (lean := "AKE.UAKE.Scheme.HonestlyCompletes") (uses := "uake_scheme, prob_comp_runtime")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.Scheme.HonestlyCompletes -docstrings
The experiment `HonestCompletionExp` runs setup and the honest run, and outputs true when
both outputs are keys.
:::
::::

The model is generic in the monad $`m`, and a runtime gives the probability semantics of
$`m` (see the first chapter). We call a runtime _coherent_ if the following four conditions
hold:

* Its semantics is lawful.
* Its measure is the measure of the monad.
* A probabilistic computation keeps its distribution when it is lifted into $`m`.
* Every observed output lies in the support almost surely.

::::definition "uake_runtime_coherent" (lean := "AKE.UAKE.RuntimeCoherent") (uses := "prob_comp_runtime, eval_dist")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.RuntimeCoherent -docstrings
The four fields are `lawful`, `evalDist_eq`, `lift_evalDist_eq` and `ae_mem_support`.
:::
::::

::::theorem "uake_runtime_coherent_prob_comp" (lean := "AKE.UAKE.runtimeCoherent_probComp") (uses := "uake_runtime_coherent")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.runtimeCoherent_probComp (part := "signature") -docstrings
The runtime of probabilistic computations, `ProbCompRuntime.probComp`, is coherent.
:::
::::

We call a scheme _admissible_ under a runtime if the runtime is coherent and the scheme is
well formed, perfectly correct and completes honestly.

::::definition "uake_admissible" (lean := "AKE.UAKE.Scheme.Admissible") (uses := "uake_runtime_coherent, uake_well_formed, uake_perfectly_correct, uake_honestly_completes")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.Scheme.Admissible -docstrings
No condition involves an adversary.
:::
::::

Admissibility does not imply that the security experiment below loses no mass against an
adversary. Under a runtime that loses mass, the lost mass lowers the probability of output
true. The advantage can then be large with no attack, or small against an attack that always
wins.
[Issue #29](https://github.com/Beneficial-AI-Foundation/libsignal-verify/issues/29) tracks
this. The PQXDH theorems use `ProbCompRuntime.probComp`, which loses no mass.

## The security experiment

DF combine authenticity and key secrecy in one experiment (DF, Section 3, p. 8). The
adversary $`\mathcal{A}` runs one challenge session with $`U` and can open any number of
sessions with copies of $`T`. After $`T` sends its last message in a session, the adversary
may ask $`T` to reveal its key. If it does so in a session that matches the challenge
session, we call it _full-ping-pong_. The experiment runs as follows.

1. Run setup to get $`(\mathrm{uk}, \mathrm{tk})`, and draw a uniform bit $`b`.
2. Run $`U(\mathrm{uk})` against $`\mathcal{A}(\mathrm{uk})`, where $`\mathcal{A}` has
   oracle access to copies of $`T(\mathrm{tk})`. Let $`K_0` be the output of $`U`.
3. If $`K_0 = \bot`, set $`K_1 = \bot`.
4. Else, if $`\mathcal{A}` is not ping-pong, output $`1`. The adversary has made $`U`
   accept without relaying, and so it has broken authenticity.
5. Else, draw $`K_1` uniformly from $`K`.
6. Give $`K_b` to $`\mathcal{A}`, which keeps its oracle access to $`T`, and let $`b'` be
   its guess.
7. If $`\mathcal{A}` is full-ping-pong, output a uniform bit. Else output $`1` if
   $`b' = b`, and $`0` otherwise.

The advantage of $`\mathcal{A}` is $`|\Pr[\text{output } 1] - \tfrac{1}{2}|`, and DF call
the protocol secure if every efficient adversary has negligible advantage (DF,
Definition 8, p. 9).

The Lean model gives the adversary four queries, besides uniform sampling. The query
$`\mathrm{openT}` starts a new session with a copy of $`T` and returns its number and the
first message of $`T`, if $`T` speaks first. The query $`\mathrm{stepT}(i, w)` sends $`w`
to session $`i` and returns the reply. The query $`\mathrm{revealT}(i)` returns the key of
session $`i` once the session has finished. The query $`\mathrm{stepChallenge}(w)` sends
$`w` to $`U` in the challenge session.

::::definition "uake_oracle_spec" (lean := "AKE.UAKE.oracleSpec") (uses := "oracle_spec")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.oracleSpec -docstrings
The index type is the inductive type `AKE.UAKE.Op W` of the four queries. The answer
`inr ()` to a step query means that no reply was sent.
:::
::::

::::definition "uake_op_impl" (lean := "AKE.UAKE.opImpl") (uses := "uake_oracle_spec, uake_scheme, uake_transcript, query_impl")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.opImpl -docstrings
The state is an environment of type `Env`: the clock, the challenge session, a flag that
says whether the challenge session has finished, and the list of sessions with $`T`. Each
accepted message and each reply gets a timestamp. A rejected message changes nothing: it
does not enter the transcript, and the session stays open.
:::
::::

We define an _adversary_ to consist of a type of states and two computations with the
oracles above. The first takes $`\mathrm{uk}` and the first message of $`U`, if any, and
runs the challenge session. The second takes the state and the key $`K_b` and outputs the
guess $`b'`.

::::definition "uake_adversary" (lean := "AKE.UAKE.Adversary") (uses := "uake_oracle_spec, oracle_comp")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.Adversary -docstrings
The two computations are `challenge` and `post`. The key passed to `post` has type
`Option K`, where `none` stands for $`\bot`.
:::
::::

::::definition "uake_exp" (lean := "AKE.UAKE.Exp") (uses := "uake_adversary, uake_op_impl, uake_ping_pong, simulate_q")
:::LibsignalVerifyBlueprint.pair AKE.UAKE.Exp -docstrings
The function `challengeSession` runs step 2, and `isPingPong` decides step 4. The function
`finalize` closes the challenge session and runs steps 6 and 7. It decides
full-ping-pong with `fullPingPong`, which keeps only the revealed sessions with $`T`.
:::
::::

The advantage of this experiment is the card `uake_advantage` of the first chapter. It is
$`|\Pr[\mathsf{Exp} = \mathrm{true}] - \tfrac{1}{2}|` as in DF Definition 8.

The experiment follows DF step by step. The Lean model differs from DF in the following
points.

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

# Joint unforgeability of signatures

Let $`(\mathrm{KeyGen}, \mathrm{Sign}, \mathrm{Verify})` be a signature scheme. In the
EUF-CMA game, the challenger draws a key pair $`(\mathrm{pk}, \mathrm{sk})` and gives
$`\mathrm{pk}` to the adversary. The adversary asks for signatures on messages of its
choice and outputs a pair $`(m, \sigma)`. It wins if $`\sigma` is a valid signature on $`m`
and $`m` is not one of the signed messages. The advantage is the probability that it wins
(Boneh and Shoup, Attack Game 13.1, pp. 529 and 530).

In PQXDH, the signing key of the identity key is also a Diffie-Hellman key. We define the
_joint unforgeability game_ for a map $`\mathrm{agree} : \mathrm{SK} \times X \to Y` to be
the EUF-CMA game in which the adversary has a second oracle $`x \mapsto \mathrm{agree}(\mathrm{sk}, x)`
on the same secret key. The game does not record the queries to this second oracle. These
queries put no condition on the forgery.

::::definition "sig_joint_adversary" (lean := "SignatureAlg.JointAdversary") (uses := "oracle_comp")
:::LibsignalVerifyBlueprint.pair SignatureAlg.JointAdversary -docstrings
The oracles are those of `SignatureAlg.JointSpec`: uniform sampling, signing, and the map
`agree sk`.
:::
::::

::::definition "sig_joint_exp" (lean := "SignatureAlg.jointUnforgeableExp") (uses := "sig_joint_adversary, simulate_q")
:::LibsignalVerifyBlueprint.pair SignatureAlg.jointUnforgeableExp -docstrings
The function `SignatureAlg.jointImpl` implements the oracles and records the signed messages.
:::
::::

::::definition "sig_joint_advantage" (lean := "SignatureAlg.JointAdversary.advantage") (uses := "sig_joint_exp, eval_dist")
:::LibsignalVerifyBlueprint.pair SignatureAlg.JointAdversary.advantage -docstrings
The advantage is the probability that the game outputs true, in $`[0, \infty]`.
:::
::::

Without the second oracle, the game is Attack Game 13.1. The word joint refers to the second
oracle, which Attack Game 13.1 does not have.

# The gap Diffie-Hellman problem

Let $`F` be a field, let $`G` be a vector space over $`F`, and let $`g \in G`. We write the
group additively, so $`x \cdot g` is the multiple of $`g` by $`x \in F`. We call a triple
$`(X, Y, Z)` a _Diffie-Hellman triple_ if there are $`x, y \in F` with $`X = x \cdot g`,
$`Y = y \cdot g` and $`Z = (xy) \cdot g`.

::::definition "dh_is_dh" (lean := "DiffieHellman.IsDH")
:::LibsignalVerifyBlueprint.pair DiffieHellman.IsDH -docstrings
The predicate is the existential statement above.
:::
::::

In the _gap Diffie-Hellman game_, the challenger draws $`a` and $`b` uniformly from $`F`
and gives $`(g, a \cdot g, b \cdot g)` to the adversary. The adversary may ask whether any
triple of its choice is a Diffie-Hellman triple, and it outputs an element $`h \in G`. It
wins if $`h = (ab) \cdot g`. The advantage is the probability that it wins.

::::definition "dh_gap_adversary" (lean := "DiffieHellman.GapDHAdversary") (uses := "oracle_comp")
:::LibsignalVerifyBlueprint.pair DiffieHellman.GapDHAdversary -docstrings
An adversary is a computation with uniform sampling and the decision oracle on triples.
:::
::::

::::definition "dh_ddh_oracle" (lean := "DiffieHellman.ddhOracle") (uses := "dh_is_dh, query_impl")
:::LibsignalVerifyBlueprint.pair DiffieHellman.ddhOracle -docstrings
The oracle answers a triple with the truth value of `IsDH`.
:::
::::

::::definition "dh_gap_exp" (lean := "DiffieHellman.gapDHExp") (uses := "dh_gap_adversary, dh_ddh_oracle, simulate_q")
:::LibsignalVerifyBlueprint.pair DiffieHellman.gapDHExp -docstrings
The game draws the exponents with `$ᵗ F`.
:::
::::

::::definition "dh_gap_advantage" (lean := "DiffieHellman.gapDHAdvantage") (uses := "dh_gap_exp, eval_dist")
:::LibsignalVerifyBlueprint.pair DiffieHellman.gapDHAdvantage -docstrings
The advantage is a real number.
:::
::::

Boneh and Shoup state the interactive computational Diffie-Hellman problem for a cyclic
group (Attack Game 12.3 and Definition 12.4, pp. 479 and 480). In that game the oracle
decides only triples whose first component is the fixed element $`a \cdot g`. The oracle of
the Lean game decides arbitrary triples, so the Lean assumption is stronger. The Lean group
is a vector space over a field, and the scalars are drawn from the whole field.

# Authenticated encryption

Let $`\mathcal{K}`, $`\mathcal{M}`, $`\mathcal{D}` and $`\mathcal{C}` be the sets of keys,
messages, associated data and ciphertexts. Boneh and Shoup define a cipher with associated
data and no nonces as a pair $`(E, D)` (Section 9.6, p. 380). The encryption $`E(k, m, d)`
may be probabilistic, and the decryption $`D(k, c, d)` outputs a message or reject. The
pair is correct if $`\Pr[D(k, E(k, m, d), d) = m] = 1`.

We define an _AEAD scheme_ to be such a pair, with $`E` a probabilistic computation and
$`D` a function. We call it _perfectly correct_ if, for every message $`m` and associated
data $`d`, a uniform key $`k` gives $`D(k, E(k, m, d), d) = m` with probability $`1`.

::::definition "aead_scheme" (lean := "AEAD.Scheme") (uses := "prob_comp")
:::LibsignalVerifyBlueprint.pair AEAD.Scheme -docstrings
The decryption returns `none` for reject.
:::
::::

::::definition "aead_perfectly_correct" (lean := "AEAD.PerfectlyCorrect") (uses := "aead_scheme, eval_dist")
:::LibsignalVerifyBlueprint.pair AEAD.PerfectlyCorrect -docstrings
The experiment `AEAD.CorrectExp` draws the key uniformly, encrypts, and tests that
decryption returns the message.
:::
::::

## Ciphertext integrity

In the ciphertext integrity game, the challenger draws a uniform key $`k`. The adversary
asks for encryptions of pairs $`(d_i, m_i)` and receives $`c_i`. It outputs a pair
$`(d, c)` that is not one of the pairs $`(d_i, c_i)`, and it wins if $`D(k, c, d)` is not
reject. The advantage is the probability that it wins (Boneh and Shoup, Attack Game 9.1,
pp. 358 and 359, with associated data as in Attack Game 9.3, p. 379).

::::definition "aead_int_ctxt_game" (lean := "AEAD.INT_CTXT_Game") (uses := "aead_scheme, simulate_q")
:::LibsignalVerifyBlueprint.pair AEAD.INT_CTXT_Game -docstrings
The encryption oracle is `AEAD.ctxtImpl`, which records each pair of associated data and
ciphertext. The adversary type is `AEAD.INT_CTXT_Adversary`.
:::
::::

::::definition "aead_int_ctxt_advantage" (lean := "AEAD.INT_CTXT_Advantage") (uses := "aead_int_ctxt_game, eval_dist")
:::LibsignalVerifyBlueprint.pair AEAD.INT_CTXT_Advantage -docstrings
The advantage is the probability that the game outputs true, as a real number.
:::
::::

The PQXDH theorems use a variant with a decryption oracle. In the _decryption game_ the
adversary has the encryption oracle and an oracle that returns $`D(k, c, d)` for any pair
$`(d, c)`. It outputs nothing. It wins if one of its decryption queries is a pair that the
encryption oracle did not return, and the decryption of that pair is not reject. Boneh and
Shoup do not have this game.

::::definition "aead_int_ctxt_d_game" (lean := "AEAD.INT_CTXT_D_Game") (uses := "aead_scheme, simulate_q")
:::LibsignalVerifyBlueprint.pair AEAD.INT_CTXT_D_Game -docstrings
The oracles are `AEAD.ctxtDecImpl`. Its state holds the list of encryptions and a flag that
becomes true at the first winning decryption query.
:::
::::

::::definition "aead_int_ctxt_d_advantage" (lean := "AEAD.INT_CTXT_D_Advantage") (uses := "aead_int_ctxt_d_game, eval_dist")
:::LibsignalVerifyBlueprint.pair AEAD.INT_CTXT_D_Advantage -docstrings
The advantage is the probability that the game outputs true, as a real number.
:::
::::

The two games are related in both directions. An adversary in the plain game gives an
adversary in the decryption game that sends the forgery to the decryption oracle. The new
adversary has the same advantage.

::::theorem "aead_int_ctxt_le_int_ctxt_d" (lean := "AEAD.INT_CTXT_Advantage_le_INT_CTXT_D_Advantage") (uses := "aead_int_ctxt_advantage, aead_int_ctxt_d_advantage")
:::LibsignalVerifyBlueprint.pair AEAD.INT_CTXT_Advantage_le_INT_CTXT_D_Advantage (part := "signature") -docstrings
For every adversary $`\mathcal{A}`,
$`\mathrm{Adv}^{\mathrm{ctxt}}(\mathcal{A}) \le \mathrm{Adv}^{\mathrm{ctxt\text{-}d}}(\mathrm{ctxtToDec}(\mathcal{A}))`.
:::
::::

In the other direction, the reduction guesses which decryption query wins. The bound
therefore has a factor $`v`, the number of decryption queries.

::::theorem "aead_int_ctxt_d_le_mul_int_ctxt" (lean := "AEAD.INT_CTXT_D_Advantage_le_mul_INT_CTXT_Advantage") (uses := "aead_int_ctxt_advantage, aead_int_ctxt_d_advantage, aead_perfectly_correct")
:::LibsignalVerifyBlueprint.pair AEAD.INT_CTXT_D_Advantage_le_mul_INT_CTXT_Advantage (part := "signature") -docstrings
Let the scheme be perfectly correct, and let $`\mathcal{B}` make at most $`v` decryption
queries. Then
$`\mathrm{Adv}^{\mathrm{ctxt\text{-}d}}(\mathcal{B}) \le v \cdot \mathrm{Adv}^{\mathrm{ctxt}}(\mathrm{decToCtxt}(\mathcal{B}))`.
The pair `fallback` is the output of the reduction when it has nothing to output, so the
theorem needs a pair of associated data and ciphertext.
:::
::::

The file also defines a third game, `AEAD.INT_CTXT_VF_Game`, with an oracle that only says
whether a pair decrypts, and two similar theorems for it. The PQXDH theorems assume a bound
on the advantage in the decryption game directly and use none of these four theorems. The
reductions count encryption and decryption queries, but not running time.

## Indistinguishability

The repository also defines IND-CPA security as a reference notion. In the game, the
challenger draws a uniform key and a uniform bit $`b`. The adversary sends triples
$`(d, m_0, m_1)` with $`m_0` and $`m_1` of the same length and receives an encryption of
$`m_b` with associated data $`d`. It outputs a guess $`b'` and wins if $`b' = b`. The
advantage is $`|\Pr[b' = b] - \tfrac{1}{2}|`.

::::definition "aead_ind_cpa_game" (lean := "AEAD.IND_CPA_Game") (uses := "aead_scheme, simulate_q")
:::LibsignalVerifyBlueprint.pair AEAD.IND_CPA_Game -docstrings
The challenge queries have type `AEAD.EqualLengthChallenge`, and the oracle is
`AEAD.cpaImpl`.
:::
::::

::::definition "aead_ind_cpa_advantage" (lean := "AEAD.IND_CPA_Advantage") (uses := "aead_ind_cpa_game, eval_dist")
:::LibsignalVerifyBlueprint.pair AEAD.IND_CPA_Advantage -docstrings
The advantage is a real number.
:::
::::

Boneh and Shoup define the advantage as $`|\Pr[W_0] - \Pr[W_1]|`, where $`W_b` is the event
that the adversary outputs $`1` in the experiment with bit $`b` (Attack Game 5.2,
pp. 181 and 182). The bit-guessing form is half of this value (their equation (5.4)). The
production message encryption is deterministic, so it cannot satisfy this notion. No PQXDH
theorem uses the notion.

# Pseudorandom functions

Let $`F : \mathcal{K} \times X \to Y` be a function. In the PRF game, Experiment 0 draws a
uniform key $`k` and answers queries $`x` with $`F(k, x)`. Experiment 1 answers with a
uniform function $`f : X \to Y`. The advantage of an adversary is
$`|\Pr[W_0] - \Pr[W_1]|`, where $`W_b` is the event that it outputs $`1` in Experiment
$`b` (Boneh and Shoup, Attack Game 4.2 and equation (4.21), pp. 132 and 133).

We define a _PRF scheme_ to consist of a key generation computation and an evaluation map.
We say that it has a _uniform key_ if its key generation is uniform sampling.

::::definition "prf_scheme" (lean := "PRFScheme")
:::LibsignalVerifyBlueprint.pair PRFScheme -docstrings
The fields are `keygen` and `eval`.
:::
::::

::::definition "prf_uniform_key" (lean := "PRFScheme.UniformKey") (uses := "prf_scheme")
:::LibsignalVerifyBlueprint.pair PRFScheme.UniformKey -docstrings
The condition is `prf.keygen = $ᵗ K`.
:::
::::

::::definition "prf_real_exp" (lean := "PRFScheme.prfRealExperiment") (uses := "prf_scheme, simulate_q")
:::LibsignalVerifyBlueprint.pair PRFScheme.prfRealExperiment -docstrings
The key comes from `keygen`, not from uniform sampling.
:::
::::

::::definition "prf_ideal_exp" (lean := "PRFScheme.prfIdealExperiment") (uses := "simulate_q")
:::LibsignalVerifyBlueprint.pair PRFScheme.prfIdealExperiment -docstrings
The oracle is a lazy random oracle. It draws a uniform answer at the first query on each
input and stores it for later queries.
:::
::::

::::definition "prf_advantage" (lean := "PRFScheme.prfAdvantage") (uses := "prf_real_exp, prf_ideal_exp, eval_dist")
:::LibsignalVerifyBlueprint.pair PRFScheme.prfAdvantage -docstrings
The value is `boolDist` of the two measures: the absolute difference of their masses on
true, in $`[0, \infty]`.
:::
::::

The advantage has the form of equation (4.21). A lazy random oracle gives the same
distribution of answers as a uniform function. A PRF scheme may have any key generation,
and the condition `UniformKey` is a separate hypothesis.

# Key encapsulation

A KEM consists of a key generation, an encapsulation that outputs a ciphertext and a key,
and a decapsulation that outputs a key or fails. Fiedler and Günther call a KEM
$`\delta`-correct if, for every key pair and every encapsulation, decapsulation fails to
return the key with probability at most $`\delta` (Definition 3.1, p. 7).

::::definition "kem_scheme" (lean := "KEMScheme") (uses := "prob_comp")
:::LibsignalVerifyBlueprint.pair KEMScheme -docstrings
The decapsulation returns `none` for failure.
:::
::::

We define the _correctness experiment_ to draw a key pair, encapsulate, decapsulate, and
output whether decapsulation returned the key. We call the KEM _perfectly correct_ under a
runtime if this experiment outputs true with probability $`1`.

::::definition "kem_perfectly_correct" (lean := "KEMScheme.PerfectlyCorrect") (uses := "kem_scheme, prob_comp_runtime")
:::LibsignalVerifyBlueprint.pair KEMScheme.PerfectlyCorrect -docstrings
The experiment is `KEMScheme.correctnessExperiment`.
:::
::::

We define the _correctness error_ to be $`1` minus the probability that the correctness
experiment outputs true, and we call the KEM _$`\delta`-correct_ if this error is at most
$`\delta`.

::::definition "kem_correctness_error" (lean := "KEMScheme.correctnessError") (uses := "kem_perfectly_correct")
:::LibsignalVerifyBlueprint.pair KEMScheme.correctnessError -docstrings
The error counts both the runs that output false and the mass that the runtime loses.
:::
::::

::::definition "kem_delta_correct" (lean := "KEMScheme.deltaCorrect") (uses := "kem_correctness_error")
:::LibsignalVerifyBlueprint.pair KEMScheme.deltaCorrect -docstrings
The bound $`\delta` lies in $`[0, \infty]`.
:::
::::

::::theorem "kem_correctness_error_eq_zero_iff" (lean := "KEMScheme.correctnessError_eq_zero_iff_perfectlyCorrect") (uses := "kem_correctness_error, kem_perfectly_correct")
:::LibsignalVerifyBlueprint.pair KEMScheme.correctnessError_eq_zero_iff_perfectlyCorrect (part := "signature") -docstrings
The correctness error is $`0` if and only if the KEM is perfectly correct.
:::
::::

Fiedler and Günther bound the error for every key pair and every encapsulation, while the
Lean notion averages over both. Under a runtime that loses no mass, their notion implies the
Lean notion. The Lean notion allows key pairs with a large error, as long as the average
error is at most $`\delta`.

In the IND-CCA game of Fiedler and Günther, the challenger draws a key pair, a bit $`b`, an
encapsulation $`(c^*, k_0)` and a uniform key $`k_1`. It gives $`(\mathrm{pk}, c^*, k_b)`
to the adversary at once. The adversary may ask for decapsulations of any ciphertext other
than $`c^*`, and it outputs a guess $`b'`. The advantage is $`|\Pr[b' = b] - \tfrac{1}{2}|`,
and they state security for adversaries with bounded time and number of queries
(Definition 3.3 and Figure 4, p. 7).

The VCV-io game has two stages. In the first stage the adversary receives $`\mathrm{pk}`
and may decapsulate any ciphertext. In the second stage it receives $`(c^*, k)` and may
decapsulate any ciphertext other than $`c^*`. The key $`k` is the encapsulated key when the
bit is true and a uniform key when it is false. The game outputs whether the guess equals
the bit.

::::definition "kem_ind_cca_game" (lean := "KEMScheme.IND_CCA_Game") (uses := "kem_scheme, simulate_q, prob_comp_runtime")
:::LibsignalVerifyBlueprint.pair KEMScheme.IND_CCA_Game -docstrings
The decapsulation oracle is `IND_CCA_preChallengeImpl` in the first stage and
`IND_CCA_postChallengeImpl` in the second. The second refuses $`c^*`.
:::
::::

::::definition "kem_ind_cca_advantage" (lean := "KEMScheme.IND_CCA_Advantage") (uses := "kem_ind_cca_game, bool_bias")
:::LibsignalVerifyBlueprint.pair KEMScheme.IND_CCA_Advantage -docstrings
The advantage is the bias of the game, in $`[0, \infty]`.
:::
::::

We do not claim that the two-stage game is equivalent to the one-stage game of Fiedler and
Günther. When the game loses no mass, the bias is twice their advantage, as the first
chapter explains
([issue #30](https://github.com/Beneficial-AI-Foundation/libsignal-verify/issues/30)).

# The oracle Diffie-Hellman premise

The classical-security theorem for PQXDH uses one more premise, about the key derivation
of PQXDH. It adapts the PRF-ODH assumptions of Brendel, Fischlin, Günther and Janson. In
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
