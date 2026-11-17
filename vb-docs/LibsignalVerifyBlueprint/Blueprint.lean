import LibsignalVerifyBlueprint.VCVio
import LibsignalVerifyBlueprint.UAKE
import LibsignalVerifyBlueprint.PQXDH
import VersoBlueprint.Commands.Graph
import VersoBlueprint.Commands.Summary
open Verso.Genre Verso.Genre.Manual Informal
#doc (Manual) "Libsignal protocol verification" =>

This book states what the Lean development of this repository proves about PQXDH, the key
agreement protocol of Signal, and what it does not prove. It has two readers: a
cryptographer with little background in formal verification, and a researcher in formal
methods with little background in cryptography. Every definition and theorem is a box that
states it as a paper would. The Lean declaration that formalises the box stands beside it.
Where the Lean differs from the literature, the text after the box says how.

The first chapter introduces the part of the VCV-io library that the statements use. The
second chapter states unilaterally authenticated key exchange (UAKE), as Dodis and Fiore
define it, and the cryptographic notions that the PQXDH theorems assume. The third chapter
models PQXDH as a UAKE, and states its correctness and security theorems.

The model of PQXDH, its formulation as a UAKE, and the statements of the two security
theorems with their proof plan are the work of Galois Inc. (author Ben Hamlin). They come
from Galois's [libsignal-docs-and-models](https://github.com/GaloisInc/libsignal-docs-and-models)
at commit `e82e566ff4f1db69b2638c5813249a4d4497b14f` (copyright 2026 Galois Inc., Apache
License 2.0), through the Beneficial AI Foundation fork
[PQXDH-model](https://github.com/Beneficial-AI-Foundation/PQXDH-model) at commit
`f8625935808bff4a85f9a59f751dac81d03384ca`, which changes only the files for continuous
integration, the blueprint, documentation, Lake and scripts. Galois documents its model at
[galoisinc.github.io/libsignal-docs-and-models](https://galoisinc.github.io/libsignal-docs-and-models/).
We recommend that page to every reader of chapters 2 and 3. This repository changes the
model in several places, and the chapters say where. In particular, Bob has one identity
key, which signs and takes part in Diffie-Hellman, as in production. The module headers of
the Lean files mark the parts that an AI assistant wrote.

{include 0 LibsignalVerifyBlueprint.VCVio}

{include 0 LibsignalVerifyBlueprint.UAKE}

{include 0 LibsignalVerifyBlueprint.PQXDH}

{blueprint_graph (direction := LR)}
{blueprint_summary}
