# Libsignal protocol verification: the blueprint book

This directory holds a book, written with [Verso Blueprint](https://github.com/leanprover/verso-blueprint),
that states what the Lean development of this repository proves about PQXDH, the key
agreement protocol of Signal, and what it does not prove. It has two readers: a
cryptographer with little background in formal verification, and a researcher in formal
methods with little background in cryptography.

Every definition and theorem is a box that states it as a paper would. The Lean declaration
that formalises the box stands beside it. Where the Lean differs from the literature, the text
after the box says how.

## Chapters

1. **VCV-io, a quick introduction.** The part of the [VCV-io](https://github.com/Verified-zkEVM/VCV-io)
   library that the statements use: oracle computations, probabilities, runtimes, and the
   advantage of a UAKE adversary. Three small programs, drawn as trees, serve as worked
   examples. Their Lean code is `LibsignalVerifyBlueprint/ProbTrees.lean`.
2. **UAKE and the primitives.** Unilaterally authenticated key exchange, as Dodis and Fiore
   define it, and the cryptographic notions that the PQXDH theorems assume: signatures with a
   joint unforgeability game, Gap Diffie-Hellman, AEAD, PRFs and KEMs.
3. **PQXDH.** The model of PQXDH, its formulation as a UAKE, its correctness and
   well-formedness theorems, the two security theorems with the six hops of their proof, and
   the places where the model differs from the specification.

## Credits

The model of PQXDH, its formulation as a UAKE, and the statements of the two security
theorems with their proof plan are the work of Galois Inc. (author Ben Hamlin). They come from
[libsignal-docs-and-models](https://github.com/GaloisInc/libsignal-docs-and-models). Galois
documents its model at
[galoisinc.github.io/libsignal-docs-and-models](https://galoisinc.github.io/libsignal-docs-and-models/).
The introduction of the book gives the commits.

## Building and viewing the book

The book is its own Lake package. It reads the Lean development of the enclosing repository
and pins VersoBlueprint in `lakefile.lean`. Run both commands from this directory, because
the code cards run `lake build subverso-extract-mod` in the working directory:

```
lake build LibsignalVerifyBlueprint
lake exe vbp build
```

The first command checks the book and the Lean it refers to. The second writes the site to
`_out/site/html-multi`, which is not committed. Serve that folder with any static file server,
for example `python3 -m http.server --directory _out/site/html-multi 8000`, and open
`http://127.0.0.1:8000/`.

The pictures of the trees are the SVG files in `figures/`. A box of the directive `treePair`
names one of them, and the renderer reads it from the working directory and writes it into the
page, so the site needs no other file. Run the renderer from this directory.

## Publishing the book

The book is published on GitHub Pages by the repository
[libsignal-verify-docs](https://github.com/Beneficial-AI-Foundation/libsignal-verify-docs). That
repository holds no source of the book. It holds a workflow, run by hand, that checks out one
commit of this repository, builds the book and deploys it. Two parts of this directory serve that
workflow:

- **`source-revision`.** The link "Source file" of a code card names a commit of this repository.
  The renderer reads the commit from the file `source-revision` in this directory when it writes
  the site, so a compiled book never names a stale commit. The workflow writes the file with the
  commit that it checked out. The file is not committed. Without it, the links name
  `defaultSourceRevision` in `LibsignalVerifyBlueprint/Code.lean`. The file must hold one
  40-digit lowercase hexadecimal hash.
- **`scripts/export-public.py`.** The build writes the absolute path of the build directory into
  `xref.json`, `-verso-data/blueprint-manifest.json` and, as embedded data, `find/index.html`.
  The script copies `_out/site/html-multi` to a publication folder and rewrites each such path to
  a path relative to the repository root. It fails if a path under `/Users/` or `/home/` remains.
  It also fails if a source link names a commit other than `source-revision`.

To check what would be published, render the book, export it and serve the copy:

```
lake exe vbp build
python3 scripts/export-public.py --destination /tmp/book-site
python3 -m http.server --directory /tmp/book-site 8000
```

## How to read the markers

Each box that refers to a Lean declaration carries the marker of VersoBlueprint: "complete",
"contains sorry" or "depends on sorry". The text of the box does not say anything about the
status. Where a theorem depends on admitted lemmas, the text after it names them.

The book is not the proof. The proofs are checked by `lake build` of the Lean development.

## Known items

- **Build path in the generated files.** `_out/site/html-multi` holds the absolute path of the
  build directory. Do not publish that folder as it is: use the export script above.
- **Docstrings in popups.** The popup of a card shows the full docstring of the Lean
  declaration, as written in the source, and VersoBlueprint offers no option to hide it. Some
  docstrings of the PQXDH model mark places where the model departs from the specification.
  The section "Modelling choices" of chapter 3 states each departure in mathematical prose.
- **Source links of the book's own code.** The cards labelled "Book example" show
  `LibsignalVerifyBlueprint/ProbTrees.lean`. Their "Source file" links work once
  `source-revision` names a commit that contains this file. Their "defined in" lines link to the
  commit that is checked out when the renderer runs. The export script accepts the book only if
  that commit is the one in `source-revision`, as it is in the publishing workflow.
- **Upstream docstring.** One popup shows a docstring from VCV-io that starts with a note
  about an upstream design choice. It is upstream text and is left as it is.
- **Open statements.** The book describes the code as it stands. Pull request #71 changes the
  matching of sessions in the security theorems, and chapters 2 and 3 say where. The
  correctness and the security of the production handshake are open
  ([#72](https://github.com/Beneficial-AI-Foundation/libsignal-verify/issues/72) and
  [#79](https://github.com/Beneficial-AI-Foundation/libsignal-verify/issues/79)).
