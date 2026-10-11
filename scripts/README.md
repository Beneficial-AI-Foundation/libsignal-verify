# Scripts

These scripts install pinned Aeneas and Charon releases and translate libsignal's Rust code into Lean under `rust/Libsignal/Translated/`. The default run extracts `libsignal-core`, the supported `signal-crypto` operations, the `libsignal-protocol` crate, and the Double Ratchet state conversion built with default Cargo features.

## Workflow

```sh
npm ci
npm run aeneas-install    # pinned release bundle for this platform
npm run aeneas-extract    # all four profiles, in order
lake build Libsignal
```

| Command | Effect |
| --- | --- |
| `npm run aeneas-extract` | Runs the `core`, `crypto`, `protocol` and `ratchet-state` profiles |
| `npm run aeneas-extract:<profile>` | Runs one profile |
| `npm run aeneas-extract:crypto-full` | Runs the crypto selection diagnostically; output stays under `.logs/` |
| `npm run aeneas-extract:crypto-cbc` | Runs the narrower CBC diagnostic without replacing canonical crypto output |
| `npm run aeneas-install -- --release` | Installs the configured release bundle; `--archive <path>` supplies a local copy, still checked against the pinned SHA-256 |
| `npm run aeneas-install -- --source` | Builds the pinned Aeneas commit and its Charon pin from source; never used as a fallback |
| `npm run src-diff` | Regenerates `src-modifications.diff` against the pinned upstream libsignal commit; needs GNU diff (`gdiff` on macOS, from Homebrew `diffutils`) |
| `npm run typecheck` | Type-checks the scripts |

## Profiles

| Profile | Configuration | Lean output |
| --- | --- | --- |
| `core` | `aeneas-config.core.yml` | `Libsignal/Translated/Core` |
| `crypto` | `aeneas-config.crypto.yml` | `Libsignal/Translated/Crypto`: AES-GCM encrypt/decrypt/tag control flow, GCM state cloning, MAC update-and-return, and existing primitive interfaces |
| `protocol` | `aeneas-config.protocol.yml` | `Libsignal/Translated/Protocol`: PQXDH, Double and Triple Ratchet, messages, session and prekey state, sender keys, fingerprints |
| `ratchet-state` | `aeneas-config.protocol.yml` + `ratchet-state.yml` | `Libsignal/Translated/RatchetState`: ratchet state ↔ session protobuf fields, default features |

The `crypto` profile retains its existing opaque AES/CTR/GHASH/hash primitive boundaries and excludes HPKE. It translates the surrounding AES-GCM and MAC operations; it is not a verification of the underlying primitives. The narrower `crypto-cbc` profile adds `cbc.yml` for diagnosis only.

The `protocol` profile builds with the crate's `extraction` feature. Every Rust change made for extraction is listed in [`extraction-notes.md`](../extraction-notes.md) and [`src-modifications.diff`](../src-modifications.diff); each profile's YAML lists its opaque and excluded items with the reason.

## Developer reference

### Pins

The Aeneas requirement in `lakefile.toml` selects the GitHub release tag. The installer reads that selection; `lake-manifest.json` records its exact resolved commit. `rust/aeneas-config.yml` retains the expected executable/backend commit, companion Charon commit, Lean version, driver Rust nightly, per-platform SHA-256 and upstream libsignal pin. Executable asset names are derived from the supported platform mapping.

To change releases, update the Lake selection and its validation pins together. Installation reports incompatible pins and extraction rejects them before writing output; neither rewrites them. Explicit local source builds remain available, with the same commit checks and no automatic fallback.

CI installs releases only, re-runs extraction and fails if generated files differ from the committed ones. It does not install opam or an unused stable Rust toolchain; the installer selects the exact driver Rust channel.

### Installation

Release bundles exist for macOS ARM64 and Linux x86-64/ARM64. Release mode uses the existing Node/TypeScript dependencies, `curl` and `rustup`; explicit local source builds need git, opam and make. The installer checks the archive digest and every archive member (no extended metadata payloads, path traversal, links or special files), installs the exact Rust nightly and components, and runs version checks before activating the installation. Never use a floating `latest` URL or a `lean-build-*` proof-cache asset.

Installations live in:

- `.aeneas/releases/<tag>/<platform>/` for releases;
- `.aeneas/sources/<commit>/<platform>/` for managed source builds;
- `.aeneas/aeneas/` for an existing developer checkout, which installation never modifies.

A lock prevents concurrent installs. Each install is staged and then renamed into a fresh versioned directory, so a failed install leaves earlier ones intact. An existing destination is re-verified on reuse and never overwritten.

### Extraction runs

Charon runs as `charon cargo --preset=aeneas --sysroot=default`. Aeneas, Charon and `charon-driver` come from one installation with no `PATH` fallback. Aeneas emits non-module Lean files (`-use-lean-modules false`) to match the maintained external models.

The extractor enables `-emit-json` centrally for every profile. Each run writes its command, LLBC, translation metadata, output hashes and logs to `.logs/<profile>/<timestamp>/`. Generated files are copied into `rust/Libsignal/Translated/` only after Charon reports no errors, the required roots have transparent bodies, Aeneas succeeds and every `required` tweak matches. The hand-maintained `TypesExternal.lean` and `FunsExternal.lean` are never overwritten; Aeneas writes `*_Template.lean` beside them. The Cargo cache is `.aeneas/cargo/<aeneas-commit>/<platform>/` unless `CARGO_TARGET_DIR` is set.

### Configuration

`rust/aeneas-config.yml` is the base; `aeneas-config.{core,crypto,protocol}.yml` are per-crate overlays, and `aeneas-config.{cbc,ratchet-state}.yml` add the narrower profiles' roots and mappings. Lists of excluded and opaque items carry a comment giving the reason. `tweaks` are text substitutions applied to the generated `Types.lean` and `Funs.lean`. A tweak marked `required` must match, so a change in the generated shape stops the run. `aeneas_args.namespace` places a profile under its own Lean namespace. `AENEAS_CONFIG` selects another base file.
