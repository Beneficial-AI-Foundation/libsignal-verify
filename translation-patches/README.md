# Translation patches

The committed `rust/` tree is upstream libsignal at the commit pinned in `rust/aeneas-config.yml` (`upstream.commit`). Every change made to the Rust source for extraction is one patch in this folder. `npm run aeneas-extract` copies the Cargo workspace to `.aeneas/work/`, applies the patches there and runs Charon in the copy. The production source is never patched.

## One patch per modification

A patch holds one modification: a change to one item (a type, function, trait or impl) together with the edits that keep the crate compiling, such as the uses of a renamed field. A new helper goes in the same patch as its call sites when it is in the same file; a helper in another module is a patch of its own (`protocol-crypto-hkdf_sha256`, `protocol-crypto-hmac_sha256_parts`). When one file gets the same gate on several items for one reason, that is one patch (the `store_api` and `store_traits` patches).

Names follow `<crate>-<module>-<item>[-<detail>].patch`. `<crate>` is `core`, `crypto` or `protocol`; `<module>` is the file under `src/`, with `/` written as `_` (`ratchet_keys` for `ratchet/keys.rs`), or `Cargo` for the manifest.

Each patch starts with a header, then the diff:

| Line | Content |
| --- | --- |
| `Translation patch:` | the item |
| `Change:` | what the patch changes |
| `Why:` | the Charon or Aeneas limitation, with the blocker-catalog id or upstream issue where one exists; "not recorded" when no source gives the reason |
| `Behaviour:` | the effect on the production build |
| `Relies on:` (optional) | patches this one needs to compile |
| `Applies after:` (optional) | earlier patches whose lines are this patch's context |

## Order

Patches apply in file-name order. Most also apply alone to upstream. A patch that does not names the earlier patches it needs in its `Applies after:` line.

## Checks

- `npm run patches-check` (CI job "Check translation patches") fails when `rust/` differs from upstream, a header field is missing, a patch does not apply after exactly the patches its `Applies after:` line names, or the series does not apply in order and revert in reverse order.
- The extraction job ("Check Aeneas Extraction") runs `npm run aeneas-extract` and fails when the generated Lean differs from the committed files.

To add or change a patch, edit the file in `.aeneas/work/` after a run, write the diff with paths `a/rust/…` and `b/rust/…` against the tree the earlier patches produce, add the header, and run both checks. The reasons are also indexed in [`extraction-notes.md`](../extraction-notes.md#source-modifications).
