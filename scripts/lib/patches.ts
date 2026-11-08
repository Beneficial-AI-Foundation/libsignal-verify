/**
 * Translation patches: the source changes made for extraction, kept as one patch per
 * modified item in `translation-patches/` and applied only to a work copy. The committed
 * `rust/` tree stays pristine upstream libsignal.
 *
 * Patches apply in file-name order. Most also apply alone to upstream; a patch whose
 * context lines come from earlier patches names them in an `Applies after:` header line.
 */

import { execFileSync } from "node:child_process";
import { createHash } from "node:crypto";
import fs from "node:fs";
import path from "node:path";
import { assertRealPath } from "./paths.js";

/** Workspace files and folders the extraction build reads, relative to the repo root. */
const WORKSPACE_FILES = ["Cargo.toml", "Cargo.lock", "rust-toolchain"];
const WORKSPACE_DIRS = ["rust"];
/** Project artifacts under `rust/` that are not upstream source and need not be copied. */
const SKIPPED = new Set(["rust/Libsignal", "rust/target"]);

/** The patch files in `dir`, in application (file-name) order. */
export function listPatches(dir: string): string[] {
  if (!fs.existsSync(dir)) return [];
  return fs.readdirSync(dir)
    .filter((name) => name.endsWith(".patch"))
    .sort()
    .map((name) => path.join(dir, name));
}

/** The header fields every patch carries before its diff. */
export const HEADER_FIELDS = ["Translation patch:", "Change:", "Why:", "Behaviour:"];

/** Names (without `.patch`) listed in a patch's `Applies after:` header line. */
export function appliesAfter(patch: string): string[] {
  const text = fs.readFileSync(patch, "utf8");
  const header = text.slice(0, text.indexOf("\ndiff --git "));
  const line = header.split("\n").find((l) => l.startsWith("Applies after:"));
  if (!line) return [];
  return [...line.matchAll(/([\w.-]+)\.patch/g)].map((m) => m[1]);
}

export function sha256File(file: string): string {
  return createHash("sha256").update(fs.readFileSync(file)).digest("hex");
}

/**
 * Copy the Cargo workspace (root manifests and `rust/`, without the Lean files) to `dest`,
 * replacing an earlier copy of those entries. Other entries in `dest`, such as a build
 * cache, are kept. Timestamps are kept so that Cargo reuses its build cache.
 */
export function copyWorkspace(root: string, dest: string): void {
  assertRealPath(dest);
  fs.mkdirSync(dest, { recursive: true });
  for (const entry of [...WORKSPACE_FILES, ...WORKSPACE_DIRS]) {
    fs.rmSync(path.join(dest, entry), { recursive: true, force: true });
  }
  for (const file of WORKSPACE_FILES) {
    fs.cpSync(path.join(root, file), path.join(dest, file), { preserveTimestamps: true });
  }
  for (const dir of WORKSPACE_DIRS) {
    fs.cpSync(path.join(root, dir), path.join(dest, dir), {
      recursive: true,
      preserveTimestamps: true,
      verbatimSymlinks: true,
      filter: (src) => !SKIPPED.has(path.relative(root, src).split(path.sep).join("/")),
    });
  }
}

/**
 * Run `git apply` on `patch` inside `dir`. `GIT_CEILING_DIRECTORIES` stops git from finding
 * the enclosing repository, so the paths in the patch resolve against `dir`.
 */
export function gitApply(dir: string, patch: string, flags: string[] = []): { ok: boolean; message: string } {
  try {
    execFileSync("git", ["apply", ...flags, patch], {
      cwd: dir,
      env: { ...process.env, GIT_CEILING_DIRECTORIES: path.dirname(path.resolve(dir)) },
      stdio: "pipe",
    });
    return { ok: true, message: "" };
  } catch (error) {
    const err = error as { stderr?: Buffer };
    return { ok: false, message: err.stderr?.toString() ?? String(error) };
  }
}

/** Apply `patches` to `dir` in order; stop at the first failure and name the patch. */
export function applyPatches(dir: string, patches: string[]): void {
  for (const patch of patches) {
    const result = gitApply(dir, patch);
    if (!result.ok) {
      throw new Error(`Translation patch does not apply: ${path.basename(patch)}\n${result.message}`);
    }
  }
}

/** A patched work copy of the workspace for extraction. Returns the patches applied. */
export function prepareWorkCopy(root: string, patchesDir: string, dest: string): { name: string; sha256: string }[] {
  const patches = listPatches(patchesDir);
  copyWorkspace(root, dest);
  applyPatches(dest, patches);
  return patches.map((patch) => ({ name: path.basename(patch), sha256: sha256File(patch) }));
}
