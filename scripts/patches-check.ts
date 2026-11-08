/**
 * Check the committed Rust source and the translation patches.
 *
 * 1. The committed rust/ tree equals upstream libsignal at the pinned commit, apart from
 *    the project's own files (the Lean tree `rust/Libsignal/`, `*.lean` and `*.yml`).
 * 2. Every patch starts with the header fields and changes only files under rust/.
 * 3. Every patch applies to the upstream tree after exactly the patches its
 *    `Applies after:` line names (none for most patches).
 * 4. The whole series applies in file-name order and reverts in reverse order,
 *    giving back the upstream tree.
 *
 * That the patched tree reproduces the committed Lean translation is checked by the
 * extraction job (`npm run aeneas-extract`, then `git diff --exit-code`).
 */

import { execSync } from "node:child_process";
import fs from "node:fs";
import path from "node:path";
import chalk from "chalk";
import { loadConfig } from "./lib/config.js";
import {
  HEADER_FIELDS, appliesAfter, applyPatches, copyWorkspace, gitApply, listPatches,
} from "./lib/patches.js";

/** Project files under rust/ that are not upstream source (matched by base name). */
function isProjectFile(name: string): boolean {
  return name === "Libsignal" || name === "target" || name.endsWith(".lean") || name.endsWith(".yml");
}

/** Relative paths of the files and symlinks under `dir`, without project files. */
function walk(dir: string, rel = ""): string[] {
  const out: string[] = [];
  for (const entry of fs.readdirSync(path.join(dir, rel), { withFileTypes: true })) {
    if (isProjectFile(entry.name)) continue;
    const child = path.join(rel, entry.name);
    if (entry.isDirectory()) out.push(...walk(dir, child));
    else out.push(child);
  }
  return out;
}

function sameEntry(a: string, b: string): boolean {
  const sa = fs.lstatSync(a);
  const sb = fs.lstatSync(b);
  if (sa.isSymbolicLink() || sb.isSymbolicLink()) {
    return sa.isSymbolicLink() && sb.isSymbolicLink() && fs.readlinkSync(a) === fs.readlinkSync(b);
  }
  return fs.readFileSync(a).equals(fs.readFileSync(b));
}

/** Differences between two source trees, as `changed`, `only in <label>` lines. */
function compareTrees(a: string, b: string, labelA: string, labelB: string): string[] {
  const filesA = new Set(walk(a));
  const filesB = new Set(walk(b));
  const problems: string[] = [];
  for (const f of [...filesA].sort()) {
    if (!filesB.has(f)) problems.push(`only in ${labelA}: ${f}`);
    else if (!sameEntry(path.join(a, f), path.join(b, f))) problems.push(`differs: ${f}`);
  }
  for (const f of [...filesB].sort()) if (!filesA.has(f)) problems.push(`only in ${labelB}: ${f}`);
  return problems;
}

/** Upstream rust/ at the pinned commit, fetched shallowly into `tmp`. */
function upstreamTree(tmp: string, repo: string, commit: string, sourceDir: string): string {
  const clone = path.join(tmp, "upstream.git");
  const out = path.join(tmp, "upstream-src");
  fs.rmSync(clone, { recursive: true, force: true });
  fs.rmSync(out, { recursive: true, force: true });
  fs.mkdirSync(out, { recursive: true });
  execSync(`git init --quiet --bare "${clone}"`, { stdio: "pipe" });
  execSync(`git -C "${clone}" fetch --quiet --depth 1 "${repo}" ${commit}`, { stdio: "pipe" });
  execSync(`git -C "${clone}" archive ${commit} ${sourceDir} | tar -x -C "${out}"`, { stdio: "pipe" });
  return path.join(out, sourceDir);
}

function main(): void {
  const { config, root } = loadConfig();
  const sourceDir = config.crate.dir;
  const tmp = path.join(root, ".tmp", "patches-check");
  const patches = listPatches(path.join(root, config.patches_dir));
  const problems: string[] = [];
  console.log(chalk.bold(`Translation patch check (${patches.length} patches)\n`));

  // 1. The committed tree is upstream.
  console.log(`Fetching ${config.upstream.repo} at ${config.upstream.commit.slice(0, 8)}...`);
  const upstream = upstreamTree(tmp, config.upstream.repo, config.upstream.commit, sourceDir);
  const drift = compareTrees(path.join(root, sourceDir), upstream, "the repository", "upstream");
  problems.push(...drift.map((d) => `${sourceDir}/ is not upstream: ${d}`));
  console.log(drift.length === 0 ? chalk.green(`  ${sourceDir}/ matches upstream`) : chalk.red(`  ${drift.length} difference(s)`));

  // 2. Headers and paths.
  const names = patches.map((p) => path.basename(p, ".patch"));
  for (const patch of patches) {
    const text = fs.readFileSync(patch, "utf8");
    const cut = text.indexOf("\ndiff --git ");
    const header = cut < 0 ? text : text.slice(0, cut);
    for (const field of HEADER_FIELDS) {
      if (!header.split("\n").some((line) => line.startsWith(field))) {
        problems.push(`${path.basename(patch)}: header has no "${field}" line`);
      }
    }
    for (const m of text.matchAll(/^(?:---|\+\+\+) [ab]\/(\S+)/gm)) {
      if (!m[1].startsWith(`${sourceDir}/`)) problems.push(`${path.basename(patch)}: changes ${m[1]}, outside ${sourceDir}/`);
    }
  }

  // 3. Each patch applies after exactly the patches it names.
  const base = path.join(tmp, "upstream-workspace");
  copyWorkspace(root, base);
  for (const [i, patch] of patches.entries()) {
    const after = appliesAfter(patch);
    const unknown = after.filter((a) => !names.slice(0, i).includes(a));
    if (unknown.length > 0) {
      problems.push(`${path.basename(patch)}: "Applies after:" names ${unknown.join(", ")}, not an earlier patch`);
      continue;
    }
    let dir = base;
    if (after.length > 0) {
      dir = path.join(tmp, "after");
      copyWorkspace(root, dir);
      applyPatches(dir, after.map((a) => patches[names.indexOf(a)]));
    }
    const result = gitApply(dir, patch, ["--check"]);
    if (!result.ok) {
      const what = after.length > 0 ? `after ${after.join(", ")}` : "alone to upstream";
      problems.push(`${path.basename(patch)}: does not apply ${what}\n${result.message}`);
    }
  }
  console.log(chalk.gray("  checked each patch against its Applies-after list"));

  // 4. The series applies in order and reverts in reverse order.
  const series = path.join(tmp, "series");
  copyWorkspace(root, series);
  try {
    applyPatches(series, patches);
    for (const patch of [...patches].reverse()) {
      const result = gitApply(series, patch, ["-R"]);
      if (!result.ok) throw new Error(`does not revert: ${path.basename(patch)}\n${result.message}`);
    }
    const left = compareTrees(path.join(series, sourceDir), path.join(base, sourceDir), "reverted", "upstream");
    problems.push(...left.map((d) => `series apply and revert changed the tree: ${d}`));
    console.log(chalk.gray("  applied the series in order and reverted it"));
  } catch (err) {
    problems.push(`series: ${(err as Error).message}`);
  }

  fs.rmSync(tmp, { recursive: true, force: true });
  if (problems.length > 0) {
    console.error(chalk.red(`\n${problems.length} problem(s):`));
    for (const p of problems) console.error(`  ${p}`);
    process.exit(1);
  }
  console.log(chalk.green("\nAll checks passed."));
}

try {
  main();
} catch (err) {
  console.error(chalk.red(`\nError: ${(err as Error).message}`));
  process.exit(1);
}
