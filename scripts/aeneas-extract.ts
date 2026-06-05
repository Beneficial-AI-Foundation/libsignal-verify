/**
 * Run the full extraction pipeline: Charon -> Aeneas -> Tweaks.
 *
 * All charon options come from aeneas-config.yml and are passed as CLI args.
 */

import fs from "node:fs";
import path from "node:path";
import chalk from "chalk";
import { loadConfig } from "./lib/config.js";
import { findBinary } from "./lib/paths.js";
import { runStreaming } from "./lib/shell.js";
import { applyTweaks, warnUnmatchedTweaks } from "./lib/tweaks.js";
import { syncLeanToolchain } from "./lib/lean-toolchain.js";

async function main(): Promise<void> {
  console.log(chalk.bold("\nAeneas Extract\n"));

  const { config, root } = loadConfig();

  // Resolve binaries
  const charonBin = findBinary("charon", root);
  const aeneasBin = findBinary("aeneas", root);

  if (!charonBin) {
    throw new Error("Charon binary not found. Run 'npm run aeneas-install' first.");
  }
  if (!aeneasBin) {
    throw new Error("Aeneas binary not found. Run 'npm run aeneas-install' first.");
  }

  const llbcFile = `${config.crate.name}.llbc`;
  const llbcPath = path.join(root, llbcFile);
  const destDir = path.join(root, config.aeneas_args.dest);
  const outputDir = config.aeneas_args.subdir
    ? path.join(destDir, config.aeneas_args.subdir)
    : destDir;
  const logsDir = path.join(root, ".logs");

  // ── Step 1: Charon ──────────────────────────────────────────────────
  console.log(chalk.bold("Step 1: Generating LLBC with Charon..."));

  const charonArgs: string[] = ["cargo"];

  charonArgs.push("--preset=aeneas");
  if (config.charon.extract_opaque_bodies) {
    charonArgs.push("--extract-opaque-bodies");
  }
  if (config.charon.start_from_pub) {
    charonArgs.push("--start-from-pub");
  }
  for (const item of config.charon.start_from) {
    charonArgs.push("--start-from", item);
  }
  for (const item of config.charon.include) {
    charonArgs.push("--include", item);
  }
  for (const item of config.charon.exclude) {
    charonArgs.push("--exclude", item);
  }
  for (const item of config.charon.opaque) {
    charonArgs.push("--opaque", item);
  }

  // Cargo args go after --
  if (config.charon.cargo_args.length > 0) {
    charonArgs.push("--", ...config.charon.cargo_args);
  }

  // Remove stale LLBC
  if (fs.existsSync(llbcPath)) {
    fs.unlinkSync(llbcPath);
  }

  fs.mkdirSync(logsDir, { recursive: true });

  // Per-item charon timings are captured by DEFAULT (we often want this data
  // after the fact). charon translates one item at a time, each wrapped in a
  // `#[tracing::instrument]` span, and its logger is a HierarchicalLayer with an
  // uptime timer (RUST_LOG-controlled). So setting RUST_LOG makes charon write
  // timestamped, nested, per-item translation spans to charon.log; slow items
  // show up as large span durations (`translate_fun_decl{…}: <N>ms`).
  //
  //   default                      → per-item info, with the noisy per-type
  //                                  `translate_ty` spans silenced (keeps volume sane)
  //   `RUST_LOG=… npm run …`       → override the filter (e.g. charon_driver=trace)
  //   `CHARON_PROFILE=0 npm run …` → disable; revert to a plain echoed log
  const charonEnv: Record<string, string> = {};
  if (process.env.RUST_LOG) {
    charonEnv.RUST_LOG = process.env.RUST_LOG; // explicit override wins
  } else if (process.env.CHARON_PROFILE !== "0") {
    // Per-item spans (translate_fun_decl/global/type_decl/...) keep their full
    // durations; silence per-type `translate_ty` (thousands of nested 0ms spans
    // per item) so the log stays ~per-item sized rather than GBs.
    charonEnv.RUST_LOG = "charon_driver=info,charon_driver::translate::translate_types=warn";
  }
  const profiling = !!charonEnv.RUST_LOG;
  if (profiling) {
    console.log(chalk.gray(`  Capturing per-item timings to charon.log (RUST_LOG=${charonEnv.RUST_LOG}; CHARON_PROFILE=0 to disable)`));
    console.log(chalk.gray(`  Slow items: grep -oE 'translate_[a-z_]+\\{[^}]*\\}|:\\s+[0-9]+ms' .logs/charon.log | paste - - | sort -t: -k2 -n | tail -30`));
  }

  await runStreaming(charonBin, charonArgs, {
    cwd: root,
    label: "charon translating",
    logFile: path.join(logsDir, "charon.log"),
    env: profiling ? charonEnv : undefined,
    // Timing logs can be large; stream to disk instead of buffering in memory
    // (avoids OOM / terminal flooding). Disk has ample room.
    streamToFile: profiling,
  });

  if (!fs.existsSync(llbcPath)) {
    throw new Error(`Failed to generate ${llbcFile}`);
  }
  console.log(chalk.green(`  LLBC generated: ${llbcFile}\n`));

  // ── Step 2: Aeneas ──────────────────────────────────────────────────
  console.log(chalk.bold("Step 2: Generating Lean files with Aeneas..."));

  const aeneasArgs: string[] = [
    "-backend", "lean",
    ...config.aeneas_args.options.map((o) => `-${o}`),
    "-dest", destDir,
  ];
  if (config.aeneas_args.subdir) {
    aeneasArgs.push("-subdir", config.aeneas_args.subdir);
  }
  aeneasArgs.push(llbcFile);

  fs.mkdirSync(outputDir, { recursive: true });

  await runStreaming(aeneasBin, aeneasArgs, {
    cwd: root,
    logFile: path.join(logsDir, "aeneas.log"),
  });

  console.log(chalk.green(`  Lean files generated in ${config.aeneas_args.dest}/\n`));

  // ── Step 3: Tweaks ──────────────────────────────────────────────────
  // Applied only to the auto-generated files (Types/Funs/*_Template) listed in
  // config.tweaks.files — never the hand-maintained TypesExternal/FunsExternal.
  if (config.tweaks.substitutions.length > 0 && config.tweaks.files.length > 0) {
    console.log(chalk.bold("Step 3: Applying tweaks..."));

    const matchedPerFile: Set<number>[] = [];
    for (const file of config.tweaks.files) {
      const filePath = path.join(outputDir, file);
      if (!fs.existsSync(filePath)) {
        console.log(chalk.yellow(`  Warning: File not found, skipping: ${file}`));
        continue;
      }
      const matched = applyTweaks(filePath, config.tweaks.substitutions);
      matchedPerFile.push(matched);
      console.log(chalk.green(`  Tweaks applied to ${file} (${matched.size} substitutions matched)`));
    }
    warnUnmatchedTweaks(config.tweaks.substitutions, matchedPerFile);
    console.log();
  }

  // ── Step 4: Realize external templates ─────────────────────────────
  // TEMPORARY (remove before committing): copies the (already-tweaked) axiom
  // stubs `*External_Template.lean` → their non-template names. Right now every
  // external item is an opaque axiom with no hand-written realization, so this
  // is a convenience. Once others fill in real realizations, TypesExternal.lean /
  // FunsExternal.lean become hand-maintained and this copy MUST be removed so it
  // doesn't overwrite their edits.
  //
  // This replaces the former TypesPre/TypesPreBase/FunsPre layer-splitting hack,
  // which worked around an Aeneas Types↔TypesExternal circular-dependency
  // limitation that is now fixed upstream (the `*_Template.lean` are self-contained).
  for (const base of ["TypesExternal", "FunsExternal"]) {
    const tmpl = path.join(outputDir, `${base}_Template.lean`);
    const dest = path.join(outputDir, `${base}.lean`);
    if (fs.existsSync(tmpl)) {
      fs.copyFileSync(tmpl, dest);
      console.log(chalk.green(`  Realized ${base}.lean from ${base}_Template.lean`));
    }
  }
  console.log();

  // ── Step 5: Lean toolchain sync ─────────────────────────────────────
  syncLeanToolchain(root);

  console.log(chalk.green("Done."));
}

main().catch((err) => {
  console.error(chalk.red(`\nError: ${err.message}`));
  process.exit(1);
});
