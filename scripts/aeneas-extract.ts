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

// Leaf-first order, used when extracting "all" crates.
const CRATE_KEYS = ["core", "crypto", "protocol"];

async function runExtraction(crateKey: string): Promise<void> {
  const configFile = `rust/aeneas-config.${crateKey}.yml`;
  console.log(chalk.bold(`\nAeneas Extract — ${crateKey}\n`));
  console.log(chalk.gray(`  Using config: ${configFile}`));

  const { config, root } = loadConfig(undefined, configFile);

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
  // Map the configured detail level (charon.profile in aeneas-config.yml) to a
  // RUST_LOG filter for charon's per-item tracing spans:
  //   full → every info span incl. nested trait-proof / per-type / fn-ptr spans.
  //          Large log (100s of MB), but shows *why* an item is slow — e.g. it's
  //          what revealed the Index<RangeFull> trait-proof explosion in
  //          fingerprint::get_fingerprint (see charon-slowdown-notes.md).
  //   item → per-item span durations only (small log) — tells you *which* item is
  //          slow but not the intra-item cause.
  //   off  → no profiling; plain echoed log.
  // NOTE: the default (when no `profile` is configured) is `off` — profiling is
  // opt-in. Set `charon.profile: item|full` in a per-crate config to enable it.
  //
  // `item` ENABLES ONLY the per-item + name spans — crucially with NO
  // `charon_driver=info` catch-all. A catch-all turns every span on and `[span]=off`
  // directives do NOT override it, so the giant `translate_bound_fn_ptr` /
  // `translate_trait_proof` spans (multi-100KB ItemRef Debug dumps) keep firing —
  // that bloats the log to 100MB+ and adds a crippling format penalty (one item,
  // compute_mac, took ~50min and crashed the run). Listing only the spans we read
  // leaves everything else at the default (off): the item openings
  // (translate_*_decl) drive the spinner + slow-item logger, and get_mir carries the
  // readable name. Result: small log, no penalty, full per-item wall-clock timing.
  const PROFILE_FILTERS: Record<string, string> = {
    full: "charon_driver=info",
    item: "[translate_fun_decl]=trace,[translate_global]=trace,[translate_type_decl]=trace,[translate_trait_decl]=trace,[translate_trait_impl]=trace,[get_mir_for_def_id_and_level]=trace",
    off: "",
  };
  const charonEnv: Record<string, string> = {};
  if (process.env.RUST_LOG) {
    charonEnv.RUST_LOG = process.env.RUST_LOG; // explicit env override wins
  } else if (process.env.CHARON_PROFILE === "0") {
    // legacy escape hatch: disable profiling regardless of config
  } else {
    const filter = PROFILE_FILTERS[config.charon.profile] ?? PROFILE_FILTERS.full;
    if (filter) charonEnv.RUST_LOG = filter;
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


  // ── Step 5: Lean toolchain sync ─────────────────────────────────────
  syncLeanToolchain(root);

  console.log(chalk.green("Done."));
}

async function main(): Promise<void> {
  // With a crate arg, extract just that crate; with none, extract all of them.
  const arg = process.argv[2];
  if (arg && !CRATE_KEYS.includes(arg)) {
    throw new Error(`Unknown crate '${arg}'. Expected one of: ${CRATE_KEYS.join(", ")}`);
  }
  const crates = arg ? [arg] : CRATE_KEYS;
  for (const key of crates) {
    await runExtraction(key);
  }
  if (crates.length > 1) console.log(chalk.green.bold(`\nAll crates extracted (${crates.join(", ")}).`));
}

main().catch((err: Error) => {
  console.error(chalk.red(`\nError: ${err.message}`));
  process.exit(1);
});
