/**
 * Extract Core, the AES-CBC provider, the protocol crate and default-feature
 * ratchet-state conversion. The broader crypto profile is a diagnostic outside
 * the Lean source tree.
 */

import fs from "node:fs";
import path from "node:path";
import { createHash } from "node:crypto";
import chalk from "chalk";
import { loadConfig } from "./lib/config.js";
import { driverEnvironment, resolveInstallation, rustMetadata } from "./lib/installation.js";
import { runStreaming } from "./lib/shell.js";
import { applyTweaks, warnUnmatchedTweaks } from "./lib/tweaks.js";
import { checkProjectCompatibility } from "./lib/lean-toolchain.js";
import { assertRealPath, platformKey } from "./lib/paths.js";

type TargetKey = "core" | "crypto-cbc" | "crypto-full" | "protocol" | "ratchet-state";
const TARGETS: Record<TargetKey, {
  configs: string[]; diagnostic?: boolean; requiredBodies?: Record<string, number>;
}> = {
  core: { configs: ["core"] },
  "crypto-cbc": { configs: ["crypto", "cbc"] },
  protocol: {
    configs: ["protocol"],
    requiredBodies: {
      "libsignal_protocol::pqxdh::pqxdh_initiate": 1,
      "libsignal_protocol::pqxdh::pqxdh_accept": 1,
      "libsignal_protocol::triple_ratchet::from_session_state": 2,
      "libsignal_protocol::triple_ratchet::apply_to_session_state": 2,
      "libsignal_protocol::triple_ratchet::encrypt": 1,
      "libsignal_protocol::triple_ratchet::decrypt": 1,
      "libsignal_protocol::protocol::compute_mac": 1,
      "libsignal_protocol::protocol::verify_mac": 1,
      "libsignal_protocol::protocol::verify_mac_with_addresses": 1,
      "libsignal_protocol::double_ratchet::consume_message_key": 1,
      "libsignal_protocol::double_ratchet::take_skipped_key": 1,
      "libsignal_protocol::double_ratchet::find_receiver_chain_index": 1,
    },
  },
  "ratchet-state": {
    configs: ["protocol", "ratchet-state"],
    requiredBodies: {
      "libsignal_protocol::double_ratchet::from_pb": 2,
      "libsignal_protocol::double_ratchet::apply_to_pb": 1,
      "libsignal_protocol::state::session::apply_ratchet_state": 1,
      "libsignal_protocol::state::session::take_pq_ratchet_state": 1,
      "libsignal_protocol::state::session::set_pq_ratchet_state": 1,
    },
  },
  "crypto-full": { configs: ["crypto"], diagnostic: true },
};
const DEFAULT_TARGETS: TargetKey[] = ["core", "crypto-cbc", "protocol", "ratchet-state"];

interface LlbcFunction {
  item_meta: {
    is_local: boolean; started_from: boolean; opacity: string;
    name: { Ident?: [string, number] }[];
  };
  body: string | Record<string, unknown>;
}

async function runExtraction(targetKey: TargetKey): Promise<void> {
  const target = TARGETS[targetKey];
  const configFiles = target.configs.map((key) => `rust/aeneas-config.${key}.yml`);
  console.log(chalk.bold(`\nAeneas Extract — ${targetKey}\n`));
  console.log(chalk.gray(`  Using configs: ${configFiles.join(", ")}`));

  const { config, root } = loadConfig(undefined, configFiles);

  // Resolve one complete installation before touching generated output.
  const installation = await resolveInstallation(root, config);
  checkProjectCompatibility(root, config, installation);
  const charonBin = installation.charon;
  const aeneasBin = installation.aeneas;
  const driverRust = rustMetadata(installation.rustToolchain);

  const runId = new Date().toISOString().replace(/[:.]/g, "-");
  const logsDir = path.join(root, ".logs", targetKey, runId);
  const llbcFile = `${config.crate.name}.llbc`;
  const llbcPath = path.join(logsDir, llbcFile);
  const destDir = path.join(logsDir, "generated");
  const outputDir = config.aeneas_args.subdir
    ? path.join(destDir, config.aeneas_args.subdir)
    : destDir;
  const canonicalDir = config.aeneas_args.subdir
    ? path.join(root, config.aeneas_args.dest, config.aeneas_args.subdir)
    : path.join(root, config.aeneas_args.dest);
  assertRealPath(outputDir);
  if (!target.diagnostic) assertRealPath(canonicalDir);

  // ── Step 1: Charon ──────────────────────────────────────────────────
  console.log(chalk.bold("Step 1: Generating LLBC with Charon..."));

  const charonArgs: string[] = ["cargo"];

  charonArgs.push("--preset=aeneas", "--dest-file", llbcPath);
  if (config.charon.sysroot) charonArgs.push("--sysroot", config.charon.sysroot);
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

  charonArgs.push("--", ...config.charon.cargo_args);
  if (!config.charon.cargo_args.includes("--locked")) charonArgs.push("--locked");

  fs.mkdirSync(logsDir, { recursive: true });
  fs.writeFileSync(path.join(logsDir, "command.json"), JSON.stringify({
    target: targetKey, config, installation, charon: { executable: charonBin, args: charonArgs },
  }, null, 2) + "\n");

  // Profiling is opt-in. The item filter records declaration timings without
  // formatting the much larger nested trait/type spans enabled by full tracing.
  // RUST_LOG overrides the configured filter; CHARON_PROFILE=0 disables it.
  const PROFILE_FILTERS: Record<string, string> = {
    full: "charon_driver=info",
    item: "[translate_fun_decl]=trace,[translate_global]=trace,[translate_type_decl]=trace,[translate_trait_decl]=trace,[translate_trait_impl]=trace,[get_mir_for_def_id_and_level]=trace",
    off: "",
  };
  // Charon locates its sibling driver; clear the Nix PATH-toolchain escape hatch.
  const charonEnv = driverEnvironment(driverRust.channel);
  // Keep driver-built artifacts separate from production and older tool stacks.
  charonEnv.CARGO_TARGET_DIR = process.env.CARGO_TARGET_DIR ??
    path.join(root, ".aeneas", "cargo", config.aeneas.commit, platformKey);
  console.log(chalk.gray(`  Extraction build cache: ${charonEnv.CARGO_TARGET_DIR}`));
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
    console.log(chalk.gray(`  Timing log: ${path.join(logsDir, "charon.log")}`));
  }

  await runStreaming(charonBin, charonArgs, {
    cwd: root,
    label: "charon translating",
    logFile: path.join(logsDir, "charon.log"),
    env: charonEnv,
    // Timing logs can be large; stream to disk instead of buffering in memory
    // (avoids OOM / terminal flooding). Disk has ample room.
    streamToFile: profiling,
  });

  if (!fs.existsSync(llbcPath)) {
    throw new Error(`Failed to generate ${llbcFile}`);
  }
  const llbcBytes = fs.readFileSync(llbcPath);
  const llbc = JSON.parse(llbcBytes.toString("utf8")) as {
    has_errors: boolean; translated: { fun_decls: (LlbcFunction | null)[] };
  };
  if (llbc.has_errors !== false) throw new Error("Charon reported errors in the generated LLBC");
  const rootBodies = llbc.translated.fun_decls
    .filter((declaration): declaration is LlbcFunction =>
      declaration !== null && declaration.item_meta.is_local && declaration.item_meta.started_from)
    .map(({ item_meta, body }) => ({
      name: item_meta.name.flatMap((part) => part.Ident ? [part.Ident[0]] : []).join("::"),
      opacity: item_meta.opacity,
      body: typeof body === "object" && body !== null ? Object.keys(body) : [body],
    }));
  for (const [name, count] of Object.entries(target.requiredBodies ?? {})) {
    const declarations = rootBodies.filter((declaration) => declaration.name === name);
    if (declarations.length !== count || declarations.some((declaration) =>
      declaration.opacity !== "Transparent" || !declaration.body.includes("Structured"))) {
      throw new Error(`Required transparent root mismatch: ${name} (expected ${count} bodies)`);
    }
  }
  console.log(chalk.green(`  LLBC generated: ${llbcPath}\n`));

  // ── Step 2: Aeneas ──────────────────────────────────────────────────
  console.log(chalk.bold("Step 2: Generating Lean files with Aeneas..."));

  const aeneasArgs: string[] = [
    "-backend", "lean",
    ...config.aeneas_args.options.map((o) => `-${o}`),
    "-dest", destDir,
  ];
  if (config.aeneas_args.use_lean_modules !== undefined) {
    aeneasArgs.push("-use-lean-modules", String(config.aeneas_args.use_lean_modules));
  }
  if (config.aeneas_args.subdir) {
    aeneasArgs.push("-subdir", config.aeneas_args.subdir);
  }
  if (config.aeneas_args.namespace) {
    aeneasArgs.push("-namespace", config.aeneas_args.namespace);
  }
  aeneasArgs.push(llbcPath);
  const commandPath = path.join(logsDir, "command.json");
  const command = JSON.parse(fs.readFileSync(commandPath, "utf8")) as Record<string, unknown>;
  command.aeneas = { executable: aeneasBin, args: aeneasArgs };
  fs.writeFileSync(commandPath, JSON.stringify(command, null, 2) + "\n");

  fs.mkdirSync(outputDir, { recursive: true });
  const jsonPath = path.join(destDir, "translation.json");
  if (config.aeneas_args.options.includes("emit-json") && fs.existsSync(jsonPath)) fs.unlinkSync(jsonPath);

  await runStreaming(aeneasBin, aeneasArgs, {
    cwd: root,
    logFile: path.join(logsDir, "aeneas.log"),
  });

  if (config.aeneas_args.options.includes("emit-json")) {
    const manifest = JSON.parse(fs.readFileSync(jsonPath, "utf8")) as { crate: string };
    if (manifest.crate !== config.crate.name) throw new Error(`Translation manifest crate mismatch: ${manifest.crate}`);
    fs.renameSync(jsonPath, path.join(logsDir, "translation.json"));
    console.log(chalk.gray(`  Translation manifest: ${path.join(logsDir, "translation.json")}`));
  }
  console.log(chalk.green(`  Lean files generated in ${outputDir}/\n`));

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

  const sha256 = (bytes: Buffer): string => createHash("sha256").update(bytes).digest("hex");
  const files = fs.readdirSync(outputDir).filter((name) => name.endsWith(".lean"));
  const generated = Object.fromEntries(files.map((name) =>
    [name, sha256(fs.readFileSync(path.join(outputDir, name)))]));
  fs.writeFileSync(path.join(logsDir, "result.json"), JSON.stringify({
    target: targetKey, llbcSha256: sha256(llbcBytes),
    cargoLockSha256: sha256(fs.readFileSync(path.join(root, "Cargo.lock"))),
    diagnostic: !!target.diagnostic, rootBodies, generated,
  }, null, 2) + "\n");
  if (!target.diagnostic) {
    fs.mkdirSync(canonicalDir, { recursive: true });
    for (const name of files) {
      const destination = path.join(canonicalDir, name);
      assertRealPath(destination);
      fs.copyFileSync(path.join(outputDir, name), destination);
    }
  }
  console.log(chalk.green("Done."));
}

async function main(): Promise<void> {
  const aliases: Record<string, TargetKey> = { crypto: "crypto-cbc" };
  const input = process.argv[2];
  const arg = input ? aliases[input] ?? input : undefined;
  if (arg && !Object.hasOwn(TARGETS, arg)) {
    throw new Error(`Unknown target '${arg}'. Expected one of: ${Object.keys(TARGETS).join(", ")}`);
  }
  const targets: TargetKey[] = arg ? [arg as TargetKey] : DEFAULT_TARGETS;
  for (const key of targets) await runExtraction(key);
  if (targets.length > 1) console.log(chalk.green.bold(`\nAll canonical targets extracted (${targets.join(", ")}).`));
}

main().catch((err: Error) => {
  console.error(chalk.red(`\nError: ${err.message}`));
  process.exit(1);
});
