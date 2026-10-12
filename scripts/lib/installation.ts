import fs from "node:fs";
import path from "node:path";
import { createHash } from "node:crypto";
import { createReadStream } from "node:fs";
import { type AeneasConfig, type InstallMode } from "./config.js";
import { assertRealPath, checkInstallationFiles, INSTALL_RECORD, installationAt, installationDir,
  platformKey, type Installation } from "./paths.js";
import { run } from "./shell.js";

export interface RustMetadata { channel: string; components: string[] }

/** Parse the small, pinned upstream toolchain file; no floating-nightly fallback. */
export function rustMetadata(file: string): RustMetadata {
  const text = fs.readFileSync(file, "utf8");
  const section = text.match(/^\[toolchain\]\s*\n([\s\S]*?)(?=^\[|$(?![\s\S]))/m)?.[1];
  const channel = section?.match(/^channel\s*=\s*"(nightly-\d{4}-\d{2}-\d{2})"\s*(?:#.*)?$/m)?.[1];
  const list = section?.match(/^components\s*=\s*\[([^\]]*)\]/m)?.[1];
  const components = list ? [...list.matchAll(/"([a-z0-9-]+)"/g)].map((m) => m[1]) : [];
  if (!channel || !list || components.length === 0 || !components.includes("rustc-dev") ||
      list.replace(/"[a-z0-9-]+"|[\s,]/g, "") !== "") {
    throw new Error(`Missing/invalid pinned driver channel or components: ${file}`);
  }
  return { channel, components };
}

export function driverEnvironment(channel: string): Record<string, string | undefined> {
  return { RUSTUP_TOOLCHAIN: channel, CHARON_TOOLCHAIN_IS_IN_PATH: undefined };
}

export async function setupRust(metadata: RustMetadata): Promise<void> {
  await run("rustup", ["toolchain", "install", metadata.channel, "--profile", "minimal",
    "--component", metadata.components.join(",")]);
  const installed = await run("rustup", ["component", "list", "--toolchain", metadata.channel, "--installed"]);
  for (const component of metadata.components) {
    if (!installed.split("\n").some((line) => line === component || line.startsWith(`${component}-`))) {
      throw new Error(`Required Rust component not installed: ${component}`);
    }
  }
}

export async function sha256(file: string): Promise<string> {
  const hash = createHash("sha256");
  for await (const chunk of createReadStream(file)) hash.update(chunk);
  return hash.digest("hex");
}

export interface InstallRecord {
  schema: 1;
  mode: InstallMode;
  platform: string;
  commit: string;
  charonCommit: string;
  lean: string;
  rust: RustMetadata;
  version: string;
  charonVersion: string;
  driverVersion: string;
  tag?: string;
  asset?: string;
  archiveSha256?: string;
  files: Record<string, string>;
}

export async function validateTools(installation: Installation, config: AeneasConfig): Promise<InstallRecord> {
  checkInstallationFiles(installation);
  const rust = rustMetadata(installation.rustToolchain);
  const lean = fs.readFileSync(path.join(installation.backend, "lean-toolchain"), "utf8").trim();
  const release = config.aeneas.release;
  let charonCommit: string;
  if (installation.mode === "release") {
    if (!release) throw new Error("Missing release pin");
    if (lean !== release.lean || rust.channel !== release.rust_channel) {
      throw new Error(`Bundle backend/Rust metadata mismatch: ${lean}, ${rust.channel}`);
    }
    charonCommit = release.charon_commit;
  } else {
    const commit = (await run("git", ["rev-parse", "HEAD"], { cwd: installation.dir })).trim();
    if (commit !== config.aeneas.commit) throw new Error(`Source revision mismatch: ${commit}`);
    charonCommit = fs.readFileSync(path.join(installation.dir, "charon-pin"), "utf8")
      .split("\n").map((line) => line.trim()).find((line) => /^[a-f0-9]{40}$/.test(line)) ?? "";
    const actual = (await run("git", ["rev-parse", "HEAD"], { cwd: path.join(installation.dir, "charon") })).trim();
    if (!charonCommit || actual !== charonCommit) throw new Error(`Source charon-pin mismatch: ${actual}`);
    for (const dir of [installation.dir, path.join(installation.dir, "charon")]) {
      if ((await run("git", ["status", "--porcelain", "--untracked-files=no"], { cwd: dir })).trim()) {
        throw new Error(`Source installation has tracked modifications: ${dir}`);
      }
    }
  }
  const version = (await run(installation.aeneas, ["-version"])).trim();
  if (installation.mode === "release") {
    if (version !== `aeneas ${release!.tag}`) throw new Error(`Aeneas release mismatch: ${version}`);
  } else if (!version.includes(config.aeneas.commit.slice(0, 7))) {
    throw new Error(`Aeneas source binary revision mismatch: ${version}`);
  }
  const env = driverEnvironment(rust.channel);
  const charonVersion = (await run(installation.charon, ["version"], { env })).trim();
  if (!charonVersion.includes(charonCommit.slice(0, 7))) {
    throw new Error(`Charon companion revision mismatch: ${charonVersion}`);
  }
  const embeddedChannel = (await run(installation.charon, ["toolchain-version"], { env })).trim();
  if (embeddedChannel !== rust.channel) throw new Error(`Charon embedded Rust channel mismatch: ${embeddedChannel}`);
  // The driver expects argv[1] = rustc. rustup supplies its shared-library paths.
  const driverVersion = (await run("rustup", ["run", rust.channel, installation.driver, "rustc", "--version"], { env })).trim();
  const rustVersion = (await run("rustup", ["run", rust.channel, "rustc", "--version"], { env })).trim();
  if (!driverVersion || driverVersion !== rustVersion) throw new Error(`Charon driver/Rust mismatch: ${driverVersion}`);
  return {
    schema: 1, mode: installation.mode, platform: platformKey,
    commit: installation.mode === "release" ? release!.commit : config.aeneas.commit,
    charonCommit, lean, rust, version, charonVersion, driverVersion,
    ...(installation.mode === "release" ? { tag: release!.tag,
      asset: release!.assets[platformKey]?.name, archiveSha256: release!.assets[platformKey]?.sha256 } : {}),
    files: {},
  };
}

/** Hash the complete extracted bundle, including backend/support libraries. */
export async function bundleInventory(dir: string): Promise<Record<string, string>> {
  const files: Record<string, string> = {};
  const pending = [dir];
  while (pending.length) {
    const current = pending.pop()!;
    for (const entry of fs.readdirSync(current, { withFileTypes: true })) {
      const file = path.join(current, entry.name);
      const relative = path.relative(dir, file);
      if (relative === INSTALL_RECORD) continue;
      if (entry.isDirectory()) pending.push(file);
      else if (entry.isFile()) files[relative] = await sha256(file);
      else throw new Error(`Unexpected link/special file in managed bundle: ${file}`);
    }
  }
  return files;
}

export async function recordInstallation(installation: Installation, record: InstallRecord): Promise<void> {
  record.files = installation.mode === "release" ? await bundleInventory(installation.dir) :
    Object.fromEntries(await Promise.all([installation.aeneas, installation.charon, installation.driver,
      installation.rustToolchain, path.join(installation.backend, "lean-toolchain")]
      .map(async (file) => [path.relative(installation.dir, file), await sha256(file)])));
  fs.writeFileSync(path.join(installation.dir, INSTALL_RECORD), JSON.stringify(record, null, 2) + "\n", { flag: "wx" });
}

export async function validateCache(installation: Installation, config: AeneasConfig,
  installRust = false): Promise<InstallRecord> {
  assertRealPath(installation.dir);
  const file = path.join(installation.dir, INSTALL_RECORD);
  assertRealPath(file);
  if (!fs.existsSync(file)) throw new Error(`Refusing developer-owned/unmarked installation: ${installation.dir}`);
  const saved = JSON.parse(fs.readFileSync(file, "utf8")) as InstallRecord;
  const metadata = rustMetadata(installation.rustToolchain);
  // Verify inventory before executing cached binaries or installing Rust components.
  const files = installation.mode === "release" ? await bundleInventory(installation.dir) :
    Object.fromEntries(await Promise.all([installation.aeneas, installation.charon, installation.driver,
      installation.rustToolchain, path.join(installation.backend, "lean-toolchain")]
      .map(async (p) => { assertRealPath(p); return [path.relative(installation.dir, p), await sha256(p)]; })));
  if (!saved.files || Object.keys(saved.files).length !== Object.keys(files).length ||
      Object.entries(files).some(([p, hash]) => saved.files[p] !== hash)) {
    throw new Error(`Incomplete/modified installation: ${installation.dir}; preserved, not replaced`);
  }
  if (saved.schema !== 1 || saved.mode !== installation.mode || saved.platform !== platformKey ||
      saved.commit !== (installation.mode === "release" ? config.aeneas.release?.commit : config.aeneas.commit) ||
      (installation.mode === "release" && (saved.tag !== config.aeneas.release?.tag ||
        saved.archiveSha256 !== config.aeneas.release?.assets[platformKey]?.sha256 ||
        saved.asset !== config.aeneas.release?.assets[platformKey]?.name ||
        saved.charonCommit !== config.aeneas.release?.charon_commit ||
        metadata.channel !== config.aeneas.release?.rust_channel || saved.lean !== config.aeneas.release?.lean))) {
    throw new Error(`Installation record does not match selected pins: ${installation.dir}`);
  }
  if (installRust) await setupRust(metadata);
  const actual = await validateTools(installation, config);
  if (actual.version !== saved.version || actual.charonVersion !== saved.charonVersion ||
      actual.driverVersion !== saved.driverVersion || actual.lean !== saved.lean ||
      JSON.stringify(actual.rust) !== JSON.stringify(saved.rust)) {
    throw new Error(`Installation identity/metadata changed: ${installation.dir}`);
  }
  return actual;
}

export async function resolveInstallation(root: string, config: AeneasConfig): Promise<Installation> {
  const mode = config.aeneas.mode ?? "release";
  const dir = installationDir(root, config, mode);
  if (mode === "release" && config.aeneas.commit !== config.aeneas.release?.commit) {
    throw new Error("Release/project backend pins differ. Align aeneas.commit with aeneas.release.commit and update the Lake/Lean pins before extraction.");
  }
  if (fs.existsSync(dir)) {
    const installation = installationAt(dir, mode);
    await validateCache(installation, config);
    return installation;
  }
  // Read-only use of a legacy developer checkout is allowed only at the selected identity.
  const legacy = path.join(root, ".aeneas", "aeneas");
  if (mode === "source" && fs.existsSync(legacy)) {
    assertRealPath(legacy);
    const installation = installationAt(legacy, mode);
    await validateTools(installation, config);
    return installation;
  }
  throw new Error(`Selected ${mode} installation missing. Run npm run aeneas-install -- --${mode}.`);
}
