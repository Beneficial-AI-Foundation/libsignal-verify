/** Install a pinned paired release, or explicitly build a source pin in a fresh location. */
import fs from "node:fs";
import path from "node:path";
import chalk from "chalk";
import { loadConfig, type AeneasConfig, type InstallMode } from "./lib/config.js";
import { assertRealPath, installationAt, installationDir, platformKey } from "./lib/paths.js";
import { recordInstallation, rustMetadata, setupRust, sha256, validateCache, validateTools } from "./lib/installation.js";
import { checkProjectCompatibility } from "./lib/lean-toolchain.js";
import { run, runStreaming } from "./lib/shell.js";

// Validate every member before writing any: no absolute/traversing paths, links,
// device files, duplicate files or directory/file collisions. Extract only regular
// files/directories with bounded permissions, not tar's link/ownership semantics.
const EXTRACT_ARCHIVE = String.raw`
import os, pathlib, shutil, sys, tarfile
archive, dest = sys.argv[1:]
with tarfile.open(archive, 'r:gz') as tar:
    members = tar.getmembers()
    entries = {}
    for member in members:
        name = member.name
        if name.startswith('/') or '\\' in name or any(ord(c) < 32 for c in name):
            raise ValueError('Unsafe archive path: ' + repr(name))
        parts = name.split('/')
        if '..' in parts:
            raise ValueError('Traversing archive path: ' + name)
        clean = '/'.join(p for p in parts if p not in ('', '.'))
        if not clean or clean == '.libsignal-install.json':
            raise ValueError('Invalid/reserved archive path: ' + name)
        if not (member.isfile() or member.isdir()):
            raise ValueError('Archive links/special files are not supported: ' + name)
        if clean in entries:
            raise ValueError('Duplicate archive path: ' + name)
        entries[clean] = member
    for name, member in entries.items():
        for parent in pathlib.PurePosixPath(name).parents:
            if str(parent) in entries and not entries[str(parent)].isdir():
                raise ValueError('Archive parent is not a directory: ' + name)
    for name, member in entries.items():
        target = os.path.join(dest, name)
        if member.isdir():
            os.makedirs(target, exist_ok=True)
        else:
            os.makedirs(os.path.dirname(target), exist_ok=True)
            with tar.extractfile(member) as src, open(target, 'xb') as out:
                shutil.copyfileobj(src, out)
            os.chmod(target, 0o755 if member.mode & 0o111 else 0o644)
print('Validated and extracted ' + str(len(entries)) + ' archive members')
`;

function options(defaultMode: InstallMode): { mode: InstallMode; archive?: string } {
  let mode = defaultMode;
  let selected = false;
  let archive: string | undefined;
  const args = process.argv.slice(2);
  for (let i = 0; i < args.length; i++) {
    const arg = args[i];
    if (arg === "--source" || arg === "--release") {
      if (selected) throw new Error("Select exactly one installation mode");
      selected = true;
      mode = arg === "--source" ? "source" : "release";
    } else if (arg === "--archive" && args[i + 1] && !archive) {
      archive = path.resolve(args[++i]);
    } else throw new Error(`Unknown/incomplete option: ${arg}. Use --release, --source, or --archive FILE.`);
  }
  if (archive && mode !== "release") throw new Error("--archive is only supported in release mode");
  return { mode, archive };
}

async function checkDependencies(mode: InstallMode): Promise<void> {
  const deps = mode === "release" ? ["curl", "python3", "rustup"] : ["git", "opam", "make", "rustup"];
  for (const dep of deps) await run("which", [dep]);
}

async function installRelease(root: string, stage: string, config: AeneasConfig, archive?: string): Promise<void> {
  const release = config.aeneas.release;
  const asset = release?.assets[platformKey];
  if (!release || !asset) {
    throw new Error(`No pinned executable bundle for ${platformKey}. Explicit --source is available; no automatic fallback.`);
  }
  const bundle = archive ?? path.join(stage, "bundle.tar.gz");
  if (!archive) {
    const url = `${config.aeneas.repo.replace(/\.git$/, "")}/releases/download/${release.tag}/${asset.name}`;
    console.log(`Downloading ${url}`);
    await run("curl", ["--fail", "--location", "--silent", "--show-error", "--output", bundle, url]);
  }
  const digest = await sha256(bundle);
  if (digest !== asset.sha256) throw new Error(`Bundle SHA-256 mismatch: expected ${asset.sha256}, got ${digest}`);
  console.log(`SHA-256 verified: ${digest}`);
  const extracted = path.join(stage, "installation");
  fs.mkdirSync(extracted);
  await run("python3", ["-c", EXTRACT_ARCHIVE, bundle, extracted]);
  const installation = installationAt(extracted, "release");
  // Fail on metadata mismatches before installing any Rust components.
  const rust = rustMetadata(installation.rustToolchain);
  const lean = fs.readFileSync(path.join(installation.backend, "lean-toolchain"), "utf8").trim();
  if (rust.channel !== release.rust_channel || lean !== release.lean) throw new Error("Bundle Rust/Lean metadata mismatch");
  await setupRust(rust);
  const record = await validateTools(installation, config);
  await recordInstallation(installation, record);
  checkProjectCompatibility(root, config, installation, true);
}

async function checkout(repo: string, dir: string, commit: string): Promise<void> {
  // Only called on new staging locations, never a legacy/developer checkout.
  await run("git", ["init", dir]);
  await run("git", ["remote", "add", "origin", repo], { cwd: dir });
  await run("git", ["fetch", "--depth", "1", "origin", commit], { cwd: dir });
  await run("git", ["checkout", "--detach", "FETCH_HEAD"], { cwd: dir });
}

async function installSource(root: string, stage: string, config: AeneasConfig): Promise<void> {
  const dir = path.join(stage, "installation");
  await checkout(config.aeneas.repo, dir, config.aeneas.commit);
  const charonCommit = fs.readFileSync(path.join(dir, "charon-pin"), "utf8").split("\n")
    .map((line) => line.trim()).find((line) => /^[a-f0-9]{40}$/.test(line));
  if (!charonCommit) throw new Error("Source has no exact charon-pin");
  await checkout("https://github.com/AeneasVerif/charon.git", path.join(dir, "charon"), charonCommit);
  const installation = installationAt(dir, "source");
  const rust = rustMetadata(installation.rustToolchain);
  await setupRust(rust);
  // Use a dedicated switch; preserve developer switches and the global selection.
  const switchName = `libsignal-aeneas-${config.aeneas.commit}-${platformKey}`;
  const switches = await run("opam", ["switch", "list", "--short"]);
  if (!switches.split("\n").some((line) => line.trim() === switchName)) {
    await runStreaming("opam", ["switch", "create", switchName, "ocaml-base-compiler.5.2.0", "--no-switch"]);
  }
  const opamEnv = await run("opam", ["env", `--switch=${switchName}`, "--set-switch"]);
  const env: Record<string, string> = { RUSTUP_TOOLCHAIN: rust.channel };
  for (const line of opamEnv.split("\n")) {
    const match = line.match(/^(\w+)='([^']*)'; export \1;/);
    if (match) env[match[1]] = match[2];
  }
  await runStreaming("opam", ["install", `--switch=${switchName}`, "-y", "dune", "ppx_deriving",
    "visitors", "easy_logging", "zarith", "yojson", "core_unix", "odoc", "ocamlgraph", "menhir",
    "ocamlformat", "unionFind", "domainslib", "progress"], { cwd: dir, env });
  const charonDir = path.join(dir, "charon");
  await runStreaming("rustup", ["run", rust.channel, "cargo", "build", "--release", "--locked"], {
    cwd: path.join(charonDir, "charon"), env,
  });
  fs.mkdirSync(path.join(charonDir, "bin"));
  for (const name of ["charon", "charon-driver"]) {
    fs.copyFileSync(path.join(charonDir, "charon", "target", "release", name), path.join(charonDir, "bin", name));
  }
  await runStreaming("make", ["build-charon-ml"], { cwd: charonDir, env });
  await runStreaming("opam", ["exec", `--switch=${switchName}`, "--", "dune", "build", "main.exe"], {
    cwd: path.join(dir, "src"), env,
  });
  fs.mkdirSync(path.join(dir, "bin"));
  fs.copyFileSync(path.join(dir, "src", "_build", "default", "main.exe"), installation.aeneas);
  const record = await validateTools(installation, config);
  await recordInstallation(installation, record);
  checkProjectCompatibility(root, config, installation, true);
}

async function main(): Promise<void> {
  const { config, root } = loadConfig();
  const { mode, archive } = options(config.aeneas.mode ?? "release");
  const dir = installationDir(root, config, mode);
  const base = path.join(root, ".aeneas");
  assertRealPath(dir);
  fs.mkdirSync(base, { recursive: true });
  // A per-checkout lock also protects the absent-destination activation check.
  const lock = path.join(base, ".libsignal-install.lock");
  const fd = fs.openSync(lock, "wx");
  let stage: string | undefined;
  try {
    await checkDependencies(mode);
    if (fs.existsSync(dir)) {
      const installation = installationAt(dir, mode);
      await validateCache(installation, config, true);
      checkProjectCompatibility(root, config, installation, true);
      console.log(chalk.green(`Verified complete ${mode} cache: ${dir}`));
      return;
    }
    const managed = path.join(base, mode === "release" ? "releases" : "sources");
    const marker = path.join(managed, ".libsignal-managed");
    assertRealPath(marker);
    if (fs.existsSync(managed)) {
      if (!fs.existsSync(marker) || fs.readFileSync(marker, "utf8") !== "libsignal-verify installer v1\n") {
        throw new Error(`Refusing developer-owned managed location: ${managed}`);
      }
    } else {
      fs.mkdirSync(managed);
      fs.writeFileSync(marker, "libsignal-verify installer v1\n", { flag: "wx" });
    }
    stage = fs.mkdtempSync(path.join(managed, ".staging-"));
    if (mode === "release") await installRelease(root, stage, config, archive);
    else await installSource(root, stage, config);
    assertRealPath(dir);
    if (fs.existsSync(dir)) throw new Error(`Activation destination appeared; preserved: ${dir}`);
    fs.mkdirSync(path.dirname(dir), { recursive: true });
    // No active pointer is replaced: the configured pin selects an immutable,
    // version-addressed installation. A failed stage leaves all older pins intact.
    fs.renameSync(path.join(stage, "installation"), dir);
    console.log(chalk.green(`\nVerified ${mode} installation activated: ${dir}`));
    console.log("Aeneas, Charon and charon-driver are paired. Existing installations and project pins preserved.");
  } finally {
    if (stage) fs.rmSync(stage, { recursive: true, force: true });
    fs.closeSync(fd);
    fs.unlinkSync(lock);
  }
}

main().catch((err: Error) => {
  console.error(chalk.red(`\nError: ${err.message}`));
  process.exitCode = 1;
});
