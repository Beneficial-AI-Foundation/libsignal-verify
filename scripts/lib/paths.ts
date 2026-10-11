import path from "node:path";
import fs from "node:fs";
import { type AeneasConfig, type InstallMode } from "./config.js";

export const INSTALL_RECORD = ".libsignal-install.json";
export const platformKey = `${process.platform}-${process.arch}`;

export function releaseAssetName(platform: string): string {
  const names: Record<string, string> = {
    "darwin-arm64": "aeneas-macos-aarch64.tar.gz",
    "linux-x64": "aeneas-linux-x86_64.tar.gz",
    "linux-arm64": "aeneas-linux-aarch64.tar.gz",
  };
  const name = names[platform];
  if (!name) throw new Error(`No supported executable bundle for ${platform}`);
  return name;
}

export interface Installation {
  mode: InstallMode;
  dir: string;
  aeneas: string;
  charon: string;
  driver: string;
  backend: string;
  rustToolchain: string;
}

/** Check every existing ancestor: installation writes must never follow symlinks. */
export function assertRealPath(file: string): void {
  let current = path.resolve(file);
  while (true) {
    if (fs.existsSync(current) || fs.lstatSync(current, { throwIfNoEntry: false })) {
      if (fs.lstatSync(current).isSymbolicLink()) throw new Error(`Refusing symlinked location: ${current}`);
    }
    const parent = path.dirname(current);
    if (parent === current) break;
    current = parent;
  }
}

export function installationDir(root: string, config: AeneasConfig, mode: InstallMode): string {
  const identity = mode === "release" ? config.aeneas.release?.tag : config.aeneas.commit;
  if (!identity) throw new Error("Release mode requires a pinned release");
  return path.join(root, ".aeneas", mode === "release" ? "releases" : "sources", identity, platformKey);
}

export function installationAt(dir: string, mode: InstallMode): Installation {
  const charonDir = mode === "source" ? path.join(dir, "charon", "bin") : dir;
  const toolchains = mode === "source"
    ? ["charon/charon/rust-toolchain.toml", "charon/charon/rust-toolchain", "charon/rust-toolchain.toml", "charon/rust-toolchain"]
    : ["rust-toolchain"];
  const rustToolchain = toolchains.map((p) => path.join(dir, p)).find((p) => fs.existsSync(p));
  if (!rustToolchain) throw new Error(`Missing driver Rust metadata in ${dir}`);
  return {
    mode, dir,
    aeneas: path.join(dir, mode === "source" ? "bin/aeneas" : "aeneas"),
    charon: path.join(charonDir, "charon"),
    driver: path.join(charonDir, "charon-driver"),
    backend: path.join(dir, "backends", "lean"),
    rustToolchain,
  };
}

/** All companions come from this installation, never from PATH. */
export function checkInstallationFiles(installation: Installation): void {
  for (const file of [installation.aeneas, installation.charon, installation.driver]) {
    assertRealPath(file);
    if (!fs.statSync(file).isFile()) throw new Error(`Not a binary: ${file}`);
    fs.accessSync(file, fs.constants.X_OK);
  }
  for (const file of [installation.rustToolchain, path.join(installation.backend, "lean-toolchain"),
    path.join(installation.backend, "lakefile.lean"), path.join(installation.backend, "lake-manifest.json")]) {
    assertRealPath(file);
    if (!fs.statSync(file).isFile()) throw new Error(`Missing installation metadata: ${file}`);
  }
}
