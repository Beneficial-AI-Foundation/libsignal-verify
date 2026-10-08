import fs from "node:fs";
import path from "node:path";
import yaml from "js-yaml";

export interface Substitution {
  find?: string;
  regex?: string;
  replace: string;
  /** Reject generation if this representation mapping does not match. */
  required?: boolean;
}

export type InstallMode = "release" | "source";

export interface ReleasePin {
  tag: string;
  commit: string;
  charon_commit: string;
  lean: string;
  rust_channel: string;
  assets: Record<string, { name: string; sha256: string }>;
}

export interface AeneasConfig {
  aeneas: {
    /** Revision used for source builds and the project's Lean backend. */
    commit: string;
    repo: string;
    mode?: InstallMode;
    release?: ReleasePin;
  };
  upstream: {
    repo: string;
    commit: string;
  };
  charon: {
    sysroot: string;
    extract_opaque_bodies: boolean;
    start_from_pub: boolean;
    cargo_args: string[];
    start_from: string[];
    include: string[];
    exclude: string[];
    opaque: string[];
    /**
     * Detail level of charon's per-item translation timings written to
     * .logs/<target>/charon.log (see aeneas-extract.ts). "full" | "item" | "off".
     */
    profile: string;
  };
  aeneas_args: {
    options: string[];
    use_lean_modules?: boolean;
    /** Lean namespace for a separately translated slice of the same Rust crate. */
    namespace?: string;
    dest: string;
    subdir?: string;
  };
  crate: {
    dir: string;
    name: string;
  };
  tweaks: {
    files: string[];
    substitutions: Substitution[];
  };
}

/**
 * The shared/base config file, relative to the repo root (repo-level `aeneas:` +
 * `upstream:` data); the configs live under `rust/`. Overridable via the
 * AENEAS_CONFIG env var. Per-crate files are merged on top.
 */
function configFileName(): string {
  return process.env.AENEAS_CONFIG ?? "rust/aeneas-config.yml";
}

/** Read and parse a YAML config file into a plain object. */
function readYamlFile(filePath: string): Record<string, unknown> {
  if (!fs.existsSync(filePath)) {
    throw new Error(`Config file not found: ${filePath}`);
  }
  const raw = yaml.load(fs.readFileSync(filePath, "utf-8"));
  if (!raw || typeof raw !== "object") {
    throw new Error(`Config file is empty or invalid: ${filePath}`);
  }
  return raw as Record<string, unknown>;
}

/** Deep-merge plain objects; `overlay` wins. Arrays and scalars are replaced. */
function deepMerge(base: Record<string, unknown>, overlay: Record<string, unknown>): Record<string, unknown> {
  const out: Record<string, unknown> = { ...base };
  for (const [key, val] of Object.entries(overlay)) {
    const prev = out[key];
    if (isPlainObject(prev) && isPlainObject(val)) {
      out[key] = deepMerge(prev, val);
    } else {
      out[key] = val;
    }
  }
  return out;
}

function isPlainObject(v: unknown): v is Record<string, unknown> {
  return typeof v === "object" && v !== null && !Array.isArray(v);
}

/**
 * Walk up from `from` to find the directory containing the config file.
 */
export function findProjectRoot(from?: string, configFile = configFileName()): string {
  let dir = from ?? process.cwd();
  while (true) {
    if (fs.existsSync(path.join(dir, configFile))) {
      return dir;
    }
    const parent = path.dirname(dir);
    if (parent === dir) {
      throw new Error(`Could not find ${configFile} in any parent directory`);
    }
    dir = parent;
  }
}

/**
 * Load and validate aeneas config file.
 */
export function loadConfig(root?: string, configFile?: string | string[]): { config: AeneasConfig; root: string } {
  const baseName = configFileName();
  const projectRoot = root ?? findProjectRoot(undefined, baseName);

  // The shared base file holds repo-level `aeneas:` + `upstream:` + `crate.dir`.
  // A per-crate overlay (e.g. aeneas-config.protocol.yml) is merged on top.
  const base = readYamlFile(path.join(projectRoot, baseName));
  const overlays = typeof configFile === "string" ? [configFile] : configFile ?? [];
  const merged = overlays.reduce((current, file) =>
    deepMerge(current, readYamlFile(path.join(projectRoot, file))), base);
  const config = merged as unknown as AeneasConfig;

  // Validate required fields
  if (!config.aeneas?.commit) throw new Error("Missing required field: aeneas.commit");
  if (!config.aeneas?.repo) throw new Error("Missing required field: aeneas.repo");
  if (!/^[a-f0-9]{40}$/.test(config.aeneas.commit)) {
    throw new Error("aeneas.commit must be a full Git revision");
  }
  config.aeneas.mode = config.aeneas.mode ?? "release";
  if (!["source", "release"].includes(config.aeneas.mode)) {
    throw new Error("aeneas.mode must be release or source");
  }
  const release = config.aeneas.release;
  if (release) {
    if (!/^nightly-[0-9.]+-[a-f0-9]+$/.test(release.tag) ||
        !/^[a-f0-9]{40}$/.test(release.commit) ||
        !/^[a-f0-9]{40}$/.test(release.charon_commit) ||
        !/^leanprover\/lean4:v[0-9.]+$/.test(release.lean) ||
        !/^nightly-\d{4}-\d{2}-\d{2}$/.test(release.rust_channel) ||
        !release.assets || Object.keys(release.assets).length === 0) {
      throw new Error("Incomplete or invalid aeneas.release pins");
    }
    for (const asset of Object.values(release.assets)) {
      if (!/^aeneas-(macos|linux)-(aarch64|x86_64)\.tar\.gz$/.test(asset.name) ||
          !/^[a-f0-9]{64}$/.test(asset.sha256)) {
        throw new Error("Invalid executable release asset or SHA-256");
      }
    }
  }
  if (!config.crate?.dir) throw new Error("Missing required field: crate.dir");

  // Apply defaults
  config.upstream = config.upstream ?? { repo: "", commit: "" };
  config.charon = config.charon ?? {} as AeneasConfig["charon"];
  config.charon.sysroot = config.charon.sysroot ?? "default";
  if (typeof config.charon.sysroot !== "string") throw new Error("charon.sysroot must be a string");
  config.charon.extract_opaque_bodies = config.charon.extract_opaque_bodies ?? false;
  config.charon.start_from_pub = config.charon.start_from_pub ?? false;
  config.charon.cargo_args = config.charon.cargo_args ?? [];
  config.charon.start_from = config.charon.start_from ?? [];
  config.charon.include = config.charon.include ?? [];
  config.charon.exclude = config.charon.exclude ?? [];
  config.charon.opaque = config.charon.opaque ?? [];
  config.charon.profile = config.charon.profile ?? "off";
  config.aeneas_args = config.aeneas_args ?? {} as AeneasConfig["aeneas_args"];
  config.aeneas_args.options = config.aeneas_args.options ?? [];
  if (config.aeneas_args.use_lean_modules !== undefined &&
      typeof config.aeneas_args.use_lean_modules !== "boolean") {
    throw new Error("aeneas_args.use_lean_modules must be a boolean");
  }
  if (config.aeneas_args.namespace !== undefined &&
      (typeof config.aeneas_args.namespace !== "string" ||
       !/^[A-Za-z_][A-Za-z0-9_]*(\.[A-Za-z_][A-Za-z0-9_]*)*$/.test(config.aeneas_args.namespace))) {
    throw new Error("aeneas_args.namespace must be a dotted Lean identifier");
  }
  config.aeneas_args.dest = config.aeneas_args.dest ?? "output";
  config.crate.name = config.crate.name ?? config.crate.dir.replace(/-/g, "_");
  config.tweaks = config.tweaks ?? { files: [], substitutions: [] };
  config.tweaks.files = config.tweaks.files ?? [];
  config.tweaks.substitutions = config.tweaks.substitutions ?? [];

  return { config, root: projectRoot };
}
