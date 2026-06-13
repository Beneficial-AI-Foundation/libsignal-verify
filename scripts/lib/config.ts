import fs from "node:fs";
import path from "node:path";
import yaml from "js-yaml";

export interface Substitution {
  find?: string;
  regex?: string;
  replace: string;
}

export interface AeneasConfig {
  aeneas: {
    commit: string;
    repo: string;
  };
  upstream: {
    repo: string;
    commit: string;
  };
  charon: {
    extract_opaque_bodies: boolean;
    start_from_pub: boolean;
    cargo_args: string[];
    start_from: string[];
    include: string[];
    exclude: string[];
    opaque: string[];
    /**
     * Detail level of charon's per-item translation timings written to
     * .logs/charon.log (see aeneas-extract.ts). "full" | "item" | "off".
     */
    profile: string;
  };
  aeneas_args: {
    options: string[];
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
 * The shared/base config file name (repo-level `aeneas:` + `upstream:` data),
 * overridable via the AENEAS_CONFIG env var. Per-crate files are merged on top.
 */
function configFileName(): string {
  return process.env.AENEAS_CONFIG ?? "aeneas-config.yml";
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
export function loadConfig(root?: string, configFile?: string): { config: AeneasConfig; root: string } {
  const baseName = configFileName();
  const projectRoot = root ?? findProjectRoot(undefined, baseName);

  // The shared base file holds repo-level `aeneas:` + `upstream:` + `crate.dir`.
  // A per-crate overlay (e.g. aeneas-config.protocol.yml) is merged on top.
  const base = readYamlFile(path.join(projectRoot, baseName));
  const overlay = configFile ? readYamlFile(path.join(projectRoot, configFile)) : {};
  const config = deepMerge(base, overlay) as unknown as AeneasConfig;

  // Validate required fields
  if (!config.aeneas?.commit) throw new Error("Missing required field: aeneas.commit");
  if (!config.aeneas?.repo) throw new Error("Missing required field: aeneas.repo");
  if (!config.crate?.dir) throw new Error("Missing required field: crate.dir");

  // Apply defaults
  config.upstream = config.upstream ?? { repo: "", commit: "" };
  config.charon = config.charon ?? {} as AeneasConfig["charon"];
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
  config.aeneas_args.dest = config.aeneas_args.dest ?? "output";
  config.crate.name = config.crate.name ?? config.crate.dir.replace(/-/g, "_");
  config.tweaks = config.tweaks ?? { files: [], substitutions: [] };
  config.tweaks.files = config.tweaks.files ?? [];
  config.tweaks.substitutions = config.tweaks.substitutions ?? [];

  return { config, root: projectRoot };
}
