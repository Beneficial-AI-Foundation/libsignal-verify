import fs from "node:fs";
import path from "node:path";
import { readAeneasRequirement, type AeneasConfig } from "./config.js";
import { type Installation } from "./paths.js";

/** Check that project pins match the installed executable and backend without editing them. */
export function checkProjectCompatibility(root: string, config: AeneasConfig,
  installation: Installation, allowMismatch = false): void {
  const backendVersion = fs.readFileSync(path.join(installation.backend, "lean-toolchain"), "utf8").trim();
  const projectVersion = fs.readFileSync(path.join(root, "lean-toolchain"), "utf8").trim();
  const expected = installation.mode === "release" ? config.aeneas.release!.commit : config.aeneas.commit;
  const lakeRev = readAeneasRequirement(root).rev;
  const manifest = JSON.parse(fs.readFileSync(path.join(root, "lake-manifest.json"), "utf8")) as {
    packages: { name: string; rev: string; inputRev?: string }[];
  };
  const entry = manifest.packages.find((pkg) => pkg.name === "aeneas");
  const resolved = entry?.rev;
  const selectorMatches = config.aeneas.release
    ? lakeRev === config.aeneas.release.tag
    : lakeRev === expected;
  if (projectVersion === backendVersion && config.aeneas.commit === expected &&
      selectorMatches && entry?.inputRev === lakeRev && resolved === expected) return;
  const message = `Project pins are not compatible with this ${installation.mode} installation.\n` +
    `  Installed backend: ${expected}, ${backendVersion}\n` +
    `  Project: ${config.aeneas.commit}, ${projectVersion}; Lake ${lakeRev} (${resolved})\n` +
    "Review rust/aeneas-config.yml, lakefile.toml, lake-manifest.json and lean-toolchain together. " +
    "No project files were rewritten; do not extract with these mismatched pins.";
  if (allowMismatch) console.warn(`\nWARNING: ${message}`);
  else throw new Error(message);
}
