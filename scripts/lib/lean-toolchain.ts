import fs from "node:fs";
import path from "node:path";
import { type AeneasConfig } from "./config.js";
import { type Installation } from "./paths.js";

/** Check that project pins match the installed executable and backend without editing them. */
export function checkProjectCompatibility(root: string, config: AeneasConfig,
  installation: Installation, allowMismatch = false): void {
  const backendVersion = fs.readFileSync(path.join(installation.backend, "lean-toolchain"), "utf8").trim();
  const projectVersion = fs.readFileSync(path.join(root, "lean-toolchain"), "utf8").trim();
  const expected = installation.mode === "release" ? config.aeneas.release!.commit : config.aeneas.commit;
  const requirements = fs.readFileSync(path.join(root, "lakefile.toml"), "utf8").split("[[require]]");
  const requirement = requirements.find((block) => /^name\s*=\s*"aeneas"/m.test(block));
  const lakeRev = requirement?.match(/^rev\s*=\s*"([a-f0-9]+)"/m)?.[1];
  const manifest = JSON.parse(fs.readFileSync(path.join(root, "lake-manifest.json"), "utf8")) as {
    packages: { name: string; rev: string }[];
  };
  const resolved = manifest.packages.find((pkg) => pkg.name === "aeneas")?.rev;
  if (projectVersion === backendVersion && config.aeneas.commit === expected &&
      lakeRev && expected.startsWith(lakeRev) && resolved === expected) return;
  const message = `Project pins are not compatible with this ${installation.mode} installation.\n` +
    `  Installed backend: ${expected}, ${backendVersion}\n` +
    `  Project: ${config.aeneas.commit}, ${projectVersion}; Lake ${lakeRev} (${resolved})\n` +
    "Review rust/aeneas-config.yml, lakefile.toml, lake-manifest.json and lean-toolchain together. " +
    "No project files were rewritten; do not extract with these mismatched pins.";
  if (allowMismatch) console.warn(`\nWARNING: ${message}`);
  else throw new Error(message);
}
