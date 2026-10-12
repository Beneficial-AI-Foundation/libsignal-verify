import fs from "node:fs";
import path from "node:path";
import { pipeline } from "node:stream/promises";
import { list, type ReadEntry } from "tar";
import { assertRealPath, INSTALL_RECORD } from "./paths.js";

/** Extract a verified bundle into a fresh directory, accepting only files/directories. */
export async function extractArchive(archive: string, destination: string): Promise<void> {
  assertRealPath(destination);
  if (fs.readdirSync(destination).length !== 0) throw new Error("Archive destination must be empty");
  const entries = new Map<string, { directory: boolean; mode: number }>();
  const nameOf = (entry: ReadEntry): string => {
    const raw = entry.path;
    if (raw.startsWith("/") || raw.includes("\\") || /[\x00-\x1f\x7f]/.test(raw) ||
        raw.split("/").includes("..")) throw new Error(`Unsafe archive path: ${JSON.stringify(raw)}`);
    const name = path.posix.normalize(raw).replace(/\/$/, "");
    if (!name || name === "." || name === INSTALL_RECORD || name.startsWith(`${INSTALL_RECORD}/`)) {
      throw new Error(`Invalid/reserved archive path: ${raw}`);
    }
    return name;
  };
  let failure: Error | undefined;
  const fail = (error: unknown) => { failure ??= error instanceof Error ? error : new Error(String(error)); };
  const parse = async (onReadEntry: (entry: ReadEntry) => void, noResume = false) => {
    const parser = list({ strict: true, onReadEntry, noResume });
    // Pinned bundles use ordinary headers. Reject extended metadata rather than
    // validate pathnames after a potentially lossy PAX/GNU metadata decode.
    parser.on("meta", () => fail(new Error("Extended archive metadata is not supported")));
    parser.on("ignoredEntry", (entry: ReadEntry) => {
      fail(new Error(`Unsupported archive entry: ${entry.type} ${entry.path}`));
    });
    await pipeline(fs.createReadStream(archive), parser);
  };
  await parse((entry) => {
    try {
      const name = nameOf(entry);
      const directory = entry.type === "Directory";
      if (!directory && !["File", "OldFile", "ContiguousFile"].includes(entry.type)) {
        throw new Error(`Unsupported archive entry: ${entry.type} ${name}`);
      }
      if (entries.has(name)) throw new Error(`Duplicate archive path: ${name}`);
      entries.set(name, { directory, mode: (directory || ((entry.mode ?? 0) & 0o111) !== 0) ? 0o755 : 0o644 });
    } catch (error) { fail(error); }
  });
  if (failure) throw failure;
  for (const name of entries.keys()) {
    for (let parent = path.posix.dirname(name); parent !== "."; parent = path.posix.dirname(parent)) {
      if (entries.has(parent) && !entries.get(parent)!.directory) {
        throw new Error(`Archive parent is not a directory: ${name}`);
      }
    }
  }
  const writes: Promise<void>[] = [];
  const seen = new Set<string>();
  try {
    await parse((entry) => {
      try {
        const name = nameOf(entry);
        const metadata = entries.get(name);
        const directory = entry.type === "Directory";
        if (!metadata || seen.has(name) || metadata.directory !== directory ||
            (!directory && !["File", "OldFile", "ContiguousFile"].includes(entry.type))) {
          throw new Error(`Archive changed during extraction: ${name}`);
        }
        seen.add(name);
        const target = path.join(destination, name);
        if (directory) {
          fs.mkdirSync(target, { recursive: true, mode: 0o755 });
          entry.resume();
        } else {
          fs.mkdirSync(path.dirname(target), { recursive: true, mode: 0o755 });
          const output = fs.createWriteStream(target, { flags: "wx", mode: metadata.mode });
          writes.push(pipeline(entry, output).then(() => fs.chmodSync(target, metadata.mode)).catch(fail));
        }
      } catch (error) { fail(error); entry.resume(); }
    }, true);
  } catch (error) { fail(error); }
  await Promise.all(writes);
  if (failure) throw failure;
  if (seen.size !== entries.size) throw new Error("Archive entries changed during extraction");
  console.log(`Validated and extracted ${entries.size} archive members`);
}
