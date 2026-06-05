import { execa, type Options as ExecaOptions } from "execa";
import ora from "ora";
import fs from "node:fs";
import path from "node:path";

export interface RunOptions {
  cwd?: string;
  env?: Record<string, string>;
  label?: string;
  logFile?: string;
  silent?: boolean;
  /**
   * Stream output straight to `logFile` as it arrives instead of buffering the
   * whole thing in memory and writing once at the end. Use for commands that
   * can produce very large output (e.g. charon with RUST_LOG profiling), where
   * buffering would risk OOM and terminal flooding. Terminal echo is suppressed
   * in this mode; `tail -f` the log to watch progress.
   */
  streamToFile?: boolean;
}

/**
 * Run a command, capture output, optionally log to file.
 * Shows a spinner if `label` is provided.
 */
export async function run(cmd: string, args: string[], opts?: RunOptions): Promise<string> {
  const spinner = opts?.label && !opts?.silent ? ora(opts.label).start() : null;

  const execaOpts: ExecaOptions = {
    cwd: opts?.cwd,
    env: opts?.env ? { ...process.env, ...opts.env } : undefined,
    reject: false,
  };

  try {
    const result = await execa(cmd, args, execaOpts);
    const output = [result.stdout, result.stderr].filter(Boolean).join("\n");

    if (opts?.logFile) {
      const logDir = path.dirname(opts.logFile);
      fs.mkdirSync(logDir, { recursive: true });
      fs.writeFileSync(opts.logFile, output, "utf-8");
    }

    if (result.exitCode !== 0) {
      spinner?.fail();
      const hint = opts?.logFile ? `\nSee log: ${opts.logFile}` : "";
      throw new Error(`Command failed: ${cmd} ${args.join(" ")}\n${result.stderr || result.stdout}${hint}`);
    }

    spinner?.succeed();
    return String(result.stdout ?? "");
  } catch (err) {
    spinner?.fail();
    throw err;
  }
}

/**
 * Run a command, streaming stdout/stderr in real time.
 */
export async function runStreaming(cmd: string, args: string[], opts?: RunOptions): Promise<void> {
  const execaOpts: ExecaOptions = {
    cwd: opts?.cwd,
    env: opts?.env ? { ...process.env, ...opts.env } : undefined,
    reject: false,
    stdout: "pipe",
    stderr: "pipe",
  };

  // Streaming mode: write each chunk straight to the log file (bounded memory),
  // no full terminal echo, no in-memory accumulation. Guards against OOM/terminal
  // flooding for very large output (e.g. RUST_LOG profiling). A live spinner
  // shows progress (items translated · log size · elapsed) so the long charon
  // step doesn't look frozen; full detail stays in the log.
  const streaming = !!(opts?.streamToFile && opts?.logFile);
  let stream: fs.WriteStream | undefined;
  let spinner: ReturnType<typeof ora> | undefined;
  let timer: NodeJS.Timeout | undefined;
  const label = opts?.label;
  const start = Date.now();
  let bytes = 0;
  let items = 0;
  let current = ""; // most recent top-level item span (e.g. "fun_decl#188")
  let currentSince = Date.now();
  // Top-level per-item translation spans (per-type `translate_ty` noise is
  // filtered out by default). Captures the kind + numeric id so the spinner can
  // show which item charon is on — when it stalls, the spinner freezes on that
  // id with a climbing timer, pinpointing the slow item (map id→name post-run).
  const itemRe = /translate_(fun_decl|global|type_decl|trait_decl|trait_impl)\{(?:[a-z_]+)=(\d+)/g;
  const fmtStatus = () => {
    const secs = Math.round((Date.now() - start) / 1000);
    const onCur = current
      ? ` · on ${current} (${Math.round((Date.now() - currentSince) / 1000)}s)`
      : "";
    return `${label ?? cmd}: ${items} items · ${(bytes / 1e6).toFixed(1)} MB · ${secs}s${onCur}`;
  };
  if (streaming) {
    fs.mkdirSync(path.dirname(opts!.logFile!), { recursive: true });
    stream = fs.createWriteStream(opts!.logFile!, { flags: "w" });
    spinner = ora({ text: fmtStatus(), stream: process.stdout }).start();
    timer = setInterval(() => { if (spinner) spinner.text = fmtStatus(); }, 500);
  }

  const child = execa(cmd, args, execaOpts);
  const chunks: string[] = [];

  const onStreamChunk = (text: string) => {
    stream!.write(text);
    bytes += Buffer.byteLength(text);
    const matches = [...text.matchAll(itemRe)];
    if (matches.length > 0) {
      items += matches.length;
      const last = matches[matches.length - 1];
      const next = `${last[0].slice("translate_".length).replace(/\{.*/, "")}#${last[1]}`;
      if (next !== current) { current = next; currentSince = Date.now(); }
    }
  };

  if (child.stdout) {
    child.stdout.on("data", (data: Buffer) => {
      const text = data.toString();
      if (streaming) { onStreamChunk(text); return; }
      chunks.push(text);
      process.stdout.write(text);
    });
  }

  if (child.stderr) {
    child.stderr.on("data", (data: Buffer) => {
      const text = data.toString();
      if (streaming) { onStreamChunk(text); return; }
      chunks.push(text);
      process.stderr.write(text);
    });
  }

  const result = await child;

  if (streaming) {
    if (timer) clearInterval(timer);
    await new Promise<void>((resolve) => stream!.end(resolve));
    if (spinner) {
      if (result.exitCode === 0) spinner.succeed(fmtStatus());
      else spinner.fail(fmtStatus());
    }
  } else if (opts?.logFile) {
    const logDir = path.dirname(opts.logFile);
    fs.mkdirSync(logDir, { recursive: true });
    fs.writeFileSync(opts.logFile, chunks.join(""), "utf-8");
  }

  if (result.exitCode !== 0) {
    const hint = opts?.logFile ? `\nSee log: ${opts.logFile}` : "";
    throw new Error(`Command failed: ${cmd} ${args.join(" ")}${hint}`);
  }
}
