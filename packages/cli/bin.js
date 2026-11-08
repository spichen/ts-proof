#!/usr/bin/env node
import { spawnSync } from "node:child_process";
import { existsSync, statSync } from "node:fs";
import { dirname, join } from "node:path";
import { fileURLToPath } from "node:url";

const here = dirname(fileURLToPath(import.meta.url));
const args = process.argv.slice(2);
const suffix = process.platform === "win32" ? ".exe" : "";
const repoRoot = join(here, "../..");

function mtime(path) {
  try {
    return statSync(path).mtimeMs;
  } catch {
    return -1;
  }
}

function fail(message) {
  console.error(message);
  process.exit(2);
}

function run(command, commandArgs) {
  const result = spawnSync(command, commandArgs, { stdio: "inherit" });
  if (result.error) {
    if (result.error.code === "ENOENT") return false;
    fail(result.error.message);
  }
  process.exit(result.status === null ? 2 : result.status);
}

const explicit = process.env.TS_PROOF_BIN;
if (explicit) {
  if (!existsSync(explicit)) {
    fail(`ts-proof: TS_PROOF_BIN does not exist: ${explicit}`);
  }
  run(explicit, args);
}

const built = [
  join(repoRoot, "target/release", `ts-proof${suffix}`),
  join(repoRoot, "target/debug", `ts-proof${suffix}`),
].filter((path) => existsSync(path));
built.sort((a, b) => mtime(b) - mtime(a));

for (const command of built) {
  run(command, args);
}

if (run("ts-proof", args) === false) {
  fail(
    "ts-proof: the verifier binary is not built and was not found on PATH.\n" +
      "From this repo, run `cargo build -p ts_proof_cli`, or set TS_PROOF_BIN.",
  );
}
