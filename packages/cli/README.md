# ts-proof

npm package `ts-proof`. The `ts-proof` bin runs the Rust prover in `crates/ts_proof_cli`. It is not published yet (`"private": true`).

Marker imports live in `@ts-proof/spec` and `@ts-proof/proof`. Calling those functions throws. The proof is this binary.

```bash
cargo build -p ts_proof_cli
node packages/cli/bin.js check [path]
node packages/cli/bin.js prove [path]
node packages/cli/bin.js build [path]
node packages/cli/bin.js coverage [path]
node packages/cli/bin.js explain VERIFY001
```

`TS_PROOF_BIN` selects a binary. Otherwise the bin uses the newer of `target/release/ts-proof` and `target/debug/ts-proof`, then `ts-proof` on `PATH`.

`check` and `prove` verify and do not emit JavaScript. `build` emits with the pinned `tsrs` CLI only after every required obligation is proved. `coverage` prints the same report.

`--format` accepts `text`, `json`, `sarif`, or `junit`.

Exit codes: `0` when every required obligation is proved, `1` when verification fails, `2` when the tool itself cannot run.
