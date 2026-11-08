# ts-proof

ts-proof checks TypeScript programs against LAW and PROOF declarations at compile time. A successful check means every required obligation was proved by Z3 for the supported subset, under the assumptions printed as `VERIFY014`.

The flagship check is an Express route, `POST /agents/:id/tokens`, in `examples/iam-token-issuer`. For the modeled request, an unauthorized caller does not attempt KMS signing and does not attempt a token insert. HTTP 201 is reachable only after a committed token row, and that row's principal is the request principal. The ordering check uses a single-request clock: the response stamp is after the insert stamp.

## Run

Z3 must be on `PATH` (or `Z3_PATH`). Rust 1.85 or newer builds the workspace.

```bash
cargo test
cargo build -p ts_proof_cli
node packages/cli/bin.js check examples/iam-token-issuer
node packages/cli/bin.js explain VERIFY001
```

The npm packages are `ts-proof` (the `ts-proof` bin), `@ts-proof/spec`, and `@ts-proof/proof`. They are private in this repo and not published. The bin runs the Rust binary from `target/`, `TS_PROOF_BIN`, or `PATH`.

`check` and `prove` do not emit JavaScript. `build` emits with `tsrs` only after the proofs succeed. Exit `0` is proved, exit `1` is a verification failure, exit `2` is a tool failure.

Example projects set `compilerRequired` to false, so they record a `VERIFY014` bypass and still prove. A project that leaves the compiler required fails with `VERIFY013` when `tsrs` 0.23.0 is absent. The pin is `integration/tsrs/PIN`.

## Layout

The verifier is a Rust workspace. Adapters for Express, PostgreSQL `pg`, Fetch, NestJS controllers, Prisma, and a narrow TypeORM repository shape live under `adapters/`. `packages/cli` is the npm package `ts-proof`. `@ts-proof/spec` and `@ts-proof/proof` are marker packages. Calling them from ordinary JavaScript throws. The proof is the Rust check.

## What a proof covers

The supported language is a semicolon-terminated subset: booleans, mathematical integers (`bigint` and integer literals), string equality, straight-line code, branches, calls, and `while` loops that carry a `// @invariant`. `number`, `/`, bitwise operators, `==`, `eval`, and missing semicolons are `VERIFY002`.

External effects are counters and state ghosts. `trace.<effect>` counts attempts. Database ghosts separate an attempt, a pending row inside `db.tx.active`, and `db.committed.<table>`. `db.last.*` is written only on the success path. Fetch records `http.last_url` for the last completed call, and `http.url.0` through `http.url.3` for the first four. A fifth completed call fails closed.

Only `unsat` is a proof. `sat` is `VERIFY001` with a counterexample of the encoded model. `unknown`, timeout, a solver error, an unmodeled call, and an unsupported framework pattern fail the build. A cache file is trusted only when its bytes are exactly `unsat`. Any other bytes are `VERIFY012`, and that run still fails after recomputing.

Limits, adapter contracts, and the trust boundary are in `docs/SOUNDNESS.md`. The phase status is in `IMPLEMENTATION_PLAN.md`.
