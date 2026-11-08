# Implementation status

This file records what the tree implements relative to the November 2026 plan. Estimates in the original plan are not schedules.

## In this revision

The Rust workspace builds a fail-closed pipeline:

1. Parse the supported TypeScript subset into an owned AST.
2. Discover Express and Nest routes and lower `pg`, Prisma, TypeORM, and Fetch calls.
3. Build a typed VIR, including effect ghosts and middleware `next()` as an inlined continuation.
4. Generate verification conditions. Branch joins are SSA equalities so the query stays linear in the program.
5. Ask Z3. Keep the result only when it is `unsat`.
6. Map `sat` to a source-linked counterexample (`VERIFY001`).
7. Refuse unsupported syntax, unmodeled calls, unknown solver results, timeouts, and bad cache entries.

`ts-proof check`, `prove`, `build`, `coverage`, and `explain` are implemented. Reports render as text, JSON, SARIF, and JUnit. `build` calls `tsrs -p <dir>` only after `ok()`. `check` typechecks with `tsrs -p <dir> --noEmit` when `compilerRequired` is true.

LAW and PROOF declarations bind to functions and endpoints. Lemmas are discharged in order and are not assumed into the implementation proof.

The example projects under `examples/` are checked by `cargo test`. `examples/iam-token-issuer` is the cross-adapter token endpoint. `compilerRequired` is false there so the proof does not depend on a `tsrs` binary. The report still contains the `VERIFY014` bypass.

## Phase status

| Phase | Status |
|---|---|
| 0 Foundation | Workspace, Z3, span-carrying diagnostics, `tsrs` CLI pin |
| 1 Pure functions | Integer and boolean VIR, contracts, counterexamples |
| 2 LAW / PROOF | Parser, spec lowering, lemma order, dependency cycles |
| 3 Modular and loops | Inlining, loop invariants, no effect-dropping summaries |
| 4 Effects | Traces, commit versus attempt, failure branches, single-request clock |
| 5 Adapter registry | Compiled-in adapters and trust records |
| 6 Express | Static routes, middleware, response commit |
| 7 PostgreSQL `pg` | Static SQL subset and transactions |
| 8 Fetch | Destination, method, four stored URLs |
| 9 Cross-adapter IAM | Proved in `examples/iam-token-issuer` |
| 10 Native `tsrs` hook | CLI orchestration only. No compiler-phase plugin |
| 11 Nest / Prisma / TypeORM | Subsets described in `docs/SOUNDNESS.md`, with passing example projects |
| 12 Cache and reports | SHA-256 cache of `unsat` only. SARIF and JUnit emitters. No language server, no parallel solver pool, no benchmark numbers |
| 13 Research | Not started |

## Still required before a production claim

The production checklist in the original plan is open. In particular this revision has no live Express, PostgreSQL, or Fetch conformance run against those runtimes, no external soundness review, no published benchmarks, and no proof-carrying build artifact beyond the verifier's own exit code. `docs/SOUNDNESS.md` is the boundary for the proofs that do pass.
