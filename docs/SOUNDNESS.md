# Soundness boundary

A `ts-proof` success is a proof of the generated SMT-LIB queries for one analyzed program. The queries use the supported TypeScript subset, the effect ghosts, and the adapter models named in the `VERIFY014` lines of the same report. Z3 must return `unsat` on the negation of each required obligation.

## Trusted computing base

The result depends on these components:

- the fail-closed parser and the VIR lowering
- verification-condition generation, including SSA equalities for branch joins
- the SMT-LIB encoding and Z3
- each official adapter's semantic model
- declared `external` and `externalNamespace` effects
- the build rule that refuses to treat a non-`unsat` cache entry as a proof

`tsrs` is the intended typechecker. This tree invokes the `tsrs` 0.23.0 CLI (`integration/tsrs/PIN`). It does not link the compiler crates, because that revision requires Rust 1.99. `verification.compilerRequired: false` and `TS_PROOF_SKIP_TSRS=1` skip that process and emit `VERIFY014`. The sources were not typechecked in that mode.

## Language

Integers are mathematical integers. Overflow of constant folding stays symbolic. `bigint` literals and integer literals share that domain. IEEE-754 `number`, division, and bitwise operations are rejected.

`===` and `!==` are equality. `==` and `!=` are rejected. `&&` and `||` in executable code require pure operands. In a formula, both sides are mathematical and are both evaluated.

A function call is inlined when it has a body in the program, or it is an adapter operation, or it is a declared external effect. A call with no model is `VERIFY003`. Recursion is rejected. An effectful call cannot be bound with `let` or `const`, and its result cannot be returned. Modular summaries that drop effects are rejected. There is no verified-function summary that omits a call's effects.

`return` inside middleware sets that middleware's `done` flag. Code after `next()` in the same function runs only when `done` is still false. Falling off the end of middleware is not `next()`. `next(err)` runs the error middleware. With no error middleware, that path is a throw. A throw sets the symbolic active flag to false, so later assignments keep their previous values.

The value caught by `catch` is not modeled. Reading it is `VERIFY002`.

Loops need a `// @invariant` comment. The obligations are entry, preservation, and an exit state havoced down to the invariant. `return` and `throw` inside a loop are rejected. Termination is not proved.

## Effects

One request is modeled, sequentially. Cross-request interleaving, connection pools, and isolation anomalies are outside the model. The report's database and HTTP assumptions say so.

`db.committed.<table>` counts successful inserts that are visible under that single-request abstraction. `UPDATE` shares the write-attempt counter and does not increment the insert count. `DELETE` does not decrement it. A rollback clears pending rows and leaves `db.last.*` in place. A law about a committed row mentions `db.committed` together with any `db.last` field it reads.

The response clock and `db.seq.<table>` increase only when that operation's success path runs. `response.status === 201` together with `response.clock > db.seq.tokens` fails when the handler emits 201 and inserts afterwards.

Fetch does not model the response status or body. `http.last_url` is the last completed destination. It is not a fact about every URL in the trace. Header and body expressions are sealed. An effect hidden inside them is `VERIFY002`.

KMS and any other `externalNamespace` entry are attempt counters plus a failure boolean. The remote service is not proved.

## Adapters

Official adapters are compiled into the binary. Application packages cannot register axioms.

Express models static `get`/`post`/`put`/`delete`/`patch`/`use` registrations, router mounts on an identifier, and synchronous middleware. Dynamic paths, wildcards, and overlapping patterns are `VERIFY011`. Request fields (`authenticated`, `authorized`, `agentId`, `principal`, `method`, `path`) are untrusted symbols. A TypeScript interface does not validate them. `res.status` does not commit a response. `res.json`, `res.send`, and `res.end` do. If status was not set, those commits use 200.

`pg` models static `SELECT`, `INSERT`, `UPDATE`, `DELETE`, `BEGIN`, `COMMIT`, and `ROLLBACK`. The SQL string must be a literal. Placeholders are `$1`, `$2`, ... in order. `WHERE` is a conjunction of `ident = $n`. Joins, comments, and concatenation are rejected. Nested `BEGIN`, or `COMMIT`/`ROLLBACK` while no transaction is active, is a failure path. Triggers, row-level security, check constraints, and other sessions are not in the model.

Prisma calls must use a receiver named `prisma`. `create` records a row as an autocommit. `update` does not increment the row count, and `where` is ignored. `$transaction` is `VERIFY011`. Returned rows are not modeled.

TypeORM accepts a receiver named `repo` or ending in `Repository`. The table name is that identifier. `insert` records a row. `save` does not. Query builders and relations are rejected.

NestJS models a class with `@Controller` and `@Get`/`@Post`/`@Put`/`@Delete`/`@Patch` string paths. `@UseGuards(Identifier)` treats the guard as a boolean. `false` commits 403 and skips the handler. Pipes, interceptors, filters, and dependency injection are rejected.

## Proof rules

Lemmas are checked in declaration order. A proved lemma may be used by a later lemma. An unproved lemma is `VERIFY008` and is not added to later assumptions, so a false lemma cannot make the next lemma vacuously true. Cycles are `VERIFY009` before Z3 runs. Lemma formulas are not assumed by the implementation proof.

An endpoint is verified when it has at least one endpoint law and every such law is proved. With `endpoints: "all"`, a discovered route with no law is `VERIFY010`. The coverage report lists discovered, verified, and unverified routes. It does not print a percentage.

## Out of scope

The verifier does not claim results about Node.js, V8, PostgreSQL, cryptographic algorithms, general concurrency, `eval`, reflection, latency, or the behavior of a remote service beyond the declared effect. Those limits are the same ones in the project plan. Native `tsrs` pipeline hooks, a language server, parallel solver workers, and live framework conformance runs are not part of this revision.
