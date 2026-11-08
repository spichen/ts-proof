# Tests

The executable tests live next to the crates they cover. `cargo test` runs them.

Pipeline proofs and the example projects are in `crates/ts_proof_frontend`. They call `verify_program` or `check_project` with `compilerRequired: false`, so a `tsrs` binary on `PATH` does not decide the result.

Positive cases must be `unsat` under Z3. Negative cases must produce the expected `VERIFY00N` code. Unsupported syntax must fail before a query is treated as a proof.
