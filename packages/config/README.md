# @ts-proof/config

`ts-proof.config.json` is read from the project root.

`verification.required`, `verification.endpoints`, `verification.unsupported`, `verification.uncoveredEffects`, and `verification.unknownProofs` accept only the fail-closed values (`true`, `"all"`, and `"error"`). Any other value is `VERIFY002`.

`verification.compilerRequired` defaults to `true`. Set it to `false` only when you accept a `VERIFY014` record that `tsrs` was not invoked. That record is a trusted assumption. The sources were not typechecked.

`ts-proof.required.json` is an array of `{ "method", "path", "laws" }`. Each entry must be discovered, and each law name must exist on that route.

`solver.timeoutMs` is the Z3 limit in milliseconds. Timeout is `VERIFY004`.
