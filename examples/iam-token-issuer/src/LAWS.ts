const expiryLaw = law({
    target: calculateExpiry,
    inputs: { now: int(), ttl: int() },
    requires: ({ now, ttl }) => now.gte(0).and(ttl.gt(0)),
    ensures: ({ now, ttl }) => call(calculateExpiry, now, ttl).gt(now),
});

const issueLaw = law({
    target: issueToken,
    ensures: ({ authorized }) => implies(!authorized, trace.count("kms.sign") === 0),
});

const unauthorizedNoSign = endpointLaw({
    method: "POST",
    path: "/agents/:id/tokens",
    name: "unauthorized_no_sign",
    ensures: ({ request, trace }) => implies(!request.authorized, trace.count("kms.sign") === 0),
});

const unauthorizedNoWrite = endpointLaw({
    method: "POST",
    path: "/agents/:id/tokens",
    name: "unauthorized_no_write",
    ensures: ({ request, trace }) => implies(!request.authorized, trace.count("db.write.tokens") === 0),
});

const identity = endpointLaw({
    method: "POST",
    path: "/agents/:id/tokens",
    name: "identity_integrity",
    ensures: ({ request, response, db }) => implies(
        response.status === 201,
        db.committed.tokens > 0 && db.last.tokens.principal === request.principal
    ),
});

const persisted = endpointLaw({
    method: "POST",
    path: "/agents/:id/tokens",
    name: "response_after_persistence",
    ensures: ({ response, db }) => implies(
        response.status === 201,
        db.committed.tokens > 0 && response.clock > db.seq.tokens
    ),
});
