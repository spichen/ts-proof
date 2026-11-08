const expiryLaw = law({
    target: calculateExpiry,
    inputs: { now: int(), ttl: int() },
    requires: ({ now, ttl }) => now.gte(0).and(ttl.gt(0)),
    ensures: ({ now, ttl }) => call(calculateExpiry, now, ttl).gt(now),
});
