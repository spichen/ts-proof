function calculateExpiry(now: bigint, ttl: bigint): bigint {
    return now + ttl;
}
