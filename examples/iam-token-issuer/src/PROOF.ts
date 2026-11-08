const expiryProof = prove(expiryLaw, ({ now, ttl }) => {
    lemma("positive_ttl_increases", ttl.gt(0).implies(now.add(ttl).gt(now)));
});
