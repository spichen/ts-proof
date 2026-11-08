function save(agentId: bigint, principal: bigint): null {
    tokenRepository.insert({ agentId: agentId, principal: principal });
    return null;
}

const committed_row_keeps_principal = law({
    target: save,
    ensures: ({ principal }) => implies(
        db.committed.tokenRepository > 0,
        db.last.tokenRepository.principal === principal
    ),
});
