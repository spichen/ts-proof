function save(agentId: bigint, principal: bigint): null {
    prisma.token.create({ data: { agentId: agentId, principal: principal } });
    return null;
}

const committed_row_keeps_principal = law({
    target: save,
    ensures: ({ principal }) => implies(db.committed.token > 0, db.last.token.principal === principal),
});
