const kms = externalNamespace({ signToken: "kms.sign" });
const app = express();
const pool = new Pool({});

function calculateExpiry(now: bigint, ttl: bigint): bigint {
    return now + ttl;
}

function issueToken(authorized: boolean): null {
    if (!authorized) {
        return null;
    }
    return kms.signToken();
}

function authenticate(req, res, next) {
    if (!req.authenticated) {
        res.status(401).json({ ok: false });
        return;
    }
    next();
}

function authorize(req, res, next) {
    if (!req.authorized) {
        res.status(403).json({ ok: false });
        return;
    }
    next();
}

function mintToken(req, res) {
    if (!req.authorized) {
        res.status(403).json({ ok: false });
        return;
    }
    const expiry = calculateExpiry(req.agentId, 60);
    kms.signToken();
    pool.query(
        "INSERT INTO tokens(agent_id, principal, expiry) VALUES($1, $2, $3)",
        [req.agentId, req.principal, expiry]
    );
    res.status(201).json({ ok: true });
}

app.post("/agents/:id/tokens", authenticate, authorize, mintToken);
