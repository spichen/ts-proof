const app = express();
const pool = new Pool({});

function authorize(req, res, next) {
    if (!req.authorized) {
        res.status(403).json({ ok: false });
        return;
    }
    next();
}

function mint(req, res) {
    pool.query("INSERT INTO tokens(agent_id) VALUES($1)", [req.agentId]);
    res.status(201).json({ ok: true });
}

app.post("/tokens", authorize, mint);

const unauthorizedNoWrite = endpointLaw({
    method: "POST",
    path: "/tokens",
    name: "unauthorized_no_write",
    ensures: ({ request, trace }) => implies(!request.authorized, trace.count("db.write.tokens") === 0),
});
