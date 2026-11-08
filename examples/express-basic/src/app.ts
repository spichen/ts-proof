const app = express();

function authenticate(req, res, next) {
    if (!req.authenticated) {
        res.status(401).json({ ok: false });
        return;
    }
    next();
}

function ok(req, res) {
    res.status(200).json({ ok: true });
}

app.get("/health", authenticate, ok);

const unauthenticatedIs401 = endpointLaw({
    method: "GET",
    path: "/health",
    name: "unauthenticated_is_401",
    ensures: ({ request, response }) => implies(!request.authenticated, response.status === 401),
});
