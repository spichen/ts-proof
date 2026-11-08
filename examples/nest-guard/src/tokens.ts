const kms = externalNamespace({ signToken: "kms.sign" });

function allow(req): boolean {
    return req.authorized;
}

@Controller("/agents")
class Tokens {
    @UseGuards(allow)
    @Post("/tokens")
    mint(req, res) {
        kms.signToken();
        res.status(201).json({ ok: true });
    }
}

const nestLaw = endpointLaw({
    method: "POST",
    path: "/agents/tokens",
    name: "nest_unauthorized_no_sign",
    ensures: ({ request, trace }) => implies(!request.authorized, trace.count("kms.sign") === 0),
});
