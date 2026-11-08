function notify(authorized: boolean): null {
    if (!authorized) {
        return null;
    }
    fetch("https://kms.example/sign", { method: "POST" });
    return null;
}

const unauthorized_no_fetch = law({
    target: notify,
    ensures: ({ authorized }) => implies(!authorized, trace.count("http.fetch") === 0),
});

const completed_fetch_stays_on_allowlist = law({
    target: notify,
    ensures: () => implies(trace.count("http.fetch.ok") > 0, http.last_url === "https://kms.example/sign"),
});
