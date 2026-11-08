use crate::Span;
use serde::{Deserialize, Serialize};

/// Stable diagnostic codes. `ts-proof explain VERIFY001` prints [`ErrorCode::explain`].
#[derive(Clone, Copy, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub enum ErrorCode {
    /// A required obligation is not valid. The model is a counterexample.
    Verify001,
    /// The program uses syntax outside the supported semantic subset.
    Verify002,
    /// A call has no verified contract, trusted model, or adapter lowering.
    Verify003,
    /// The solver timed out. Required verification fails closed.
    Verify004,
    /// The solver returned `unknown`. Required verification fails closed.
    Verify005,
    /// The solver crashed or rejected the query.
    Verify006,
    /// A loop has no invariant. The engine will not guess one.
    Verify007,
    /// A lemma is not entailed by the law's precondition.
    Verify008,
    /// Proof dependencies are cyclic, dangling, or refer to a missing law.
    Verify009,
    /// A required endpoint or law is missing from the program.
    Verify010,
    /// An adapter recognized a framework use it cannot model.
    Verify011,
    /// A cached proof no longer matches its dependency key.
    Verify012,
    /// `tsrs` typechecking did not run or reported errors.
    Verify013,
    /// Informational record of a trusted assumption. Not a failure by itself.
    Verify014,
    /// The verified build could not emit because verification failed.
    Verify015,
}

impl ErrorCode {
    pub fn as_str(self) -> &'static str {
        match self {
            Self::Verify001 => "VERIFY001",
            Self::Verify002 => "VERIFY002",
            Self::Verify003 => "VERIFY003",
            Self::Verify004 => "VERIFY004",
            Self::Verify005 => "VERIFY005",
            Self::Verify006 => "VERIFY006",
            Self::Verify007 => "VERIFY007",
            Self::Verify008 => "VERIFY008",
            Self::Verify009 => "VERIFY009",
            Self::Verify010 => "VERIFY010",
            Self::Verify011 => "VERIFY011",
            Self::Verify012 => "VERIFY012",
            Self::Verify013 => "VERIFY013",
            Self::Verify014 => "VERIFY014",
            Self::Verify015 => "VERIFY015",
        }
    }

    pub fn parse(text: &str) -> Option<Self> {
        Some(match text.trim().to_ascii_uppercase().as_str() {
            "VERIFY001" => Self::Verify001,
            "VERIFY002" => Self::Verify002,
            "VERIFY003" => Self::Verify003,
            "VERIFY004" => Self::Verify004,
            "VERIFY005" => Self::Verify005,
            "VERIFY006" => Self::Verify006,
            "VERIFY007" => Self::Verify007,
            "VERIFY008" => Self::Verify008,
            "VERIFY009" => Self::Verify009,
            "VERIFY010" => Self::Verify010,
            "VERIFY011" => Self::Verify011,
            "VERIFY012" => Self::Verify012,
            "VERIFY013" => Self::Verify013,
            "VERIFY014" => Self::Verify014,
            "VERIFY015" => Self::Verify015,
            _ => return None,
        })
    }

    pub fn title(self) -> &'static str {
        match self {
            Self::Verify001 => "obligation not proved",
            Self::Verify002 => "unsupported syntax",
            Self::Verify003 => "unmodeled operation",
            Self::Verify004 => "solver timeout",
            Self::Verify005 => "solver returned unknown",
            Self::Verify006 => "solver error",
            Self::Verify007 => "missing loop invariant",
            Self::Verify008 => "unproved lemma",
            Self::Verify009 => "invalid proof dependency",
            Self::Verify010 => "required coverage missing",
            Self::Verify011 => "unsupported framework pattern",
            Self::Verify012 => "proof cache invalidated",
            Self::Verify013 => "tsrs typecheck failed",
            Self::Verify014 => "trusted assumption",
            Self::Verify015 => "verified build blocked",
        }
    }

    pub fn explain(self) -> &'static str {
        match self {
            Self::Verify001 => {
                "A required verification condition is not valid under the supported semantics. \
The counterexample assigns the mathematical variables of the encoded model. \
It is a counterexample to that encoding. Only an unsat result counts as a proof. \
A failing required obligation blocks a verified build."
            }
            Self::Verify002 => {
                "The source uses a TypeScript construct this verifier does not model \
(for example eval, number arithmetic, abstract equality, reflection, or ASI). \
The construct is rejected. It is not erased and it is not treated as skip."
            }
            Self::Verify003 => {
                "A call is not a verified function, a declared external effect, or an operation \
recognized by a pinned adapter. Unmodeled calls fail closed so a proof cannot ignore them."
            }
            Self::Verify004 => {
                "Z3 exceeded the configured timeout. Timeout is inconclusive. \
Required verification treats it as failure."
            }
            Self::Verify005 => {
                "Z3 returned unknown. Unknown is inconclusive. \
Required verification treats it as failure."
            }
            Self::Verify006 => {
                "Z3 crashed, could not be executed, or rejected the SMT-LIB query. \
This is a verification failure, not a successful proof."
            }
            Self::Verify007 => {
                "A while loop has no // @invariant annotation. The engine does not infer \
invariants and does not unroll the loop into an unsound finite check."
            }
            Self::Verify008 => {
                "A lemma in a PROOF file is not entailed by the law precondition and previously \
proved lemmas. Lemmas are never assumed. An unproved lemma fails the build."
            }
            Self::Verify009 => {
                "A proof names a missing law, a law names a missing target, or lemma dependencies \
form a cycle. Stale and circular proof structure is rejected."
            }
            Self::Verify010 => {
                "A required endpoint or required law is absent, or an endpoint has no endpoint law \
while verification.endpoints is \"all\". Discovery gaps must not look like coverage."
            }
            Self::Verify011 => {
                "An adapter recognized a framework call but its shape is outside the supported \
pattern (dynamic SQL, dynamic routes, unparsed decorators, overlapping routes). \
The adapter refuses the pattern instead of approximating it."
            }
            Self::Verify012 => {
                "A cache entry does not match the current source hash, contract hash, verifier \
version, adapter versions, or solver configuration. The proof is recomputed or rejected."
            }
            Self::Verify013 => {
                "Verified builds typecheck with the pinned tsrs compiler before verification. \
A missing binary, a type error, or a compiler failure blocks the build. \
TS_PROOF_SKIP_TSRS=1 is an explicit development bypass and is reported as a trusted assumption."
            }
            Self::Verify014 => {
                "An external behavior was assumed under a named trusted model. Trusted assumptions \
are printed in every verification report. They are not proofs about the external system."
            }
            Self::Verify015 => {
                "JavaScript is emitted only after every required obligation is proved. \
A failed, unknown, timed-out, or unsupported obligation blocks emission."
            }
        }
    }

    pub fn all() -> &'static [ErrorCode] {
        &[
            Self::Verify001,
            Self::Verify002,
            Self::Verify003,
            Self::Verify004,
            Self::Verify005,
            Self::Verify006,
            Self::Verify007,
            Self::Verify008,
            Self::Verify009,
            Self::Verify010,
            Self::Verify011,
            Self::Verify012,
            Self::Verify013,
            Self::Verify014,
            Self::Verify015,
        ]
    }
}

impl std::fmt::Display for ErrorCode {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(self.as_str())
    }
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Assignment {
    pub name: String,
    pub value: String,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Counterexample {
    pub assignments: Vec<Assignment>,
}

#[derive(Clone, Debug, PartialEq, Eq, Serialize, Deserialize)]
pub struct Diagnostic {
    pub code: ErrorCode,
    pub message: String,
    pub span: Option<Span>,
    pub notes: Vec<String>,
    pub counterexample: Option<Counterexample>,
    pub expected: Option<String>,
}

impl Diagnostic {
    pub fn new(code: ErrorCode, message: impl Into<String>) -> Self {
        Self {
            code,
            message: message.into(),
            span: None,
            notes: Vec::new(),
            counterexample: None,
            expected: None,
        }
    }

    pub fn at(mut self, span: Span) -> Self {
        self.span = Some(span);
        self
    }

    pub fn note(mut self, note: impl Into<String>) -> Self {
        self.notes.push(note.into());
        self
    }

    pub fn expected(mut self, expected: impl Into<String>) -> Self {
        self.expected = Some(expected.into());
        self
    }

    pub fn with_counterexample(mut self, counterexample: Counterexample) -> Self {
        self.counterexample = Some(counterexample);
        self
    }

    pub fn is_failure(&self) -> bool {
        !matches!(self.code, ErrorCode::Verify014)
    }
}
