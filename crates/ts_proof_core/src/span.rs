use serde::{Deserialize, Serialize};
use std::sync::Arc;

/// Byte span into a source file. Offsets are UTF-8 bytes.
#[derive(Clone, Debug, PartialEq, Eq, Hash, Serialize, Deserialize)]
pub struct Span {
    pub file: Arc<str>,
    pub start: u32,
    pub end: u32,
}

impl Span {
    pub fn new(file: impl AsRef<str>, start: u32, end: u32) -> Self {
        Self {
            file: Arc::from(file.as_ref()),
            start,
            end,
        }
    }

    pub fn dummy() -> Self {
        Self::new("<synthetic>", 0, 0)
    }

    pub fn line_col(&self, source: &str) -> (u32, u32) {
        line_col(source, self.start)
    }
}

pub fn line_col(source: &str, offset: u32) -> (u32, u32) {
    let mut line = 1u32;
    let mut col = 1u32;
    for (i, c) in source.char_indices() {
        if i >= offset as usize {
            break;
        }
        if c == '\n' {
            line += 1;
            col = 1;
        } else {
            col += 1;
        }
    }
    (line, col)
}

/// A source file retained so diagnostics can quote the original text.
#[derive(Clone, Debug, PartialEq, Eq)]
pub struct SourceFile {
    pub path: String,
    pub source: String,
}

impl SourceFile {
    pub fn line_col(&self, offset: u32) -> (u32, u32) {
        line_col(&self.source, offset)
    }

    pub fn snippet(&self, span: &Span) -> String {
        let start = (span.start as usize).min(self.source.len());
        let end = (span.end as usize).min(self.source.len());
        self.source.get(start..end).unwrap_or("").to_string()
    }

    pub fn line_text(&self, line: u32) -> String {
        self.source
            .lines()
            .nth((line.saturating_sub(1)) as usize)
            .unwrap_or("")
            .to_string()
    }
}
