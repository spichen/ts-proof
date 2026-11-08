//! Proof cache. Only an `unsat` result is stored.
//!
//! A file that is missing is a miss and is recomputed. A file that exists but
//! does not contain `unsat` is invalid: it is never treated as a proof.

use sha2::{Digest, Sha256};
use std::fs;
use std::path::{Path, PathBuf};

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum CacheLookup {
    Miss,
    Unsat,
    Invalid,
}

pub struct Cache {
    dir: PathBuf,
}

impl Cache {
    pub fn open(dir: impl Into<PathBuf>) -> Self {
        Self { dir: dir.into() }
    }

    pub fn lookup(&self, key: &str) -> CacheLookup {
        let Some(path) = self.path(key) else {
            return CacheLookup::Invalid;
        };
        match fs::read(&path) {
            Ok(bytes) if bytes == b"unsat\n" => CacheLookup::Unsat,
            Ok(_) => CacheLookup::Invalid,
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => CacheLookup::Miss,
            Err(_) => CacheLookup::Invalid,
        }
    }

    /// Record a proof. Callers must pass a key whose solver result was `unsat`.
    pub fn store_unsat(&self, key: &str) -> std::io::Result<()> {
        let Some(path) = self.path(key) else {
            return Err(std::io::Error::new(
                std::io::ErrorKind::InvalidInput,
                "cache key is not a sha256 hex digest",
            ));
        };
        fs::create_dir_all(&self.dir)?;
        fs::write(path, b"unsat\n")
    }

    pub fn forget(&self, key: &str) -> std::io::Result<()> {
        let Some(path) = self.path(key) else {
            return Ok(());
        };
        match fs::remove_file(path) {
            Ok(()) => Ok(()),
            Err(err) if err.kind() == std::io::ErrorKind::NotFound => Ok(()),
            Err(err) => Err(err),
        }
    }
}

impl Cache {
    fn path(&self, key: &str) -> Option<PathBuf> {
        if key.len() == 64 && key.chars().all(|c| c.is_ascii_hexdigit()) {
            Some(self.dir.join(key))
        } else {
            None
        }
    }
}

pub fn digest(material: &str) -> String {
    let hash = Sha256::digest(material.as_bytes());
    hash.iter().map(|byte| format!("{byte:02x}")).collect()
}

pub fn cache_dir(project: &Path) -> PathBuf {
    project.join(".ts-proof").join("cache")
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn only_unsat_is_a_hit_and_other_bytes_are_invalid() {
        let dir = std::env::temp_dir().join(format!("ts-proof-cache-{}", std::process::id()));
        let _ = fs::remove_dir_all(&dir);
        let cache = Cache::open(&dir);
        let key = digest("obligation");
        assert_eq!(cache.lookup(&key), CacheLookup::Miss);
        cache.store_unsat(&key).unwrap();
        assert_eq!(cache.lookup(&key), CacheLookup::Unsat);
        fs::write(dir.join(&key), b"sat\n").unwrap();
        assert_eq!(cache.lookup(&key), CacheLookup::Invalid);
        cache.forget(&key).unwrap();
        assert_eq!(cache.lookup(&key), CacheLookup::Miss);
        assert_eq!(cache.lookup("../not-a-key"), CacheLookup::Invalid);
        let _ = fs::remove_dir_all(&dir);
    }
}
