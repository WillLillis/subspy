//! Paths as git records them: root-relative, `/`-separated bytes.

use std::{
    borrow::{Borrow, Cow},
    path::Path,
    str::Utf8Error,
};

use bincode::{BorrowDecode, Encode};

/// A root-relative path exactly as git records it in the index and in trees.
#[derive(Clone, PartialEq, Eq, PartialOrd, Ord, Hash, Encode, BorrowDecode)]
pub struct GitPath(Vec<u8>);

impl GitPath {
    #[must_use]
    pub const fn as_bytes(&self) -> &[u8] {
        self.0.as_slice()
    }

    /// The path on the filesystem, relative to the working tree root.
    ///
    /// # Errors
    ///
    /// On non-Unix platforms git records paths as UTF-8, and a path that is not
    /// UTF-8 has no filesystem equivalent.
    pub fn to_path(&self) -> Result<&Path, Utf8Error> {
        super::path_from_bytes(&self.0)
    }

    /// The path for log and error messages, with invalid bytes replaced. Output
    /// that mirrors git goes through the byte quoting in `status::quote`.
    #[must_use]
    pub fn display(&self) -> Cow<'_, str> {
        String::from_utf8_lossy(&self.0)
    }
}

impl From<&[u8]> for GitPath {
    fn from(bytes: &[u8]) -> Self {
        Self(bytes.to_vec())
    }
}

impl From<Vec<u8>> for GitPath {
    fn from(bytes: Vec<u8>) -> Self {
        Self(bytes)
    }
}

impl From<&str> for GitPath {
    fn from(path: &str) -> Self {
        Self::from(path.as_bytes())
    }
}

impl AsRef<[u8]> for GitPath {
    fn as_ref(&self) -> &[u8] {
        &self.0
    }
}

impl Borrow<[u8]> for GitPath {
    fn borrow(&self) -> &[u8] {
        &self.0
    }
}

impl PartialEq<[u8]> for GitPath {
    fn eq(&self, other: &[u8]) -> bool {
        *self.0 == *other
    }
}

impl PartialEq<str> for GitPath {
    fn eq(&self, other: &str) -> bool {
        *self.0 == *other.as_bytes()
    }
}

impl PartialEq<&str> for GitPath {
    fn eq(&self, other: &&str) -> bool {
        *self.0 == *other.as_bytes()
    }
}

/// Prints like a string literal. A path that is not UTF-8 prints with every
/// non-ASCII byte escaped (`"sub\xff"`).
impl std::fmt::Debug for GitPath {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match std::str::from_utf8(&self.0) {
            Ok(path) => write!(f, "{path:?}"),
            Err(_) => write!(f, "\"{}\"", self.0.escape_ascii()),
        }
    }
}
