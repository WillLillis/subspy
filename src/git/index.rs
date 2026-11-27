//! git's index file, versions 2 to 4, read without verifying its checksum.
//!
//! [`Index`] keeps the file's own entry records and the offset of each, and
//! [`Entry`] decodes a field when it is read. Version 4 stores each path as a
//! suffix of the one before it, so the parse rewrites those entries into
//! records holding whole paths. Every path is followed by a NUL in place, ready
//! for system calls.
//!
//! Split and sparse indexes, which the `link` and `sdir` extensions mark, are
//! refused.

use std::{ffi::CStr, num::NonZeroU32, ops::Range};

use thiserror::Error;

use super::ObjectFormat;

/// The signature that opens an index file.
const SIGNATURE: &[u8; 4] = b"DIRC";
/// Where the version sits in the file header.
const VERSION_OFFSET: usize = 4;
/// Where the entry count sits in the file header.
const ENTRY_COUNT_OFFSET: usize = 8;
/// The file header: signature, version, and entry count.
const FILE_HEADER_LEN: usize = 12;
/// An extension's header: signature and size.
const EXTENSION_HEADER_LEN: usize = 8;
/// The stat data that opens every entry record, before the object id.
const STAT_DATA_LEN: usize = 40;
const FLAG_WORD_LEN: usize = 2;
/// The shortest entry record: stat data, a SHA-1 id, flags, and a NUL,
/// padded.
const MIN_ENTRY_LEN: usize = 64;
/// Records before version 4 are padded with NULs to a multiple of this.
const ENTRY_ALIGN: usize = 8;

/// Where the ctime's seconds sit in an entry record.
const CTIME_SECS_OFFSET: usize = 0;
/// Where the mtime's seconds sit in an entry record.
const MTIME_SECS_OFFSET: usize = 8;
/// Where the inode number sits in an entry record.
const INO_OFFSET: usize = 20;
/// Where the mode sits in an entry record.
const MODE_OFFSET: usize = 24;
/// Where the owner's user id sits in an entry record.
const UID_OFFSET: usize = 28;
/// Where the owner's group id sits in an entry record.
const GID_OFFSET: usize = 32;
/// Where the file size sits in an entry record.
const SIZE_OFFSET: usize = 36;

/// Flags bit: git assumes the file unchanged.
const FLAG_ASSUME_VALID: u16 = 0x8000;
/// Flags bit: an extended flags word follows.
const FLAG_EXTENDED: u16 = 0x4000;
/// Flags bits: the merge stage.
const FLAG_STAGE: u16 = 0x3000;
/// Where the merge stage starts in the flags.
const STAGE_SHIFT: u16 = 12;
/// Flags bits: the path's length, saturated for longer paths.
const NAME_MASK: u16 = 0x0fff;
/// Extended flags bit: the file is left out of the work tree.
const EXT_SKIP_WORKTREE: u16 = 0x4000;
/// Extended flags bit: the entry was added with `git add --intent-to-add`.
const EXT_INTENT_TO_ADD: u16 = 0x2000;

/// Failure to parse an index file.
#[derive(Error, Debug)]
pub enum IndexError {
    #[error("not an index file")]
    NotAnIndex,
    #[error("index version {0} is not supported")]
    UnsupportedVersion(u32),
    #[error("index file is truncated")]
    Truncated,
    #[error("index file is too large")]
    TooLarge,
    #[error("index entry {0} has a malformed path")]
    MalformedPath(usize),
    #[error("index entry {position} has unknown extended flags {flags:#06x}")]
    UnknownExtendedFlags { position: usize, flags: u16 },
    #[error("index uses the {} extension, which subspy cannot read", String::from_utf8_lossy(.0))]
    UnsupportedExtension([u8; 4]),
}

/// A parsed index file.
pub struct Index {
    /// Every entry's record, in order: the file's own records before
    /// version 4, rewritten with whole paths in version 4.
    records: Box<[u8]>,
    /// Where each entry's record starts in `records`.
    offsets: Box<[u32]>,
    tree: Option<CacheTree>,
    format: ObjectFormat,
    has_conflicts: bool,
}

impl Index {
    /// Parses the index file `bytes`, whose object ids are in `format`.
    ///
    /// # Errors
    ///
    /// Fails if `bytes` is not an index file of version 2, 3, or 4, is
    /// truncated or malformed, or uses an extension that changes how its
    /// entries are read.
    pub fn parse(mut bytes: Vec<u8>, format: ObjectFormat) -> Result<Self, IndexError> {
        if bytes.len() < FILE_HEADER_LEN + format.raw_len()
            || &bytes[..SIGNATURE.len()] != SIGNATURE
        {
            return Err(IndexError::NotAnIndex);
        }
        if u32::try_from(bytes.len()).is_err() {
            return Err(IndexError::TooLarge);
        }
        let version = be32(&bytes, VERSION_OFFSET);
        if !(2..=4).contains(&version) {
            return Err(IndexError::UnsupportedVersion(version));
        }
        let count = be32(&bytes, ENTRY_COUNT_OFFSET) as usize;
        let end = bytes.len() - format.raw_len();
        if count > (end - FILE_HEADER_LEN) / MIN_ENTRY_LEN {
            return Err(IndexError::Truncated);
        }
        let mut entries = Entries {
            format,
            offsets: Vec::with_capacity(count),
            has_conflicts: false,
        };
        let (records, tree) = if version == 4 {
            let (rewritten, extensions) = entries.read_compressed(&bytes, count, end)?;
            (rewritten, read_extensions(&bytes, extensions, end, format)?)
        } else {
            let extensions = entries.read(&bytes, count, end)?;
            let tree = read_extensions(&bytes, extensions, end, format)?;
            // Only the entry records are read from here on.
            bytes.truncate(extensions);
            (bytes, tree)
        };
        Ok(Self {
            records: records.into_boxed_slice(),
            offsets: entries.offsets.into_boxed_slice(),
            tree,
            format,
            has_conflicts: entries.has_conflicts,
        })
    }

    fn entry_at(&self, offset: u32) -> Entry<'_> {
        let start = offset as usize;
        let flags = be16(&self.records, start + STAT_DATA_LEN + self.format.raw_len());
        let extended = flags & FLAG_EXTENDED != 0;
        let header = header_len(self.format, extended);
        let len = match usize::from(flags & NAME_MASK) {
            len if len < usize::from(NAME_MASK) => len,
            // INVARIANT: the parse found the NUL that ends this record.
            _ => memchr::memchr(0, &self.records[start + header..]).unwrap(),
        };
        Entry {
            record: &self.records[start..=start + header + len],
            format: self.format,
            extended,
        }
    }

    #[must_use]
    pub const fn len(&self) -> usize {
        self.offsets.len()
    }

    #[must_use]
    pub const fn is_empty(&self) -> bool {
        self.offsets.is_empty()
    }

    /// The entry at `position`, in the index's order.
    ///
    /// # Panics
    ///
    /// Panics if `position` is not below [`Self::len`].
    #[must_use]
    pub fn entry(&self, position: usize) -> Entry<'_> {
        self.entry_at(self.offsets[position])
    }

    /// Every entry, in the index's order: by path, then by stage.
    pub fn entries(&self) -> impl ExactSizeIterator<Item = Entry<'_>> {
        self.offsets.iter().map(|&offset| self.entry_at(offset))
    }

    /// Whether any entry has a merge stage, meaning a conflict is unresolved.
    #[must_use]
    pub const fn has_conflicts(&self) -> bool {
        self.has_conflicts
    }

    /// The position of the first entry whose path sorts at or after `path`.
    #[must_use]
    pub fn first_at_or_after(&self, path: &[u8]) -> usize {
        self.offsets
            .partition_point(|&offset| self.entry_at(offset).path() < path)
    }

    /// The entry for `path` at merge stage `stage`.
    #[must_use]
    pub fn find(&self, path: &[u8], stage: u8) -> Option<Entry<'_>> {
        self.offsets[self.first_at_or_after(path)..]
            .iter()
            .map(|&offset| self.entry_at(offset))
            .take_while(|entry| entry.path() == path)
            .find(|entry| entry.stage() == stage)
    }

    /// The cache-tree's root, when the index has a cache-tree.
    #[must_use]
    pub fn cache_tree(&self) -> Option<TreeNode<'_>> {
        self.tree.as_ref().map(|tree| TreeNode {
            tree,
            format: self.format,
            node: 0,
        })
    }
}

/// The entries a parse has found so far.
struct Entries {
    format: ObjectFormat,
    /// Where each entry's record starts.
    offsets: Vec<u32>,
    has_conflicts: bool,
}

impl Entries {
    /// Records the offset of each of `count` entries before version 4, and
    /// returns where the extensions start.
    fn read(&mut self, bytes: &[u8], count: usize, end: usize) -> Result<usize, IndexError> {
        let mut pos = FILE_HEADER_LEN;
        for position in 0..count {
            let (header, len) = self.read_flags(bytes, pos, end, position)?;
            let name = &bytes[pos + header..end];
            let len = match len {
                len if len < usize::from(NAME_MASK) => len,
                _ => memchr::memchr(0, name).ok_or(IndexError::Truncated)?,
            };
            match name.get(len) {
                Some(0) => {}
                Some(_) => return Err(IndexError::MalformedPath(position)),
                None => return Err(IndexError::Truncated),
            }
            self.offsets.push(offset(pos)?);
            // NUL-padded to a multiple of `ENTRY_ALIGN`, with at least one NUL.
            pos += (header + len + ENTRY_ALIGN) & !(ENTRY_ALIGN - 1);
        }
        Ok(pos)
    }

    /// Reads the flags of the entry record at `pos`. Returns the length of
    /// the record before its path, and the flags' path length.
    fn read_flags(
        &mut self,
        bytes: &[u8],
        pos: usize,
        end: usize,
        position: usize,
    ) -> Result<(usize, usize), IndexError> {
        let flags_at = pos + STAT_DATA_LEN + self.format.raw_len();
        if flags_at + FLAG_WORD_LEN > end {
            return Err(IndexError::Truncated);
        }
        let flags = be16(bytes, flags_at);
        self.has_conflicts |= flags & FLAG_STAGE != 0;
        let extended = flags & FLAG_EXTENDED != 0;
        if extended {
            if flags_at + 2 * FLAG_WORD_LEN > end {
                return Err(IndexError::Truncated);
            }
            let ext = be16(bytes, flags_at + FLAG_WORD_LEN);
            // git refuses an entry with an extended flag it does not know.
            if ext & !(EXT_SKIP_WORKTREE | EXT_INTENT_TO_ADD) != 0 {
                return Err(IndexError::UnknownExtendedFlags {
                    position,
                    flags: ext,
                });
            }
        }
        let header = header_len(self.format, extended);
        if pos + header > end {
            return Err(IndexError::Truncated);
        }
        Ok((header, usize::from(flags & NAME_MASK)))
    }

    /// Rewrites version 4's `count` entries into records with whole paths.
    /// Returns the records and where the extensions start.
    fn read_compressed(
        &mut self,
        bytes: &[u8],
        count: usize,
        end: usize,
    ) -> Result<(Vec<u8>, usize), IndexError> {
        // Whole paths outgrow the file. Boxing the records gives back the
        // capacity they leave unused, which they never touch.
        let mut rewritten = Vec::with_capacity(2 * bytes.len());
        let mut pos = FILE_HEADER_LEN;
        let mut previous: Range<usize> = 0..0;
        for position in 0..count {
            let malformed = || IndexError::MalformedPath(position);
            let (header, len) = self.read_flags(bytes, pos, end, position)?;
            let name = &bytes[pos + header..end];
            let (strip, varint_len) = decode_varint(name).ok_or_else(malformed)?;
            // git ignores the first entry's strip count, with no path before it.
            let keep = match position {
                0 => 0,
                _ => previous.len().checked_sub(strip).ok_or_else(malformed)?,
            };
            let suffix = &name[varint_len..];
            let suffix_len = match len {
                len if len < usize::from(NAME_MASK) => {
                    len.checked_sub(keep).ok_or_else(malformed)?
                }
                _ => memchr::memchr(0, suffix).ok_or(IndexError::Truncated)?,
            };
            match suffix.get(suffix_len) {
                Some(0) => {}
                Some(_) => return Err(malformed()),
                None => return Err(IndexError::Truncated),
            }
            self.offsets.push(offset(rewritten.len())?);
            rewritten.extend_from_slice(&bytes[pos..pos + header]);
            let path = rewritten.len();
            rewritten.extend_from_within(previous.start..previous.start + keep);
            rewritten.extend_from_slice(&suffix[..suffix_len]);
            rewritten.push(0);
            previous = path..path + keep + suffix_len;
            pos += header + varint_len + suffix_len + 1;
        }
        Ok((rewritten, pos))
    }
}

/// Reads the extensions between `pos` and the checksum at `end`, and returns
/// the cache-tree when the index has one git would read.
fn read_extensions(
    bytes: &[u8],
    mut pos: usize,
    end: usize,
    format: ObjectFormat,
) -> Result<Option<CacheTree>, IndexError> {
    let mut tree = None;
    while pos + EXTENSION_HEADER_LEN <= end {
        let signature: [u8; 4] = bytes[pos..pos + 4].try_into().unwrap();
        let data = pos + EXTENSION_HEADER_LEN;
        let data_end = data + be32(bytes, pos + 4) as usize;
        if data_end > end {
            return Err(IndexError::Truncated);
        }
        match &signature {
            b"TREE" => tree = CacheTree::read(&bytes[data..data_end], format),
            // Extensions that only add information start with an uppercase
            // letter.
            [b'A'..=b'Z', ..] => {}
            _ => return Err(IndexError::UnsupportedExtension(signature)),
        }
        pos = data_end;
    }
    Ok(tree)
}

/// One entry of an [`Index`], decoded from its record as fields are read.
#[derive(Clone, Copy)]
pub struct Entry<'a> {
    /// The record, from its stat data through the NUL after its path.
    record: &'a [u8],
    format: ObjectFormat,
    extended: bool,
}

impl<'a> Entry<'a> {
    /// The seconds of the inode change time git recorded.
    #[must_use]
    pub fn ctime_secs(self) -> u32 {
        be32(self.record, CTIME_SECS_OFFSET)
    }

    /// The seconds of the modification time git recorded.
    #[must_use]
    pub fn mtime_secs(self) -> u32 {
        be32(self.record, MTIME_SECS_OFFSET)
    }

    /// The inode number git recorded.
    #[must_use]
    pub fn ino(self) -> u32 {
        be32(self.record, INO_OFFSET)
    }

    /// The mode git records for the entry's object.
    #[must_use]
    pub fn mode(self) -> u32 {
        be32(self.record, MODE_OFFSET)
    }

    /// The owner's user id git recorded.
    #[must_use]
    pub fn uid(self) -> u32 {
        be32(self.record, UID_OFFSET)
    }

    /// The owner's group id git recorded.
    #[must_use]
    pub fn gid(self) -> u32 {
        be32(self.record, GID_OFFSET)
    }

    /// The file size git recorded, truncated to 32 bits.
    #[must_use]
    pub fn size(self) -> u32 {
        be32(self.record, SIZE_OFFSET)
    }

    /// The object id, in the index's object format.
    #[must_use]
    pub fn oid(self) -> &'a [u8] {
        &self.record[STAT_DATA_LEN..STAT_DATA_LEN + self.format.raw_len()]
    }

    fn flags(self) -> u16 {
        be16(self.record, STAT_DATA_LEN + self.format.raw_len())
    }

    fn extended_flags(self) -> u16 {
        if self.extended {
            be16(
                self.record,
                STAT_DATA_LEN + self.format.raw_len() + FLAG_WORD_LEN,
            )
        } else {
            0
        }
    }

    /// The merge stage: 0 for a resolved path, then 1, 2, and 3 for a
    /// conflict's base, ours, and theirs.
    #[must_use]
    pub fn stage(self) -> u8 {
        ((self.flags() & FLAG_STAGE) >> STAGE_SHIFT) as u8
    }

    /// Whether git assumes the file unchanged (`update-index
    /// --assume-unchanged`).
    #[must_use]
    pub fn assume_valid(self) -> bool {
        self.flags() & FLAG_ASSUME_VALID != 0
    }

    /// Whether the file is left out of the work tree, by a sparse checkout or
    /// `update-index --skip-worktree`.
    #[must_use]
    pub fn skip_worktree(self) -> bool {
        self.extended_flags() & EXT_SKIP_WORKTREE != 0
    }

    /// Whether the entry was added with `git add --intent-to-add`.
    #[must_use]
    pub fn intent_to_add(self) -> bool {
        self.extended_flags() & EXT_INTENT_TO_ADD != 0
    }

    /// The path, relative to the work tree's root.
    #[must_use]
    pub fn path(self) -> &'a [u8] {
        &self.record[header_len(self.format, self.extended)..self.record.len() - 1]
    }

    /// The path with the NUL that follows it, for system calls.
    ///
    /// # Panics
    ///
    /// Panics if no NUL follows the path, which [`Index::parse`] rules out.
    #[must_use]
    pub fn c_path(self) -> &'a CStr {
        CStr::from_bytes_until_nul(&self.record[header_len(self.format, self.extended)..]).unwrap()
    }
}

/// The `TREE` extension.
struct CacheTree {
    /// The extension's bytes, which the nodes point into.
    bytes: Box<[u8]>,
    /// The directories, in the extension's pre-order, root first.
    nodes: Box<[Node]>,
}

impl CacheTree {
    /// Parses the extension's `data`, or returns `None` when it is malformed,
    /// which git reads as having no cache-tree.
    fn read(data: &[u8], format: ObjectFormat) -> Option<Self> {
        // The root's name is empty.
        if data.first() != Some(&0) {
            return None;
        }
        let mut nodes = Vec::new();
        // Each open directory, and how many of its subtrees are still to come.
        let mut open: Vec<(usize, i64)> = Vec::new();
        let mut at = 0;
        loop {
            let (node, subtrees) = read_node(data, &mut at, format)?;
            if let Some((_, remaining)) = open.last_mut() {
                *remaining -= 1;
            }
            open.push((nodes.len(), subtrees));
            nodes.push(node);
            // A directory closes after its last subtree, so its subtree is
            // every node pushed since. git reads a negative count as no
            // subtrees.
            while let Some(&(index, ..=0)) = open.last() {
                open.pop();
                nodes[index].size = u32::try_from(nodes.len() - index).ok()?;
            }
            if open.is_empty() {
                break;
            }
        }
        Some(Self {
            bytes: data.into(),
            nodes: nodes.into_boxed_slice(),
        })
    }
}

/// One cache-tree directory.
struct Node {
    /// The directory's name, as a range of the extension.
    name: (u32, u32),
    /// Where the directory's tree id starts in the extension, unless the node
    /// is invalid. Never 0, where the root's empty name sits.
    oid: Option<NonZeroU32>,
    /// Nodes in this subtree, itself included. Its children fill the rest.
    size: u32,
}

const _: () = assert!(size_of::<Node>() == 16);

/// A directory of an [`Index`]'s cache-tree.
#[derive(Clone, Copy)]
pub struct TreeNode<'a> {
    tree: &'a CacheTree,
    format: ObjectFormat,
    node: usize,
}

impl<'a> TreeNode<'a> {
    /// The id of the tree the directory's entries form, unless an entry
    /// below it changed after the tree was computed.
    #[must_use]
    pub fn oid(self) -> Option<&'a [u8]> {
        let at = self.tree.nodes[self.node].oid?.get() as usize;
        Some(&self.tree.bytes[at..at + self.format.raw_len()])
    }

    /// The child directory `name`.
    #[must_use]
    pub fn child(self, name: &[u8]) -> Option<Self> {
        let nodes = &self.tree.nodes;
        let end = self.node + nodes[self.node].size as usize;
        let mut child = self.node + 1;
        while child < end {
            let (start, name_end) = nodes[child].name;
            if self.tree.bytes[start as usize..name_end as usize] == *name {
                return Some(Self {
                    node: child,
                    ..self
                });
            }
            child += nodes[child].size as usize;
        }
        None
    }
}

/// Reads the directory record at `at`. Returns its node, whose size is left
/// for its subtrees to settle, and how many subtrees follow it.
fn read_node(data: &[u8], at: &mut usize, format: ObjectFormat) -> Option<(Node, i64)> {
    let rest = data.get(*at..)?;
    let name_len = memchr::memchr(0, rest)?;
    let name = (
        u32::try_from(*at).ok()?,
        u32::try_from(*at + name_len).ok()?,
    );
    *at += name_len + 1;
    let rest = &data[*at..];
    let space = memchr::memchr(b' ', rest)?;
    let newline = memchr::memchr(b'\n', rest)?;
    let entry_count = parse_int(&rest[..space])?;
    let subtrees = parse_int(rest.get(space + 1..newline)?)?;
    *at += newline + 1;
    // An invalid node, with a negative entry count, has no tree id.
    let oid = if entry_count < 0 {
        None
    } else {
        data.get(*at..*at + format.raw_len())?;
        let oid = NonZeroU32::new(u32::try_from(*at).ok()?)?;
        *at += format.raw_len();
        Some(oid)
    };
    Some((Node { name, oid, size: 0 }, subtrees))
}

/// A decimal integer with an optional minus sign.
fn parse_int(digits: &[u8]) -> Option<i64> {
    let (sign, digits) = match digits {
        [b'-', rest @ ..] => (-1, rest),
        _ => (1, digits),
    };
    if digits.is_empty() {
        return None;
    }
    digits.iter().try_fold(0i64, |n, &d| {
        let digit = i64::from(d.checked_sub(b'0').filter(|d| *d < 10)?);
        n.checked_mul(10)?.checked_add(sign * digit)
    })
}

/// git's `decode_varint`: the value at the start of `bytes` and how many
/// bytes it took, or `None` when it overflows or runs out of bytes.
fn decode_varint(bytes: &[u8]) -> Option<(usize, usize)> {
    let mut value = 0usize;
    for (i, &b) in bytes.iter().enumerate() {
        value = value.checked_mul(128)? | usize::from(b & 0x7f);
        if b & 0x80 == 0 {
            return Some((value, i + 1));
        }
        value = value.checked_add(1)?;
    }
    None
}

/// The length of an entry record before its path.
const fn header_len(format: ObjectFormat, extended: bool) -> usize {
    STAT_DATA_LEN
        + format.raw_len()
        + if extended {
            2 * FLAG_WORD_LEN
        } else {
            FLAG_WORD_LEN
        }
}

fn offset(pos: usize) -> Result<u32, IndexError> {
    u32::try_from(pos).map_err(|_| IndexError::TooLarge)
}

fn be32(bytes: &[u8], at: usize) -> u32 {
    u32::from_be_bytes(bytes[at..at + 4].try_into().unwrap())
}

fn be16(bytes: &[u8], at: usize) -> u16 {
    u16::from_be_bytes(bytes[at..at + 2].try_into().unwrap())
}

#[cfg(test)]
mod tests {
    use super::*;

    use std::{collections::HashMap, fmt::Write as _, path::Path};

    use pretty_assertions::assert_eq;
    use rstest::rstest;
    use tempfile::TempDir;
    use testutil::Repo;

    /// git's in-memory `ce_flags` bit for an assumed-unchanged entry, as
    /// `ls-files --debug` prints it.
    const CE_VALID: u32 = 0x8000;
    /// The in-memory bit for an intent-to-add entry.
    const CE_INTENT_TO_ADD: u32 = 1 << 29;
    /// The in-memory bit for a skip-worktree entry.
    const CE_SKIP_WORKTREE: u32 = 1 << 30;

    /// One entry's fields, as git lists them or as the reader decodes them.
    #[derive(Debug, PartialEq, Eq)]
    struct Listed {
        path: Vec<u8>,
        stage: u8,
        mode: u32,
        oid: String,
        ctime: u32,
        mtime: u32,
        ino: u32,
        uid: u32,
        gid: u32,
        size: u32,
        assume_valid: bool,
        skip_worktree: bool,
        intent_to_add: bool,
    }

    fn init(dir: &Path, format: ObjectFormat) -> Repo {
        let repo = Repo::new(dir);
        let format = match format {
            ObjectFormat::Sha1 => "--object-format=sha1",
            ObjectFormat::Sha256 => "--object-format=sha256",
        };
        repo.run_git(&["init", "-q", "--initial-branch=master", format]);
        repo
    }

    fn git_stdout(repo: &Repo, args: &[&str]) -> Vec<u8> {
        let output = repo.try_git(args);
        assert!(
            output.status.success(),
            "git {} failed: {}",
            args.join(" "),
            String::from_utf8_lossy(&output.stderr)
        );
        output.stdout
    }

    fn rev_parse(repo: &Repo, spec: &str) -> String {
        let stdout = git_stdout(repo, &["rev-parse", spec]);
        String::from_utf8(stdout).unwrap().trim_end().to_owned()
    }

    fn index_bytes(repo: &Repo) -> Vec<u8> {
        std::fs::read(repo.path().join(".git/index")).unwrap()
    }

    fn read(repo: &Repo, format: ObjectFormat) -> Index {
        Index::parse(index_bytes(repo), format).unwrap()
    }

    fn hex(oid: &[u8]) -> String {
        oid.iter().fold(String::new(), |mut hex, b| {
            write!(hex, "{b:02x}").unwrap();
            hex
        })
    }

    /// The entries as `git ls-files --stage --debug -z` lists them.
    fn listed_by_git(repo: &Repo) -> Vec<Listed> {
        let stdout = git_stdout(repo, &["ls-files", "--stage", "--debug", "-z"]);
        let mut rest = stdout.as_slice();
        let mut listed = Vec::new();
        while let Some(nul) = memchr::memchr(0, rest) {
            // `<mode> <oid> <stage>\t<path>`, then five lines of stat data.
            let (line, after) = (&rest[..nul], &rest[nul + 1..]);
            let tab = memchr::memchr(b'\t', line).unwrap();
            let head = std::str::from_utf8(&line[..tab]).unwrap();
            let [mode, oid, stage] = head.split(' ').collect::<Vec<_>>()[..] else {
                panic!("unexpected ls-files line {head}");
            };
            let mut lines = after.splitn(6, |&b| b == b'\n');
            let mut stat = HashMap::new();
            for line in lines.by_ref().take(5) {
                for field in std::str::from_utf8(line).unwrap().split('\t') {
                    let (key, value) = field.trim().split_once(": ").unwrap();
                    stat.insert(key.to_owned(), value.to_owned());
                }
            }
            rest = lines.next().unwrap_or_default();
            // Times print as `<seconds>:<nanoseconds>`.
            let number = |key: &str| stat[key].split(':').next().unwrap().parse().unwrap();
            let flags = u32::from_str_radix(&stat["flags"], 16).unwrap();
            listed.push(Listed {
                path: line[tab + 1..].to_vec(),
                stage: stage.parse().unwrap(),
                mode: u32::from_str_radix(mode, 8).unwrap(),
                oid: oid.to_owned(),
                ctime: number("ctime"),
                mtime: number("mtime"),
                ino: number("ino"),
                uid: number("uid"),
                gid: number("gid"),
                size: number("size"),
                assume_valid: flags & CE_VALID != 0,
                skip_worktree: flags & CE_SKIP_WORKTREE != 0,
                intent_to_add: flags & CE_INTENT_TO_ADD != 0,
            });
        }
        listed
    }

    fn listed_by_reader(index: &Index) -> Vec<Listed> {
        index
            .entries()
            .map(|entry| Listed {
                path: entry.path().to_vec(),
                stage: entry.stage(),
                mode: entry.mode(),
                oid: hex(entry.oid()),
                ctime: entry.ctime_secs(),
                mtime: entry.mtime_secs(),
                ino: entry.ino(),
                uid: entry.uid(),
                gid: entry.gid(),
                size: entry.size(),
                assume_valid: entry.assume_valid(),
                skip_worktree: entry.skip_worktree(),
                intent_to_add: entry.intent_to_add(),
            })
            .collect()
    }

    /// A repository whose index holds nested directories, an executable, a
    /// symlink, an empty file, and an unresolved conflict.
    fn fixture(dir: &Path, format: ObjectFormat) -> Repo {
        let repo = init(dir, format);
        repo.write("a", "a\n")
            .write("b/c", "c\n")
            .write("b/d/e", "e\n")
            .write("empty", "")
            .write("conflict", "base\n")
            .add_all();
        // Set in the index alone, so file systems without symlinks or
        // executable bits build the same index.
        let blob = rev_parse(&repo, ":a");
        repo.run_git(&[
            "update-index",
            "--add",
            "--cacheinfo",
            &format!("120000,{blob},link"),
        ]);
        repo.run_git(&["update-index", "--chmod=+x", "b/c"]);
        repo.commit("base");
        repo.branch("side")
            .write("conflict", "side\n")
            .add("conflict")
            .commit("side");
        repo.checkout("master")
            .write("conflict", "master\n")
            .add("conflict")
            .commit("master");
        assert!(!repo.try_git(&["merge", "-q", "side"]).status.success());
        repo
    }

    #[rstest]
    fn reads_every_entry_as_git_lists_it(
        #[values(ObjectFormat::Sha1, ObjectFormat::Sha256)] format: ObjectFormat,
        #[values(2, 3, 4)] version: u32,
    ) {
        let dir = TempDir::new().unwrap();
        let repo = fixture(dir.path(), format);
        repo.run_git(&["update-index", "--assume-unchanged", "a"]);
        // Extended flags take version 3 or later.
        if version >= 3 {
            repo.run_git(&["update-index", "--skip-worktree", "b/d/e"]);
            repo.write("new", "new\n")
                .run_git(&["add", "--intent-to-add", "new"]);
        }
        repo.run_git(&["update-index", "--index-version", &version.to_string()]);
        assert_eq!(be32(&index_bytes(&repo), VERSION_OFFSET), version);

        let index = read(&repo, format);
        let listed = listed_by_git(&repo);
        assert_eq!(listed_by_reader(&index), listed);
        assert!(index.has_conflicts());
        for entry in &listed {
            let found = index.find(&entry.path, entry.stage).unwrap();
            assert_eq!(hex(found.oid()), entry.oid);
            let first = listed.iter().position(|e| e.path == entry.path).unwrap();
            assert_eq!(index.first_at_or_after(&entry.path), first);
        }
        assert!(index.find(b"conflict", 0).is_none());
    }

    #[rstest]
    fn reads_paths_too_long_for_the_length_field(
        #[values(ObjectFormat::Sha1, ObjectFormat::Sha256)] format: ObjectFormat,
        #[values(2, 4)] version: u32,
    ) {
        let dir = TempDir::new().unwrap();
        let repo = init(dir.path(), format);
        repo.write("a", "a\n").add("a");
        let blob = rev_parse(&repo, ":a");
        // Both paths outgrow the flags' length field, and the second shares
        // all but its last byte with the first, which version 4 strips.
        let long = vec!["d".repeat(100); 50].join("/");
        for name in ["y", "z"] {
            let entry = format!("100644,{blob},{long}/{name}");
            repo.run_git(&["update-index", "--add", "--cacheinfo", &entry]);
        }
        repo.run_git(&["update-index", "--index-version", &version.to_string()]);

        let index = read(&repo, format);
        assert!(
            index
                .entries()
                .any(|entry| entry.path().len() > usize::from(NAME_MASK))
        );
        assert_eq!(listed_by_reader(&index), listed_by_git(&repo));
    }

    #[rstest]
    fn reads_the_cache_tree_git_wrote(
        #[values(ObjectFormat::Sha1, ObjectFormat::Sha256)] format: ObjectFormat,
    ) {
        let dir = TempDir::new().unwrap();
        let repo = init(dir.path(), format);
        repo.write("a", "a\n")
            .write("b/c", "c\n")
            .write("b/d/e", "e\n")
            .write("f/g", "g\n")
            .add_all()
            .commit("base");

        let index = read(&repo, format);
        let root = index.cache_tree().unwrap();
        let b = root.child(b"b").unwrap();
        assert_eq!(root.oid().map(hex), Some(rev_parse(&repo, "HEAD:")));
        assert_eq!(b.oid().map(hex), Some(rev_parse(&repo, "HEAD:b")));
        assert_eq!(
            b.child(b"d").unwrap().oid().map(hex),
            Some(rev_parse(&repo, "HEAD:b/d"))
        );
        assert_eq!(
            root.child(b"f").unwrap().oid().map(hex),
            Some(rev_parse(&repo, "HEAD:f"))
        );
        assert!(root.child(b"a").is_none());

        // Staging a change invalidates the directories above it.
        repo.write("b/d/e", "changed\n").add("b/d/e");
        let index = read(&repo, format);
        let root = index.cache_tree().unwrap();
        let b = root.child(b"b").unwrap();
        assert_eq!(root.oid(), None);
        assert_eq!(b.oid(), None);
        assert_eq!(b.child(b"d").unwrap().oid(), None);
        assert_eq!(
            root.child(b"f").unwrap().oid().map(hex),
            Some(rev_parse(&repo, "HEAD:f"))
        );

        // `write-tree` computes the trees again and records them.
        let tree = String::from_utf8(git_stdout(&repo, &["write-tree"])).unwrap();
        let index = read(&repo, format);
        assert_eq!(
            index.cache_tree().unwrap().oid().map(hex),
            Some(tree.trim_end().to_owned())
        );
    }

    #[test]
    fn refuses_a_split_index() {
        let dir = TempDir::new().unwrap();
        let repo = init(dir.path(), ObjectFormat::Sha1);
        repo.write("a", "a\n").add_all().commit("base");
        repo.run_git(&["update-index", "--split-index"]);
        let parsed = Index::parse(index_bytes(&repo), ObjectFormat::Sha1);
        assert!(
            matches!(parsed, Err(IndexError::UnsupportedExtension(signature)) if signature == *b"link")
        );
    }

    #[test]
    fn refuses_a_sparse_index() {
        let dir = TempDir::new().unwrap();
        let repo = init(dir.path(), ObjectFormat::Sha1);
        repo.write("a", "a\n")
            .write("in/b", "b\n")
            .write("out/c", "c\n")
            .add_all()
            .commit("base");
        repo.run_git(&["sparse-checkout", "set", "--cone", "--sparse-index", "in"]);
        let parsed = Index::parse(index_bytes(&repo), ObjectFormat::Sha1);
        assert!(
            matches!(parsed, Err(IndexError::UnsupportedExtension(signature)) if signature == *b"sdir")
        );
    }
}
