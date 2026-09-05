//! Discovery of Subspy servers in the platform's socket namespace.

use std::ffi::{OsStr, OsString};

use super::transport::{SOCKET_NAME_PREFIX, SOCKET_NAME_SUFFIX};

/// Returns the connection names of every discoverable Subspy IPC endpoint.
///
/// Discovery is a snapshot: endpoints may disappear before a caller connects.
///
/// # Errors
///
/// Returns an I/O error if the platform's socket namespace cannot be inspected.
pub fn discover_ipc_endpoints() -> std::io::Result<Vec<OsString>> {
    let mut endpoints = discover_endpoints()?;
    endpoints.sort_unstable();
    Ok(endpoints)
}

#[cfg(any(target_os = "linux", target_os = "android"))]
fn discover_endpoints() -> std::io::Result<Vec<OsString>> {
    let table = std::fs::read("/proc/net/unix")?;
    Ok(parse_abstract_endpoints(&table))
}

/// Scans the temp directory that [`ipc_socket_path`](super::ipc_socket_path) binds
/// into, treating a missing directory as empty.
#[cfg(not(any(target_os = "linux", target_os = "android")))]
fn discover_endpoints() -> std::io::Result<Vec<OsString>> {
    let entries = match std::fs::read_dir(std::env::temp_dir()) {
        Ok(entries) => entries,
        Err(error) if error.kind() == std::io::ErrorKind::NotFound => return Ok(Vec::new()),
        Err(error) => return Err(error),
    };

    Ok(entries
        .flatten()
        .filter(|entry| is_socket_name(&entry.file_name()) && is_socket_file(entry))
        .map(|entry| entry.path().into_os_string())
        .collect())
}

/// `uds_windows` sockets are indistinguishable from regular files, so the name is
/// all Windows has to go on.
#[cfg(target_os = "windows")]
const fn is_socket_file(_entry: &std::fs::DirEntry) -> bool {
    true
}

#[cfg(all(unix, not(any(target_os = "linux", target_os = "android"))))]
fn is_socket_file(entry: &std::fs::DirEntry) -> bool {
    use std::os::unix::fs::FileTypeExt as _;

    entry.file_type().is_ok_and(|ty| ty.is_socket())
}

/// Parses listening abstract-namespace sockets out of `/proc/net/unix`, whose
/// whitespace-separated columns are `Num RefCount Protocol Flags Type St Inode Path`.
#[cfg(any(target_os = "linux", target_os = "android"))]
fn parse_abstract_endpoints(table: &[u8]) -> Vec<OsString> {
    /// `SO_ACCEPTCON`: the socket is listening.
    const LISTENING: &str = "00010000";
    /// `SOCK_STREAM`
    const STREAM: &str = "0001";
    /// `SS_UNCONNECTED`:  what a listener reports.
    const UNCONNECTED: &str = "01";

    table
        .split(|byte| *byte == b'\n')
        .skip(1)
        .filter_map(|line| {
            let line = std::str::from_utf8(line).ok()?;
            let mut fields = line.split_ascii_whitespace().skip(3);
            let (flags, socket_type, state) = (fields.next()?, fields.next()?, fields.next()?);
            let name = fields.nth(1)?.strip_prefix('@')?;
            (flags == LISTENING
                && socket_type == STREAM
                && state == UNCONNECTED
                && is_socket_name(OsStr::new(name)))
            .then(|| OsString::from(name))
        })
        .collect()
}

fn is_socket_name(name: &OsStr) -> bool {
    name.to_str()
        .and_then(|name| {
            name.strip_prefix(SOCKET_NAME_PREFIX)?
                .strip_suffix(SOCKET_NAME_SUFFIX)
        })
        .is_some_and(|hash| {
            hash.bytes().all(|byte| byte.is_ascii_digit()) && hash.parse::<u64>().is_ok()
        })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn accepts_only_generated_socket_names() {
        assert!(is_socket_name(OsStr::new("subspy-0.sock")));
        assert!(is_socket_name(OsStr::new(&format!(
            "subspy-{}.sock",
            u64::MAX
        ))));

        for name in [
            "0.sock",
            "subspy-.sock",
            "subspy-+1.sock",
            "subspy--1.sock",
            "subspy-1",
            "subspy-1.sock.bak",
            "prefix-subspy-1.sock",
            "subspy-1x.sock",
            "subspy-18446744073709551616.sock",
        ] {
            assert!(!is_socket_name(OsStr::new(name)), "{name}");
        }
    }

    #[cfg(any(target_os = "linux", target_os = "android"))]
    #[test]
    fn parses_only_listening_abstract_stream_sockets() {
        let table = b"\
Num       RefCount Protocol Flags    Type St Inode Path
0001: 00000002 00000000 00010000 0001 01 10 @subspy-7.sock
0002: 00000002 00000000 00010000 0002 01 11 @subspy-8.sock
0003: 00000002 00000000 00010000 0001 01 12 /tmp/subspy-9.sock
0004: 00000002 00000000 00010000 0001 01 13 @other-10.sock
0005: 00000002 00000000 00000000 0001 01 14 @subspy-11.sock
0006: 00000002 00000000 00010000 0001 03 15 @subspy-12.sock
0007: 00000002 00000000 00010000 0001 01 16 @other-\xff.sock
0008: 00000002 00000000 00010000 0001 01 17 @subspy-13.sock
0009: malformed
";
        pretty_assertions::assert_eq!(
            parse_abstract_endpoints(table),
            [
                OsString::from("subspy-7.sock"),
                OsString::from("subspy-13.sock")
            ]
        );
    }
}
