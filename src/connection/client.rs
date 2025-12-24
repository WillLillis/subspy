use std::{
    io::{BufReader, Read as _, Write as _},
    path::Path,
};

use interprocess::local_socket::{Stream, traits::Stream as _};

use crate::{
    StatusSummary,
    connection::{BINCODE_CFG, ipc_name},
};

/// Requests the statuses of the submodules within `path` from the watch server
///
/// # Errors
///
/// Returns error if the ipc channel cannot be created, or communication over said channel fails
///
/// # Panics
///
/// Panics if a malformed response from the watch server is received
pub fn get_statuses(path: &Path) -> std::io::Result<Vec<(String, StatusSummary)>> {
    let name = ipc_name(path)?;

    let conn = Stream::connect(name)?;
    let mut conn = BufReader::new(conn);
    conn.get_mut().write_all(b"status\n")?;

    // TODO: Get some impirical data on the actual buffer size we need
    let mut buffer = Vec::with_capacity(1024);
    conn.read_to_end(&mut buffer)?;

    let (statuses, _): (Vec<(String, StatusSummary)>, usize) =
        bincode::borrow_decode_from_slice(&buffer, BINCODE_CFG).unwrap();

    Ok(statuses)
}
