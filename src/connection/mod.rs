use std::{hash::Hash as _, hash::Hasher as _, path::Path};

use interprocess::local_socket::{
    GenericFilePath, GenericNamespaced, Name, NameType as _, ToFsName as _, ToNsName as _,
};

pub mod client;
pub mod watch_server;

pub const BINCODE_CFG: bincode::config::Configuration = bincode::config::standard().with_no_limit();

/// Returns the `interprocess::local_socket::name::Name` used to communicate between
/// the watch server and request clients for a given git project at `path`.
///
/// # Errors
///
/// Returns `std::io::Error` if socket name isn't supported by the given platform
pub fn ipc_name(path: &Path) -> std::io::Result<Name<'_>> {
    let mut hasher = std::hash::DefaultHasher::new();
    path.hash(&mut hasher);
    let hash = hasher.finish();
    let base_name = hash.to_string();
    if GenericNamespaced::is_supported() {
        format!("{base_name}.sock").to_ns_name::<GenericNamespaced>()
    } else {
        format!("/tmp/{base_name}.sock").to_fs_name::<GenericFilePath>()
    }
}
