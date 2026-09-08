use std::{
    io::BufReader,
    sync::{Arc, Condvar, Mutex, atomic::Ordering},
    time::Duration,
};

use log::error;

use crate::connection::{
    DebugState, IpcStream, ServerMessage, encode_and_write, ipc_socket_path, try_lock_for,
    watch_server::{InFlightTracker, WatchServer},
};

const DEBUG_LOCK_TIMEOUT: Duration = Duration::from_secs(5);

impl WatchServer {
    /// Gathers a snapshot of the server's internal state for diagnostic purposes.
    fn gather_debug_state(
        &self,
        in_flight: Option<&(Mutex<InFlightTracker>, Condvar)>,
    ) -> DebugState {
        let submodules: Vec<(String, String)> = self
            .submodules
            .iter()
            .map(|s| {
                (
                    s.relative_path.clone(),
                    s.workdir_path.display().to_string(),
                )
            })
            .collect();
        let tripwires: Vec<String> = self
            .tripwires
            .iter()
            .map(|p| p.display().to_string())
            .collect();

        let submodule_statuses = try_lock_for(&self.submod_statuses, DEBUG_LOCK_TIMEOUT)
            .map(|guard| guard.iter().map(|(k, v)| (k.clone(), *v)).collect());

        let in_flight_tasks = in_flight.and_then(|in_flight| {
            try_lock_for(&in_flight.0, DEBUG_LOCK_TIMEOUT).map(|guard| {
                guard
                    .tasks
                    .iter()
                    .map(|(idx, state)| {
                        let rel_path = self
                            .submodules
                            .get(*idx)
                            .map_or("(unknown)", |s| s.relative_path.as_str());
                        let cancelled = state.cancel.load(Ordering::Relaxed);
                        let state_str = match (state.dirty, cancelled) {
                            (false, false) => "active",
                            (false, true) => "active (cancelling)",
                            (true, false) => "dirty",
                            (true, true) => "dirty (cancelling)",
                        };
                        (rel_path.to_owned(), state_str.to_owned())
                    })
                    .collect()
            })
        });

        let progress_subscribers = try_lock_for(&self.progress_subscribers, DEBUG_LOCK_TIMEOUT)
            .map(|guard| {
                guard
                    .iter()
                    .map(|(pid, pending)| (*pid, pending.map(|p| (p.curr, p.total))))
                    .collect()
            });

        DebugState {
            server_pid: std::process::id(),
            rayon_threads: rayon::current_num_threads() as u32,
            progress_subscribers,
            git_watch_pending: self.git_watch.as_ref().map(|w| w.receiver.len() as u32),
            tree_watch_pending: self.tree_watch.as_ref().map(|w| w.receiver.len() as u32),
            submodules,
            root_path: self.root_path.display().to_string(),
            socket_name: ipc_socket_path(&self.root_path)
                .into_string()
                .unwrap_or_else(|name| name.to_string_lossy().into_owned()),
            submodule_statuses,
            in_flight: in_flight_tasks,
            last_watcher_error: self.last_watcher_error.clone(),
            tripwires,
        }
    }

    /// Handles a debug request from a client by serializing and sending the current server state.
    #[cold]
    pub(super) fn handle_debug_request(
        &self,
        conn: &mut BufReader<IpcStream>,
        in_flight: Option<&Arc<(Mutex<InFlightTracker>, Condvar)>>,
    ) {
        let state = self.gather_debug_state(in_flight.map(Arc::as_ref));
        let msg = ServerMessage::DebugInfo(Box::new(state));
        let mut buf = Vec::with_capacity(1024);
        if let Err(e) = encode_and_write(conn, msg, &mut buf) {
            error!("Failed to send debug state: {e}");
        }
    }
}
