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
    fn gather_debug_state(&self, in_flight: &(Mutex<InFlightTracker>, Condvar)) -> DebugState {
        let watched_paths: Vec<(String, String, u32)> = self
            .watchers
            .iter()
            .map(|w| {
                (
                    w.relative_path.clone(),
                    w.watch_path.display().to_string(),
                    w.receiver.len() as u32,
                )
            })
            .collect();
        let tripwires: Vec<(String, u32)> = self
            .tripwires
            .iter()
            .map(|w| (w.watch_path.display().to_string(), w.receiver.len() as u32))
            .collect();

        let skip_set: Vec<String> = self
            .skip_set
            .iter()
            .filter_map(|idx| self.watchers.get(idx).map(|w| w.relative_path.clone()))
            .collect();

        let submodule_statuses = try_lock_for(&self.submod_statuses, DEBUG_LOCK_TIMEOUT)
            .map(|guard| guard.iter().map(|(k, v)| (k.clone(), *v)).collect());

        let in_flight_tasks = try_lock_for(&in_flight.0, DEBUG_LOCK_TIMEOUT).map(|guard| {
            guard
                .tasks
                .iter()
                .map(|(idx, state)| {
                    let rel_path = self
                        .watchers
                        .get(*idx)
                        .map_or("(unknown)", |w| w.relative_path.as_str());
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
        });

        let progress_queues = try_lock_for(&self.progress_queue, DEBUG_LOCK_TIMEOUT).map(|guard| {
            guard
                .iter()
                .map(|(pid, queue)| {
                    let updates: Vec<(u32, u32)> =
                        queue.iter().map(|p| (p.curr, p.total)).collect();
                    (*pid, updates)
                })
                .collect()
        });

        let progress_subscribers = try_lock_for(&self.progress_subscribers, DEBUG_LOCK_TIMEOUT)
            .map(|guard| guard.iter().copied().collect());

        DebugState {
            server_pid: std::process::id(),
            rayon_threads: rayon::current_num_threads() as u32,
            progress_subscribers,
            watcher_count: self.watchers.len() as u32,
            watched_paths,
            skip_set,
            root_rebasing: self.root_rebasing,
            root_path: self.root_path.display().to_string(),
            socket_name: ipc_socket_path(&self.root_path),
            submodule_statuses,
            in_flight: in_flight_tasks,
            progress_queues,
            last_watcher_error: self.last_watcher_error.clone(),
            tripwires,
        }
    }

    /// Handles a debug request from a client by serializing and sending the current server state.
    #[cold]
    pub(super) fn handle_debug_request(
        &self,
        conn: &mut BufReader<IpcStream>,
        in_flight: &Arc<(Mutex<InFlightTracker>, Condvar)>,
    ) {
        let state = self.gather_debug_state(in_flight);
        let msg = ServerMessage::DebugInfo(Box::new(state));
        let mut buf = Vec::with_capacity(1024);
        if let Err(e) = encode_and_write(conn, msg, &mut buf) {
            error!("Failed to send debug state -- {e}");
        }
    }
}
