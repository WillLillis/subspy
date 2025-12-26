use std::{
    collections::BTreeMap,
    io::{BufRead as _, BufReader, Write},
    path::Path,
    sync::{LazyLock, Mutex},
    time::Duration,
};

use anstyle::AnsiColor;
use git2::{Repository, Submodule};
use indicatif::{ProgressBar, ProgressStyle};
use interprocess::local_socket::{ListenerOptions, Stream, traits::ListenerExt as _};
use log::{error, info, trace};
use notify::{
    EventKind,
    event::{AccessKind, AccessMode, RemoveKind},
};
use notify_debouncer_full::new_debouncer;

use crate::{
    StatusSummary,
    connection::{BINCODE_CFG, ipc_name},
    paint,
    watch::WatchResult,
};

static SUBMOD_STATUSES: LazyLock<Mutex<BTreeMap<String, StatusSummary>>> =
    LazyLock::new(|| Mutex::new(BTreeMap::new()));

type WatcherList = Vec<(
    String,
    crossbeam_channel::Receiver<notify_debouncer_full::DebounceEventResult>,
    notify_debouncer_full::Debouncer<
        notify::RecommendedWatcher,
        notify_debouncer_full::RecommendedCache,
    >,
)>;

fn place_watch(
    full_path: &Path,
    rel_path: String,
    watchers: &mut WatcherList,
    watch_mode: notify::RecursiveMode,
) -> WatchResult<()> {
    let (tx, rx) = crossbeam_channel::unbounded();
    let log_full_path = full_path.to_path_buf();
    let mut debouncer = new_debouncer(
        Duration::from_secs(1),
        None,
        move |res: notify_debouncer_full::DebounceEventResult| {
            if let Err(e) = tx.send(res) {
                error!(
                    "Watcher for {} failed to send -- {e}",
                    log_full_path.display()
                );
            }
        },
    )?;
    debouncer.watch(full_path, watch_mode)?;
    info!("Placed watch: {}", full_path.display());
    watchers.push((rel_path, rx, debouncer));

    Ok(())
}

fn stop_watchers(watchers: WatcherList) {
    for (_, _, w) in watchers {
        w.stop();
    }
}

fn populate_status_map(
    root_dir: &Path,
    repo: &Repository,
    submodules: &[Submodule],
    watchers: &mut WatcherList,
    display_progress: bool,
) -> WatchResult<()> {
    info!("Indexing project at {}", root_dir.display());
    let progress_bar = if display_progress {
        Some(
            ProgressBar::new(submodules.len() as u64)
                .with_style(
                    ProgressStyle::with_template("{prefix:.cyan.bold}: {wide_bar:} {pos}/{len}")
                        .unwrap(),
                )
                .with_prefix("Indexing submodules"),
        )
    } else {
        None
    };
    let mut status_guard = SUBMOD_STATUSES.lock().expect("Mutex poisoned");
    status_guard.clear();
    for submod in submodules {
        let sub_start = std::time::Instant::now();
        let rel_path = submod.path();
        let mut full_path = root_dir.to_path_buf();
        full_path.push(submod.path());

        let status =
            repo.submodule_status(submod.path().to_str().unwrap(), git2::SubmoduleIgnore::None)?;
        let converted_status: StatusSummary = status.into();
        status_guard.insert(rel_path.to_string_lossy().to_string(), converted_status);
        place_watch(
            &full_path,
            rel_path.to_string_lossy().to_string(),
            watchers,
            notify::RecursiveMode::Recursive,
        )?;
        if let Some(ref pb) = progress_bar {
            pb.inc(1);
        }
        info!(
            "Indexed {} ({:?} -> {:?}) in {}ms",
            full_path.display(),
            status,
            converted_status,
            sub_start.elapsed().as_millis(),
        );
    }
    drop(status_guard);
    if let Some(ref pb) = progress_bar {
        pb.finish();
        println!("Indexing complete. If you haven't already, send this process to the background.");
    }

    Ok(())
}

/// Runs the watch server for the repository at `root_dir`
///
/// # Errors
///
/// Returns `Err` if communication with a client or interacting with the repository fails
///
/// # Panics
///
/// Panics if the `SUBMOD_STATUSES` mutex is poisoned.
#[allow(clippy::too_many_lines)]
pub fn watch(root_dir: &Path) -> WatchResult<()> {
    let path = root_dir.to_path_buf();

    let name = ipc_name(&path)?;
    let opts = ListenerOptions::new().name(name.clone());
    let listener = match opts.create_sync() {
        Err(e) if e.kind() == std::io::ErrorKind::AddrInUse => {
            eprintln!(
                "{}: could not start watch server because the socket file is occupied. Is there already a watcher placed on {}?",
                paint(Some(AnsiColor::Red), "Error"),
                root_dir.display()
            );
            Err(e)?
        }
        x => x?,
    };
    std::thread::spawn(move || {
        fn handle_error(conn: std::io::Result<Stream>) -> Option<Stream> {
            match conn {
                Ok(c) => Some(c),
                Err(e) => {
                    error!("Incoming connection failed: {e}");
                    None
                }
            }
        }

        let mut buffer = String::with_capacity(1024);
        for conn in listener.incoming().filter_map(handle_error) {
            let mut conn = BufReader::new(conn);
            info!("New client connection to server for {}", path.display());

            conn.read_line(&mut buffer)?;

            let guard = SUBMOD_STATUSES.lock().expect("Mutex poisoned");
            let mut status_out = Vec::with_capacity(guard.len());
            for (submod_path, status) in guard.iter().filter(|(_, st)| **st != StatusSummary::CLEAN)
            {
                status_out.push((submod_path.clone(), *status));
            }
            drop(guard);
            let serialized = bincode::encode_to_vec(&status_out, BINCODE_CFG).unwrap();
            conn.get_mut().write_all(&serialized).unwrap();
            buffer.clear();
            trace!("Sent: {status_out:?}");
        }

        std::io::Result::Ok(())
    });

    let repo = Repository::open(root_dir)?;
    let submodules = repo.submodules()?;
    let mut gitmodules_path = root_dir.to_path_buf();
    gitmodules_path.push(".gitmodules");
    let mut dot_git_dir = root_dir.to_path_buf();
    dot_git_dir.push(".git");

    let mut first_index = true;
    let mut do_watch = true;
    while do_watch {
        let mut watchers = Vec::with_capacity(submodules.len() + 2);

        // Place a watch on the project's root directory,
        place_watch(
            root_dir,
            ".gitmodules".to_string(),
            &mut watchers,
            notify::RecursiveMode::NonRecursive,
        )?;
        // And the `.git` directory
        place_watch(
            &dot_git_dir,
            ".git".to_string(),
            &mut watchers,
            notify::RecursiveMode::Recursive,
        )?;

        populate_status_map(root_dir, &repo, &submodules, &mut watchers, first_index)?;
        first_index = false;

        let mut sel = crossbeam_channel::Select::new();
        for (_path, rx, _w) in &watchers {
            sel.recv(rx); // Register each recv op
        }

        'inner: loop {
            let oper = sel.select(); // Blocks until any ready
            let index = oper.index(); // Which rx fired

            match oper.recv(&watchers[index].1) {
                Ok(Ok(events)) => {
                    for event in events {
                        if event.kind == EventKind::Access(AccessKind::Close(AccessMode::Write))
                            || event.kind == EventKind::Remove(RemoveKind::Any)
                        {
                            let rel_path = watchers[index].0.as_str();
                            // TODO: Check for reindex sentinel file here, add re-index command
                            // that just creates and deletes the file. *Maybe* send reindex updates
                            // over ipc back to display to user. Same approach for shutdown
                            if rel_path.eq(".gitmodules") || rel_path.eq(".git") {
                                if event.paths.iter().any(|p| {
                                    p.starts_with(&dot_git_dir) || p.eq(gitmodules_path.as_path())
                                }) {
                                    // Who knows what just happened, re-index the entire repo
                                    break 'inner;
                                }
                                continue;
                            }
                            let submod_status = match repo
                                .submodule_status(rel_path, git2::SubmoduleIgnore::None)
                            {
                                Ok(st) => st,
                                Err(e) => {
                                    error!(
                                        "Failed to get submodule status for path: {rel_path} -- {e}"
                                    );
                                    continue;
                                }
                            };
                            let mut guard = SUBMOD_STATUSES.lock().expect("Mutex poisoned");
                            guard
                                .entry(rel_path.to_string())
                                .and_modify(|st| *st = submod_status.into())
                                .or_insert_with(|| submod_status.into());
                            drop(guard);
                            // Any events for this receiver will refer to the same submodule. Once
                            // we've triggered an update, any more will be redundant.
                            break;
                        }
                    }
                }
                Ok(Err(e)) => {
                    error!("Watcher error for submodule {}: {:?}", watchers[index].0, e);
                }
                Err(e) => {
                    error!(
                        "Fatal error, failed to receive for watcher {} -- {e}",
                        watchers[index].0
                    );
                    // Channel closed, exit loop
                    do_watch = false;
                    break 'inner;
                }
            }
        }
        stop_watchers(watchers);
    }

    Ok(())
}
