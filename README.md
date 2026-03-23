# SubSpy

A faster `git status` when working in repositories with many submodules.

### The Problem

Running `git status` at the top level of a repository with many submodules can take tens of seconds to minutes. This performance
issue is amplified on Windows, which is hindered by Windows Defender as well as an inefficient [lstat implementation](https://git-scm.com/docs/git-update-index#_using_assume_unchanged_bit).

There are a few potential workarounds you should try before using this tool, including 

- Running `git gc`
- Set `ignore = dirty` as needed in your `.gitmodules` file (Usually unacceptable for anything besides vendored dependencies)
- Don't use submodules ;)

### The Solution

SubSpy provides a solution to this issue by placing recursive filesystem watches on your repository's `.git` folder, `.gitmodules`
file, and all submodule directories. The status for all submodules is cached by an initial indexing operation and updated
any time a change is detected in one of these locations. For sufficiently many submodules, `subspy status` is usually
100-300x faster than `git status` on Windows, and 20-40x faster on Linux.

### Usage

```sh
~/very_large_project/ > subspy --help
Usage: subspy <COMMAND>

Commands:
  start    Start a watch server on a git project [aliases: watch, w]
  status   Display the status of a watched git project [aliases: st, s]
  stop     Shutdown a watch server
  reindex  Reindex a watch server [aliases: re, r]
  debug    Dump the internal state of the watch server [aliases: dbg, d]
  list     List submodule metadata [aliases: ls, l]
  prompt   Submodule status summary for shell prompt integration

Options:
  -h, --help  Print help

~/very_large_project/ > subspy status # spawns a watch server if needed
-- top level status here --
~/very_large_project/ > subspy status some/subdirectory/
-- other status here --
~/very_large_project/ > subspy stop # Shutdown the watch server
```

#### Shell Prompt Integration

The `prompt` subcommand outputs submodule status counts for use in shell prompts. It connects to a running watch server
and returns immediately. If no server is running, it spawns one in the background and produces no output until the next
invocation.

The default output is space-separated fields: `<dirty> <staged> <new_commits> <clean> <total>`. A custom format string can
be provided with `-f`:

```sh
# Bash / Zsh
subspy_prompt() {
  local s
  s=$(subspy prompt 2>/dev/null) && [ -n "$s" ] && echo " [$s]"
}
PS1='...\$(subspy_prompt)...'

# With a custom format
subspy_prompt() {
  local s
  s=$(subspy prompt -f '{dirty}!{new_commits}↑' 2>/dev/null) && [ -n "$s" ] && echo " $s"
}
```

For [Starship](https://starship.rs), use a [custom command](https://starship.rs/config/#custom-commands):

```toml
[custom.subspy]
command = "subspy prompt -f '{dirty}!{staged}+{new_commits}↑'"
when = "subspy prompt -f '{dirty}!{staged}+{new_commits}↑'"
format = "[$output]($style) "
```

### Installation

Installing subspy requires the [Rust toolchain](https://rust-lang.org/tools/install/).
Note that the project's current Minimum Supported Rust Version (MSRV) is 1.87.0.

```sh
> git clone https://github.com/WillLillis/subspy
> cd subspy
> cargo install --path . --locked
```

#### Outrageous Anecdotal Performance Claims

For both of the following data points, the `subspy` measurement was taken twice and both times are shown. The first
measures the time to start the watch server, connect to it, and display the status. The second measures the time to connect
to the existing server and display the status. The `git` measurement was taken after already running `git status` to "preheat"
any caching mechanisms git may have in place. Note that making changes within or performing git operations on a repository
may increase the runtime of the next `git status` invocation, while `subspy status`'s should remain constant.

- Windows:

Subspy is most useful on Windows, where git is the slowest. Here's a comparison between `subspy status` and `git status`
on a private repo with >200 submodules, running on Windows 11 with git bash. Note that spawning a process that immediately
exits already takes ~80ms on the machine this measurement was performed on.

```sh
~/very_large_project/ > time subspy status # Spawns a new watch server
real    0m0.745s
user    0m0.000s
sys     0m0.000s

~/very_large_project/ > time subspy status # Connects to previously spawned server
real    0m0.117s
user    0m0.000s
sys     0m0.000s

~/very_large_project/ > time git status
real    0m15.667s
user    0m0.015s
sys     0m0.000s
```

- Linux:

Git's performance is typically acceptable on Linux platforms. Testing on [boost](https://github.com/boostorg/boost), we
see a much smaller performance gain:

```sh
~/boost/ > time subspy status # Spawns a new watch server
subspy status  0.01s user 0.00s system 3% cpu 0.375 total

~/boost/ > time subspy status # Connects to previously spawned server
subspy status  0.01s user 0.00s system 97% cpu 0.012 total

~/boost/ > time git status
git st  0.07s user 0.21s system 104% cpu 0.264 total
```

#### Limitations

- Watch servers for nested submodules (submodules which contain submodules of their own) is not supported. `subspy` must
be run from the top-level of the repository.
- On Linux, each watch server consumes inotify watches. For very large repositories or many concurrent servers, you may
need to increase the system limit (e.g. `sudo sysctl fs.inotify.max_user_watches=<value>`).

#### Future Improvements

- [ ] crates.io releases if desired
