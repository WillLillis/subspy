# SubSpy

A faster `git status` when working in repositories with many submodules.

### The Problem

Running `git status` at the top level of a repository with many submodules can take minutes, a flow state-breaking pause!
This problem is exacerbated on Windows, which is hindered by Windows Defender as well as an inefficient [lstat implementation](https://git-scm.com/docs/git-update-index#_using_assume_unchanged_bit).

There are a few potential workarounds you should try before using this tool, including 

- Running `git gc`
- Set `ignore = dirty` as needed in your `.gitmodules` file (Usually unacceptable for anything besides vendored dependencies)
- Don't use submodules ;)

### The Solution

SubSpy provides a solution to this issue by placing recursive filesystem watches on your repository's `.git` folder, `.gitmodules`
file, and all submodule directories. The status for all submodules is cached by an initial indexing operation and updated
any time a change is detected in one of these locations. For sufficiently many submodules, `subspy status` is usually
100-200x faster than `git status`.

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

Options:
  -h, --help  Print help

~/very_large_project/ > subspy status # spawns a watch server if needed
-- top level status here --
~/very_large_project/ > subspy status some/subdirectory/
-- other status here --
~/very_large_project/ > subspy stop # Shutdown the watch server
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

I developed this tool to remove an annoyance at work. Here's a comparison between `subspy status` and `git status` on a
repo with >200 submodules, running on Windows 11 with git bash. The `subspy` measurement was taken twice and both times
are shown. The first measures the time to start the watch server, connect to it, and display the status. The second connects
to the existing server and display the status.  The `git` measurement was taken after already running `git status` to "preheat"
any caching mechanisms git may have in place. Note that making changes to a repository may increase the runtime of the next
`git status` invocation, while `subspy status`'s should remain constant.

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

#### Future Improvements

- [ ] crates.io releases if desired

#### Known Issues
