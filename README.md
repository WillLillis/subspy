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
  reindex   Reindex a watch server [aliases: r, re]
  shutdown  Shutdown a watch server [aliases: sh, stop]
  status    Display the status of a watched git project [aliases: s, st]
  watch     Start a watch server on a git project [aliases: w, wa]

Options:
  -h, --help  Print help

~/very_large_project/ > subspy watch --daemon # Or start normally in another terminal w/o --daemon
# Work on your project as normal
~/very_large_project/ > subspy status
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
repo with >200 submodules, running on Windows 11 with git bash. The `subspy` measurement was taken after the initial `watch`
indexing step completed. The `git` measurement was taken after already running `git status` to "preheat" any caching mechanisms
git may have in place.

```sh
~/very_large_project/ > time subspy status
real    0m0.099s
user    0m0.000s
sys     0m0.000s

~/very_large_project/ > time git status
real    0m11.770s
user    0m0.015s
sys     0m0.000s
```

#### Future Improvements

- [ ] Tests
- [ ] crates.io releases if desired

#### Known Issues
