# SubSpy

A faster `git status` when working in a repository with many submodules.

### The Problem

Running `git status` at the top level of a respository with many submodules can take minutes, a flow state-breaking pause!
This problem is exacerbated on Windows, which is hindered by Windows Defender as wel as an inefficient [lstat implementation](https://git-scm.com/docs/git-update-index#_using_assume_unchanged_bit).

There are a few potential workarounds you should try before using this tool, including 

- Running `git gc`
- Set `ignore = dirty` for the relevant submodules in your `.gitmodules` file
- Don't use submodules ;)

### The Solution

SubSpy provides a solution to this issue by placing recursive filesystem watches on your `.git` folder, `.gitmodules` file,
and all submodule directories. The status for all submodules is cached by an initial indexing operation, and updated any time
a change is detected in one of these locations.

### Usage

```sh
~/very_large_project/ > subspy watch # This process can be sent to the background
# Work on your project as normal
~/very_large_project/ > subspy status
```

#### Future Improvements

- [ ] Add a command to force the watcher to re-index
- [ ] Add a command to shutdown the watcher
- [ ] Support some of `git status`'s flags for the `subspy status` command if reasonable
