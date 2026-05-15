//! Output-format verification tests. Each submodule exercises a specific
//! renderer (long / porcelain v1 / porcelain v2 / short) and asserts its
//! output against an external reference - either a committed snapshot
//! (long, short) or a live `git status` invocation (porcelain).

mod fixtures;
mod long;
mod porcelain;
mod short;
