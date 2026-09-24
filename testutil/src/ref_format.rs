//! Ref storage formats for fixtures, and conversion of a built fixture between
//! them.

use std::path::PathBuf;

use subspy::git::path_from_bytes;

use crate::Repo;

/// The ref storage a fixture's repositories use.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Default)]
pub enum RefFormat {
    #[default]
    Files,
    Reftable,
}

impl std::fmt::Display for RefFormat {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        let name = match self {
            Self::Files => "files",
            Self::Reftable => "reftable",
        };
        write!(f, "{name}")
    }
}

impl Repo {
    /// The ref storage this repository uses.
    pub fn ref_format(&self) -> RefFormat {
        // git records a format other than files in the repository config.
        // Reading it there keeps the files half working on git older than 2.45,
        // which lacks `rev-parse --show-ref-format`.
        let output = self.try_git(&["config", "--local", "--get", "extensions.refStorage"]);
        match (output.status.code(), output.stdout.trim_ascii()) {
            (Some(1), _) | (Some(0), b"files") => RefFormat::Files,
            (Some(0), b"reftable") => RefFormat::Reftable,
            (code, value) => panic!(
                "unexpected extensions.refStorage in {} (exit {code:?}): {}",
                self.path().display(),
                String::from_utf8_lossy(value)
            ),
        }
    }

    /// Migrates this repository, and every submodule checked out beneath it,
    /// to `ref_format`. A repository that already uses it is left as is.
    pub fn migrate_refs(&self, ref_format: RefFormat) {
        for submodule in self.checked_out_submodules() {
            submodule.migrate_refs(ref_format);
        }
        if self.ref_format() != ref_format {
            let flag = format!("--ref-format={ref_format}");
            self.run_git(&["refs", "migrate", &flag]);
        }
    }

    /// The submodules checked out at this repository's index gitlinks.
    fn checked_out_submodules(&self) -> Vec<Self> {
        let output = self.try_git(&["ls-files", "--stage", "-z"]);
        assert!(
            output.status.success(),
            "git ls-files failed in {}: {}",
            self.path().display(),
            String::from_utf8_lossy(&output.stderr)
        );
        let mut workdirs: Vec<PathBuf> = Vec::new();
        // Each record is `<mode> <oid> <stage>\t<path>`.
        for record in output.stdout.split(|&b| b == 0) {
            let Some(rest) = record.strip_prefix(b"160000 ") else {
                continue;
            };
            let Some(tab) = rest.iter().position(|&b| b == b'\t') else {
                continue;
            };
            let path = path_from_bytes(&rest[tab + 1..]).unwrap();
            let workdir = self.path().join(path);
            if workdirs.last() != Some(&workdir) && workdir.join(".git").exists() {
                workdirs.push(workdir);
            }
        }
        workdirs.iter().map(|workdir| Self::new(workdir)).collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::HarnessBuilder;

    fn get_ref_format(repo: &Repo) -> String {
        let output = repo.try_git(&["rev-parse", "--show-ref-format"]);
        String::from_utf8(output.stdout).unwrap().trim().to_string()
    }

    fn porcelain_status(repo: &Repo) -> Vec<u8> {
        repo.try_git(&["status", "--porcelain=v2", "--branch"])
            .stdout
    }

    #[test]
    fn migration_round_trips_every_submodule_and_keeps_status() {
        let harness = HarnessBuilder::new()
            .no_server()
            .submodule("sub_a")
            .submodule("libs/sub_b")
            .build();
        harness.submodule("sub_a").write("untracked.txt", "x\n");
        harness
            .submodule("libs/sub_b")
            .write("README.md", "changed\n");
        let before = porcelain_status(harness.root());

        let repos = [
            harness.root(),
            harness.submodule("sub_a"),
            harness.submodule("libs/sub_b"),
        ];
        for ref_format in [RefFormat::Reftable, RefFormat::Files] {
            harness.root().migrate_refs(ref_format);
            for repo in repos {
                assert_eq!(
                    get_ref_format(repo),
                    ref_format.to_string(),
                    "{} was not migrated",
                    repo.path().display()
                );
            }
            assert_eq!(
                porcelain_status(harness.root()),
                before,
                "status changed on migrating to {ref_format}"
            );
        }
    }

    #[test]
    fn submodule_ref_format_reaches_added_submodules_and_skips_the_root() {
        for (root_format, submodule_format) in [
            (RefFormat::Files, RefFormat::Reftable),
            (RefFormat::Reftable, RefFormat::Files),
        ] {
            let mut harness = HarnessBuilder::new()
                .no_server()
                .ref_format(root_format)
                .submodule_ref_format(submodule_format)
                .submodule("sub_a")
                .build();
            // git clones a new submodule in the default ref format, so it follows
            // `submodule_ref_format` as well.
            harness.add_submodule("sub_b");

            assert_eq!(get_ref_format(harness.root()), root_format.to_string());
            for name in ["sub_a", "sub_b"] {
                assert_eq!(
                    get_ref_format(harness.submodule(name)),
                    submodule_format.to_string(),
                    "{name} under a {root_format} root"
                );
            }
        }
    }
}
