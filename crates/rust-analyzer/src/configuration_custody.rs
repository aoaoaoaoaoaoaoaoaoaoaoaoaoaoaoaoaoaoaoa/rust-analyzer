//! Finite filesystem witnesses attached to normal project-loading generations.
//!
//! Inputs are assumed stable throughout each load. Endpoint agreement cannot
//! detect an edit followed by restoration. Build/proc-macro outputs are the
//! loaded configuration, not evidence that arbitrary external inputs were reread.

use std::{
    collections::{BTreeMap, BTreeSet},
    fs,
    hash::{Hash, Hasher},
    io::Read,
};

use anyhow::{Context, ensure};
use paths::Utf8Path;
use project_model::{CargoConfig, ProjectManifest, ProjectWorkspace, ProjectWorkspaceKind};
use sha2::{Digest, Sha256};
use triomphe::Arc;
use vfs::{AbsPath, AbsPathBuf};

use crate::config::{Config, LinkedProject};

const MAX_ENTRIES: usize = 32_768;
const MAX_FILE_BYTES: u64 = 4 * 1024 * 1024;
const MAX_TOTAL_BYTES: u64 = 64 * 1024 * 1024;
const MAX_DEPTH: usize = 64;
const MAX_DISCOVERY_PASSES: usize = 4;

#[derive(Debug, Clone, Default)]
struct Candidates {
    files: BTreeSet<AbsPathBuf>,
    manifests: BTreeSet<AbsPathBuf>,
    presences: BTreeSet<AbsPathBuf>,
    members: BTreeSet<AbsPathBuf>,
    targets: BTreeSet<AbsPathBuf>,
    configs: BTreeSet<AbsPathBuf>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Hash)]
enum InputKind {
    File,
    Presence,
    Members,
    Targets,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
enum FileState {
    Missing,
    Presence { canonical: AbsPathBuf },
    File { canonical: AbsPathBuf, digest: [u8; 32] },
    Directory { canonical: AbsPathBuf, digest: [u8; 32] },
}

#[derive(Clone)]
pub(crate) struct ConfigurationWitness {
    generation: u64,
    config: Arc<Config>,
    candidates: Candidates,
    entries: BTreeMap<(AbsPathBuf, InputKind), FileState>,
}

#[derive(Default)]
pub(crate) struct ConfigurationCustody {
    generation: u64,
    candidates: Candidates,
    passes: usize,
    pub(crate) model: Option<Arc<ConfigurationWitness>>,
    active: Option<Arc<ConfigurationWitness>>,
}

pub(crate) struct ConfigurationPlan {
    generation: u64,
    cargo: CargoConfig,
    config: Arc<Config>,
    candidates: Result<Candidates, String>,
    origin: Option<Arc<ConfigurationWitness>>,
    discovery_only: bool,
}

// Config and its diagnostic objects are shared immutably; no load mutates them.
impl std::panic::UnwindSafe for ConfigurationPlan {}

pub(crate) struct ConfigurationAttempt {
    generation: u64,
    cargo: CargoConfig,
    config: Arc<Config>,
    before: anyhow::Result<ConfigurationWitness>,
    discovery_only: bool,
    retry_on_error: bool,
}

pub(crate) struct ConfigurationLoad {
    generation: u64,
    config: Arc<Config>,
    candidates: Candidates,
    pub(crate) witness: Option<Arc<ConfigurationWitness>>,
    retry: bool,
}

pub(crate) struct ConfigurationOrigin {
    generation: u64,
    config: Arc<Config>,
    workspaces: Arc<Vec<ProjectWorkspace>>,
}

impl std::fmt::Debug for ConfigurationOrigin {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_tuple("ConfigurationOrigin").field(&self.generation).finish()
    }
}

impl ConfigurationWitness {
    pub(crate) fn validate(&self) -> anyhow::Result<()> {
        let now = capture(self.generation, self.config.clone(), self.candidates.clone())?;
        ensure!(self.entries == now.entries, "configuration inputs changed since project loading");
        Ok(())
    }

    pub(crate) fn file_paths(&self) -> impl Iterator<Item = &AbsPath> {
        self.entries
            .iter()
            .filter(|((_, kind), state)| {
                *kind == InputKind::File && !matches!(state, FileState::Directory { .. })
            })
            .map(|((path, _), _)| path.as_path())
    }

    pub(crate) fn hash_identity(&self, state: &mut impl Hasher) {
        self.generation.hash(state);
        self.entries.hash(state);
    }
}

impl std::fmt::Debug for ConfigurationLoad {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.debug_struct("ConfigurationLoad")
            .field("generation", &self.generation)
            .field("ready", &self.witness.is_some())
            .field("retry", &self.retry)
            .finish()
    }
}

impl ConfigurationCustody {
    pub(crate) fn origin(
        &self,
        config: &Arc<Config>,
        workspaces: &Arc<Vec<ProjectWorkspace>>,
    ) -> ConfigurationOrigin {
        ConfigurationOrigin {
            generation: self.generation,
            config: config.clone(),
            workspaces: workspaces.clone(),
        }
    }

    pub(crate) fn matches_origin(
        &self,
        origin: &ConfigurationOrigin,
        config: &Arc<Config>,
        workspaces: &Arc<Vec<ProjectWorkspace>>,
    ) -> bool {
        origin.generation == self.generation
            && Arc::ptr_eq(&origin.config, config)
            && Arc::ptr_eq(&origin.workspaces, workspaces)
    }

    pub(crate) fn is_current(&self, load: &ConfigurationLoad, config: &Arc<Config>) -> bool {
        load.generation == self.generation && Arc::ptr_eq(&load.config, config)
    }

    pub(crate) fn invalidate(&mut self) {
        self.generation = self.generation.wrapping_add(1);
        self.active = None;
    }

    pub(crate) fn active(&self, config: &Arc<Config>) -> Option<Arc<ConfigurationWitness>> {
        self.active.as_ref().filter(|witness| Arc::ptr_eq(&witness.config, config)).cloned()
    }

    pub(crate) fn needs_refresh(&self, config: &Arc<Config>) -> bool {
        self.model.as_ref().is_some_and(|witness| !Arc::ptr_eq(&witness.config, config))
    }

    pub(crate) fn workspace_plan(
        &mut self,
        config: &Arc<Config>,
        discovery: bool,
    ) -> ConfigurationPlan {
        self.invalidate();
        if !discovery {
            self.passes = 0;
        }
        self.passes += 1;
        let cargo = config.cargo(None);
        let candidates = (|| {
            supported(config, &cargo)?;
            let mut candidates = self.candidates.clone();
            for project in config.linked_or_discovered_projects() {
                match project {
                    LinkedProject::ProjectManifest(ProjectManifest::CargoToml(path)) => {
                        candidates.package(path.parent());
                    }
                    _ => anyhow::bail!(
                        "non-Cargo project configuration has no finite loader witness"
                    ),
                }
            }
            candidates.ambient(&cargo)?;
            Ok(candidates)
        })()
        .map_err(|error: anyhow::Error| error.to_string());
        ConfigurationPlan {
            generation: self.generation,
            cargo,
            config: config.clone(),
            candidates,
            origin: None,
            discovery_only: self.passes == 1,
        }
    }

    pub(crate) fn dependent_plan(&mut self, config: &Arc<Config>) -> ConfigurationPlan {
        self.invalidate();
        let cargo = config.cargo(None);
        let origin = self.model.clone();
        let candidates = (|| {
            supported(config, &cargo)?;
            let origin = origin.as_ref().context("workspace configuration witness unavailable")?;
            ensure!(Arc::ptr_eq(&origin.config, config), "loader configuration changed");
            Ok(origin.candidates.clone())
        })()
        .map_err(|error: anyhow::Error| error.to_string());
        ConfigurationPlan {
            generation: self.generation,
            cargo,
            config: config.clone(),
            candidates,
            origin,
            discovery_only: false,
        }
    }

    /// Returns whether the existing workspace queue should repeat discovery.
    pub(crate) fn observe(&mut self, load: &ConfigurationLoad) -> bool {
        if load.generation != self.generation {
            return false;
        }
        self.candidates = load.candidates.clone();
        load.retry && self.passes < MAX_DISCOVERY_PASSES
    }

    pub(crate) fn install_model(&mut self, load: &ConfigurationLoad) {
        if load.generation == self.generation {
            self.model = load.witness.clone();
        }
    }

    /// Called only when the corresponding graph/proc-macro change is applied.
    pub(crate) fn publish(&mut self, witness: Option<Arc<ConfigurationWitness>>) {
        self.active = witness.filter(|witness| witness.generation == self.generation);
        if self.active.is_some() {
            self.model = self.active.clone();
        }
    }
}

impl ConfigurationPlan {
    pub(crate) fn begin(self) -> ConfigurationAttempt {
        let retry_on_error = self.origin.is_some();
        let before = (|| {
            let before = capture(
                self.generation,
                self.config.clone(),
                self.candidates.map_err(anyhow::Error::msg)?,
            )?;
            if let Some(origin) = self.origin {
                ensure!(
                    origin.entries == before.entries,
                    "configuration changed between loading stages"
                );
            }
            Ok(before)
        })();
        ConfigurationAttempt {
            generation: self.generation,
            cargo: self.cargo,
            config: self.config,
            before,
            discovery_only: self.discovery_only,
            retry_on_error,
        }
    }
}

impl ConfigurationAttempt {
    pub(crate) fn finish(self, workspaces: &[ProjectWorkspace]) -> Box<ConfigurationLoad> {
        let result = (|| {
            let before = self.before?;
            let mut candidates = Candidates::default();
            for workspace in workspaces {
                match &workspace.kind {
                    ProjectWorkspaceKind::Cargo { cargo, error: None, rustc, .. } => {
                        for cargo in
                            std::iter::once(cargo).chain(rustc.as_ref().ok().map(|rustc| &rustc.0))
                        {
                            candidates.package(cargo.workspace_root());
                            for package in cargo.packages() {
                                candidates.package(cargo[package].manifest.parent());
                            }
                        }
                    }
                    _ => anyhow::bail!("unsupported or incomplete workspace configuration"),
                }
            }
            candidates.ambient(&self.cargo)?;
            let after = capture(self.generation, self.config.clone(), candidates)?;
            let ready = !self.discovery_only
                && after.entries.iter().all(|(key, state)| before.entries.get(key) == Some(state));
            Ok((after, ready))
        })();
        Box::new(match result {
            Ok((after, ready)) => ConfigurationLoad {
                generation: self.generation,
                config: self.config.clone(),
                candidates: after.candidates.clone(),
                witness: ready.then(|| Arc::new(after)),
                retry: !ready,
            },
            Err(error) => {
                tracing::debug!(%error, "configuration witness unavailable");
                ConfigurationLoad {
                    generation: self.generation,
                    config: self.config,
                    candidates: Candidates::default(),
                    witness: None,
                    retry: self.retry_on_error,
                }
            }
        })
    }
}

fn supported(config: &Config, cargo: &CargoConfig) -> anyhow::Result<()> {
    ensure!(
        config.discover_workspace_config().is_none(),
        "custom project discovery is unsupported"
    );
    ensure!(config.detached_files().is_empty(), "detached project inputs are unsupported");
    ensure!(cargo.run_build_script_command.is_none(), "custom build command is unsupported");
    ensure!(cargo.metadata_extra_args.is_empty(), "custom metadata arguments are unsupported");
    ensure!(cargo.extra_args.is_empty(), "custom Cargo arguments are unsupported");
    ensure!(env(cargo, "RUST_TARGET_PATH").is_none(), "custom target search paths are unsupported");
    Ok(())
}

fn env(cargo: &CargoConfig, name: &str) -> Option<String> {
    cargo.extra_env.get(name).cloned().unwrap_or_else(|| std::env::var(name).ok())
}

impl Candidates {
    fn package(&mut self, root: &AbsPath) {
        let root = root.normalize();
        self.files.insert(root.join("Cargo.toml"));
        self.manifests.insert(root.join("Cargo.toml"));
        self.files.insert(root.join("Cargo.lock"));
        for file in ["src/lib.rs", "src/main.rs"] {
            self.presences.insert(root.join(file));
        }
        for directory in ["src/bin", "examples", "tests", "benches"] {
            self.targets.insert(root.join(directory));
        }
        for ancestor in std::iter::successors(Some(root.as_path()), |path| path.parent()) {
            for file in [".cargo/config", ".cargo/config.toml"] {
                let path = ancestor.join(file);
                self.files.insert(path.clone());
                self.configs.insert(path);
            }
            for file in ["rust-toolchain", "rust-toolchain.toml", "rust-analyzer.toml"] {
                self.files.insert(ancestor.join(file));
            }
        }
    }

    fn ambient(&mut self, cargo: &CargoConfig) -> anyhow::Result<()> {
        if let Some(path) = &cargo.config_path {
            self.files.insert(path.clone());
            self.configs.insert(path.clone());
        }
        let cargo_home = env(cargo, "CARGO_HOME")
            .or_else(|| env(cargo, "HOME").map(|home| format!("{home}/.cargo")));
        if let Some(home) = cargo_home {
            let home = AbsPathBuf::try_from(paths::Utf8PathBuf::from(home))
                .map_err(|_| anyhow::anyhow!("Cargo home must be absolute"))?;
            for file in ["config", "config.toml"] {
                let path = home.join(file);
                self.files.insert(path.clone());
                self.configs.insert(path);
            }
        }
        if let Some(directory) = Config::user_config_dir_path() {
            self.files.insert(directory.join("rust-analyzer.toml"));
        }
        for target in [cargo.target.clone(), env(cargo, "CARGO_BUILD_TARGET")].into_iter().flatten()
        {
            self.target(&target)?;
        }
        Ok(())
    }

    fn target(&mut self, target: &str) -> anyhow::Result<()> {
        if target.ends_with(".json") {
            let target = Utf8Path::new(target);
            if target.is_absolute() {
                self.files.insert(AbsPathBuf::assert(target.to_path_buf()).normalize());
            } else {
                let roots: Vec<_> = self
                    .manifests
                    .iter()
                    .filter(|path| path.file_name() == Some("Cargo.toml"))
                    .map(|path| path.parent().unwrap().to_path_buf())
                    .collect();
                for root in roots {
                    self.files.insert(root.join(target).normalize());
                }
            }
        }
        Ok(())
    }
}

fn capture(
    generation: u64,
    config: Arc<Config>,
    mut candidates: Candidates,
) -> anyhow::Result<ConfigurationWitness> {
    let mut total_bytes = 0;
    let mut done = BTreeSet::new();
    let mut entries = BTreeMap::new();
    let mut directory_nodes = 0;
    loop {
        let paths: BTreeSet<_> = [
            (&candidates.files, InputKind::File),
            (&candidates.presences, InputKind::Presence),
            (&candidates.members, InputKind::Members),
            (&candidates.targets, InputKind::Targets),
        ]
        .into_iter()
        .flat_map(|(paths, kind)| paths.iter().map(move |path| (path.clone(), kind)))
        .collect();
        let pending: Vec<_> = paths.difference(&done).cloned().collect();
        if pending.is_empty() {
            break;
        }
        ensure!(
            done.len() + pending.len() <= MAX_ENTRIES,
            "configuration witness entry budget exceeded"
        );
        for (path, kind) in pending {
            let key = (path.clone(), kind);
            done.insert(key.clone());
            let metadata = match fs::symlink_metadata(&path) {
                Ok(metadata) => metadata,
                Err(error) if error.kind() == std::io::ErrorKind::NotFound => {
                    entries.insert(key, FileState::Missing);
                    continue;
                }
                Err(error) => return Err(error).context("reading configuration metadata"),
            };
            ensure!(
                !metadata.file_type().is_symlink(),
                "symlinked configuration inputs are unsupported"
            );
            let canonical = paths::Utf8PathBuf::from_path_buf(fs::canonicalize(&path)?)
                .map_err(|_| anyhow::anyhow!("non-UTF8 canonical configuration path"))?;
            let canonical = AbsPathBuf::assert(canonical);
            if matches!(kind, InputKind::Members | InputKind::Targets) {
                ensure!(metadata.is_dir(), "Cargo discovery root is not a directory");
                let mut children: Vec<_> =
                    fs::read_dir(&path)?.take(MAX_ENTRIES + 1).collect::<Result<_, _>>()?;
                directory_nodes += children.len();
                ensure!(
                    directory_nodes <= MAX_ENTRIES,
                    "configuration membership node budget exceeded"
                );
                children.sort_by_key(|entry| entry.file_name());
                let mut hash = Sha256::new();
                for child in children {
                    let name = child
                        .file_name()
                        .into_string()
                        .map_err(|_| anyhow::anyhow!("non-UTF8 configuration member"))?;
                    let file_type = child.file_type()?;
                    let named_file = match kind {
                        InputKind::Members => name == "Cargo.toml",
                        InputKind::Targets => name.ends_with(".rs"),
                        InputKind::File | InputKind::Presence => unreachable!(),
                    };
                    if file_type.is_symlink() {
                        // Irrelevant regular-file aliases (e.g. license files) cannot
                        // select a member or Rust target; directory aliases can.
                        ensure!(
                            !named_file && fs::metadata(child.path())?.is_file(),
                            "symlinked Cargo discovery input is unsupported: {}",
                            path.join(&name)
                        );
                        continue;
                    }
                    if !file_type.is_dir() && !named_file {
                        continue;
                    }
                    hash.update((name.len() as u64).to_le_bytes());
                    hash.update(name.as_bytes());
                    hash.update([
                        u8::from(file_type.is_dir()),
                        u8::from(file_type.is_file()),
                        u8::from(file_type.is_symlink()),
                    ]);
                    let child = path.join(&name);
                    if file_type.is_dir() {
                        ensure!(
                            <AbsPathBuf as AsRef<Utf8Path>>::as_ref(&child).components().count()
                                <= MAX_DEPTH,
                            "configuration witness depth budget exceeded"
                        );
                        match kind {
                            InputKind::Members => candidates.members.insert(child.normalize()),
                            InputKind::Targets => candidates.targets.insert(child.normalize()),
                            InputKind::File | InputKind::Presence => unreachable!(),
                        };
                    } else if kind == InputKind::Members {
                        candidates.files.insert(child);
                    }
                }
                entries.insert(
                    key,
                    FileState::Directory { canonical, digest: hash.finalize().into() },
                );
            } else {
                ensure!(metadata.is_file(), "unsupported configuration file type");
                if kind == InputKind::Presence {
                    entries.insert(key, FileState::Presence { canonical });
                    continue;
                }
                let mut bytes = Vec::new();
                fs::File::open(&path)?.take(MAX_FILE_BYTES + 1).read_to_end(&mut bytes)?;
                ensure!(
                    bytes.len() as u64 <= MAX_FILE_BYTES,
                    "configuration file byte budget exceeded"
                );
                total_bytes += bytes.len() as u64;
                ensure!(
                    total_bytes <= MAX_TOTAL_BYTES,
                    "configuration witness byte budget exceeded"
                );
                if candidates.manifests.contains(&path) || candidates.configs.contains(&path) {
                    let text = std::str::from_utf8(&bytes)?;
                    let table: toml::Table = toml::from_str(text)?;
                    if candidates.configs.contains(&path) {
                        ensure!(
                            !table.contains_key("include"),
                            "included Cargo config sources are unsupported"
                        );
                        if let Some(targets) =
                            table.get("build").and_then(|value| value.get("target"))
                        {
                            let targets: Vec<_> = match targets {
                                toml::Value::String(target) => vec![target.as_str()],
                                toml::Value::Array(targets) => targets
                                    .iter()
                                    .map(|target| {
                                        target
                                            .as_str()
                                            .context("unsupported Cargo target specification")
                                    })
                                    .collect::<Result<_, _>>()?,
                                _ => anyhow::bail!("unsupported Cargo target specification"),
                            };
                            for target in targets {
                                candidates.target(target)?;
                                if target.ends_with(".json") && !Utf8Path::new(target).is_absolute()
                                {
                                    let parent = path.parent().unwrap();
                                    candidates.files.insert(parent.join(target).normalize());
                                    if let Some(root) = parent.parent() {
                                        candidates.files.insert(root.join(target).normalize());
                                    }
                                }
                            }
                        }
                    } else if let Some(members) =
                        table.get("workspace").and_then(|workspace| workspace.get("members"))
                    {
                        for member in members.as_array().context("unsupported workspace members")? {
                            let member = member.as_str().context("unsupported workspace member")?;
                            let prefix: Vec<_> = member
                                .split('/')
                                .take_while(|part| !part.contains(['*', '?', '[', ']', '{', '}']))
                                .collect();
                            if prefix.len() == member.split('/').count() {
                                candidates.package(&path.parent().unwrap().join(member));
                            } else {
                                candidates.members.insert(
                                    path.parent().unwrap().join(prefix.join("/")).normalize(),
                                );
                            }
                        }
                    }
                }
                entries.insert(
                    key,
                    FileState::File { canonical, digest: Sha256::digest(&bytes).into() },
                );
            }
        }
    }
    Ok(ConfigurationWitness { generation, config, candidates, entries })
}

#[cfg(test)]
mod tests {
    use stdx::tempfile::NamedTempDir;

    use super::*;

    #[test]
    fn member_inventory_and_absent_configuration_are_custodied() {
        let directory = NamedTempDir::new("configuration-custody").unwrap();
        let root = AbsPathBuf::try_from(directory.path().to_str().unwrap()).unwrap();
        fs::create_dir_all(root.join("crates/a/fixture")).unwrap();
        fs::create_dir_all(root.join("src/bin")).unwrap();
        fs::write(root.join("src/bin/existing.rs"), "fn main() {}").unwrap();
        fs::write(root.join("Cargo.toml"), "[workspace]\nmembers = [\"crates/*\"]\n").unwrap();
        fs::write(
            root.join("crates/a/Cargo.toml"),
            "[package]\nname = \"a\"\nversion = \"0.1.0\"\n",
        )
        .unwrap();
        // Membership inventory retains fixture manifest bytes without treating
        // every nested file as a manifest Cargo actually selected.
        fs::write(root.join("crates/a/fixture/Cargo.toml"), "not a Cargo manifest").unwrap();
        let config =
            Arc::new(Config::new(root.clone(), Default::default(), vec![root.clone()], None));
        let mut candidates = Candidates::default();
        candidates.package(&root);
        let witness = capture(1, config.clone(), candidates).unwrap();
        assert!(witness.file_paths().any(|path| path == root.join(".cargo/config.toml").as_path()));
        witness.validate().unwrap();
        fs::write(root.join("src/bin/.staged-import"), "staged source bytes").unwrap();
        fs::write(root.join("crates/a/.staged-import"), "staged source bytes").unwrap();
        witness.validate().unwrap();
        fs::write(root.join("src/bin/new.rs"), "fn main() {}").unwrap();
        assert!(witness.validate().is_err());
        let witness = capture(2, config.clone(), witness.candidates.clone()).unwrap();

        // Neither a new member nor creation of a previously absent config file
        // need have reached the VFS watcher to invalidate the saved witness.
        fs::create_dir_all(root.join("crates/b")).unwrap();
        fs::write(
            root.join("crates/b/Cargo.toml"),
            "[package]\nname = \"b\"\nversion = \"0.1.0\"\n",
        )
        .unwrap();
        assert!(witness.validate().is_err());
        let witness = capture(3, config.clone(), witness.candidates.clone()).unwrap();
        fs::create_dir(root.join(".cargo")).unwrap();
        fs::write(
            root.join(".cargo/config.toml"),
            "[build]\ntarget = \"x86_64-unknown-linux-gnu\"\n",
        )
        .unwrap();
        assert!(witness.validate().is_err());

        fs::write(root.join(".cargo/config.toml"), "[build]\ntarget = [\"custom.json\"]\n")
            .unwrap();
        fs::write(root.join("custom.json"), "{}").unwrap();
        let witness = capture(4, config, witness.candidates.clone()).unwrap();
        assert!(witness.file_paths().any(|path| path == root.join("custom.json").as_path()));
        fs::write(root.join("custom.json"), "{\"changed\": true}").unwrap();
        assert!(witness.validate().is_err());
    }

    #[test]
    fn dependent_loads_and_publication_keep_their_generation() {
        let directory = NamedTempDir::new("configuration-generation").unwrap();
        let root = AbsPathBuf::try_from(directory.path().to_str().unwrap()).unwrap();
        fs::write(root.join("Cargo.toml"), "[package]\nname = \"a\"\nversion = \"0.1.0\"\n")
            .unwrap();
        let config =
            Arc::new(Config::new(root.clone(), Default::default(), vec![root.clone()], None));
        let mut candidates = Candidates::default();
        candidates.package(&root);
        let witness = Arc::new(capture(1, config.clone(), candidates).unwrap());
        let mut custody = ConfigurationCustody { generation: 1, ..Default::default() };
        custody.publish(Some(witness.clone()));
        assert!(custody.active(&config).is_some());
        custody.invalidate();
        custody.publish(Some(witness.clone()));
        assert!(custody.active(&config).is_none());

        fs::write(root.join("Cargo.toml"), "[package]\nname = \"changed\"\nversion = \"0.1.0\"\n")
            .unwrap();
        let attempt = ConfigurationPlan {
            generation: custody.generation,
            cargo: config.cargo(None),
            config,
            candidates: Ok(witness.candidates.clone()),
            origin: Some(witness),
            discovery_only: false,
        }
        .begin();
        assert!(attempt.before.is_err());
    }
}
