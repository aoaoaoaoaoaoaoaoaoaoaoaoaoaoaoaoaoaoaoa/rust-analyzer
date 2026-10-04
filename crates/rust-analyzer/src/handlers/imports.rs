//! Read-only import assessments over the existing analysis database.

use std::hash::{Hash, Hasher};

use ide::{ImportAssessment, InputStamp};
use paths::Utf8PathBuf;
use sha2::{Digest, Sha256};
use syntax::{TextRange, TextSize};
use vfs::AbsPathBuf;

use crate::{
    global_state::GlobalStateSnapshot,
    lsp::{ext, to_proto},
};

const MAX_INPUT_FILES: usize = 32_768;
const MAX_INPUT_BYTES: usize = 256 * 1024 * 1024;

struct StampHasher(Sha256);

pub(super) enum WitnessUse {
    Assessment,
    Recheck,
}

impl Hasher for StampHasher {
    fn write(&mut self, bytes: &[u8]) {
        self.0.update(bytes);
    }

    fn finish(&self) -> u64 {
        let bytes = self.0.clone().finalize();
        u64::from_le_bytes(bytes[..8].try_into().unwrap())
    }
}

pub(super) fn stamp_digest(snap: &GlobalStateSnapshot, stamp: InputStamp) -> String {
    let mut hasher = StampHasher(Sha256::new());
    hasher.0.update(b"semedit-imports-input-stamp-v1");
    stamp.hash(&mut hasher);
    if let Some(witness) = &snap.configuration_witness {
        hasher.0.update(b"configuration-witness");
        witness.hash_identity(&mut hasher);
    } else {
        hasher.0.update(b"configuration-unwitnessed");
    }
    format!("{:x}", hasher.0.finalize())
}

pub(super) fn text_digest(text: &str) -> String {
    format!("{:x}", Sha256::digest(text.as_bytes()))
}

pub(super) fn ready(snap: &GlobalStateSnapshot) -> anyhow::Result<()> {
    anyhow::ensure!(
        snap.import_inputs_ready && snap.proc_macros_loaded,
        "import analysis inputs are incomplete or a reload is pending"
    );
    Ok(())
}

/// Applied Salsa inputs cannot attest to unmodeled files consumed by Cargo earlier.
/// A loader witness must verify those bytes before returning an actionable assessment.
pub(super) fn configuration_witness(
    snap: &GlobalStateSnapshot,
    purpose: WitnessUse,
) -> anyhow::Result<()> {
    let Some(witness) = snap.configuration_witness.as_ref() else {
        if matches!(purpose, WitnessUse::Assessment) {
            snap.request_configuration_reload_if_needed();
        }
        anyhow::bail!(
            "configuration loader witness unavailable: reload the workspace or use supported Cargo configuration"
        );
    };
    let result = witness.validate();
    if result.is_err() && matches!(purpose, WitnessUse::Assessment) {
        snap.request_configuration_reload();
    }
    result
}

fn config_paths(snap: &GlobalStateSnapshot) -> Vec<lsp_types::Uri> {
    snap.configuration_witness
        .iter()
        .flat_map(|witness| witness.file_paths())
        .map(to_proto::url_from_abs_path)
        .collect()
}

pub(crate) fn handle_import_stamp(
    snap: GlobalStateSnapshot,
    _: ext::ImportStampParams,
) -> anyhow::Result<ext::ImportStampResult> {
    ready(&snap)?;
    configuration_witness(&snap, WitnessUse::Recheck)?;
    let stamp = stamp_digest(&snap, snap.analysis.input_stamp()?);
    configuration_witness(&snap, WitnessUse::Recheck)?;
    Ok(ext::ImportStampResult { stamp })
}

pub(crate) fn handle_assess_import(
    snap: GlobalStateSnapshot,
    params: ext::AssessImportParams,
) -> anyhow::Result<ext::AssessImportResult> {
    let input_stamp = snap.analysis.input_stamp()?;
    let mut result = ext::AssessImportResult {
        decision: ext::ImportDecision::Unknown,
        reason: None,
        stamp: stamp_digest(&snap, input_stamp),
        dependencies: Vec::new(),
        config_paths: config_paths(&snap),
    };
    let assessment = (|| -> anyhow::Result<ImportAssessment> {
        ready(&snap)?;
        configuration_witness(&snap, WitnessUse::Assessment)?;
        anyhow::ensure!(
            params.expected_sha256.len() == 64
                && params
                    .expected_sha256
                    .bytes()
                    .all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)),
            "expectedSha256 must be lowercase SHA256 hex"
        );
        let target_path = params
            .text_document
            .uri
            .to_file_path()
            .map_err(|()| anyhow::anyhow!("target URI must name a local file"))?;
        let target_path = Utf8PathBuf::from_path_buf(target_path)
            .map_err(|_| anyhow::anyhow!("target file path must be UTF-8"))?;
        let target_path = AbsPathBuf::try_from(target_path)
            .map_err(|_| anyhow::anyhow!("target file path must be absolute"))?;
        let inputs = snap
            .analysis
            .input_files(MAX_INPUT_FILES)?
            .ok_or_else(|| anyhow::anyhow!("analysis input-file budget exceeded"))?;
        let mut target = None;
        let mut input_bytes = 0usize;
        for (file, path) in inputs {
            let path = path
                .as_path()
                .ok_or_else(|| anyhow::anyhow!("virtual analysis inputs are unsupported"))?;
            let text = snap.analysis.file_text(file)?;
            input_bytes = input_bytes
                .checked_add(text.len())
                .ok_or_else(|| anyhow::anyhow!("analysis input-byte budget overflow"))?;
            anyhow::ensure!(input_bytes <= MAX_INPUT_BYTES, "analysis input-byte budget exceeded");
            let hash = text_digest(&text);
            if path == &*target_path {
                anyhow::ensure!(
                    hash == params.expected_sha256,
                    "target text differs from expectedSha256"
                );
                target = Some((file, text));
            }
            result.dependencies.push(ext::ImportDependency {
                uri: to_proto::url_from_abs_path(path),
                sha256: hash,
            });
        }
        let (file, text) =
            target.ok_or_else(|| anyhow::anyhow!("target is absent from analysis inputs"))?;
        let start = params.scope.start as usize;
        let end = params.scope.end as usize;
        anyhow::ensure!(
            start <= end
                && end <= text.len()
                && text.is_char_boundary(start)
                && text.is_char_boundary(end),
            "scope is not a valid UTF-8 byte range"
        );
        let assessment = snap.analysis.assess_import(
            file,
            TextRange::new(TextSize::from(params.scope.start), TextSize::from(params.scope.end)),
            &params.path,
            params.alias.as_deref(),
        )?;
        configuration_witness(&snap, WitnessUse::Assessment)?;
        anyhow::ensure!(snap.analysis.input_stamp()? == input_stamp, "analysis inputs changed");
        Ok(assessment)
    })();
    let assessment =
        assessment.unwrap_or_else(|error| ImportAssessment::Unknown(error.to_string()));
    match assessment {
        ImportAssessment::AlreadyAvailable => {
            result.decision = ext::ImportDecision::AlreadyAvailable
        }
        ImportAssessment::Insert => result.decision = ext::ImportDecision::Insert,
        ImportAssessment::Conflict(reason) => {
            result.decision = ext::ImportDecision::Conflict;
            result.reason = Some(reason);
        }
        ImportAssessment::Unknown(reason) => result.reason = Some(reason),
    }
    result.dependencies.sort_by(|a, b| a.uri.as_str().cmp(b.uri.as_str()));
    Ok(result)
}
