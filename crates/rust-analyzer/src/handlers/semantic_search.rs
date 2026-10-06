//! Snapshot-guarded source capture for private semantic discovery requests.

use std::collections::BTreeMap;

use ide::{SignatureAnchor, SignatureCandidateSource, SignatureSearchScope};
use lsp_types::Uri;
use syntax::{TextRange, TextSize};

use super::imports::text_digest;
use crate::{global_state::GlobalStateSnapshot, lsp::signature as wire};

#[derive(Default)]
pub(crate) struct SourceRevisions {
    pub(crate) entries: BTreeMap<String, String>,
    bytes: usize,
}

pub(crate) fn record_source(
    snap: &GlobalStateSnapshot,
    file: ide::FileId,
    revisions: &mut SourceRevisions,
) -> anyhow::Result<String> {
    let uri = snap.file_id_to_url(file).to_string();
    if let Some(hash) = revisions.entries.get(&uri) {
        return Ok(hash.clone());
    }
    let text = snap.analysis.file_text(file)?;
    revisions.bytes = revisions
        .bytes
        .checked_add(text.len())
        .ok_or_else(|| anyhow::anyhow!("source revision byte overflow"))?;
    anyhow::ensure!(
        revisions.bytes <= 64 * 1024 * 1024,
        "selected source revision bytes exceed64MiB; narrow scope/max_candidates"
    );
    let hash = text_digest(&text);
    revisions.entries.insert(uri, hash.clone());
    Ok(hash)
}
pub(crate) fn anchor(
    snap: &GlobalStateSnapshot,
    anchor: wire::SourceAnchor,
    revisions: &mut SourceRevisions,
    stamp: &str,
) -> anyhow::Result<SignatureAnchor> {
    anyhow::ensure!(
        anchor.sha256.len() == 64
            && anchor.sha256.bytes().all(|b| b.is_ascii_digit() || (b'a'..=b'f').contains(&b)),
        "anchor sha256 must be lowercase SHA256 hex"
    );
    let uri = anchor.uri.parse::<Uri>()?;
    let file_id = snap
        .url_to_file_id(&uri)?
        .ok_or_else(|| anyhow::anyhow!("anchor URI is absent from provider VFS"))?;
    anyhow::ensure!(
        record_source(snap, file_id, revisions)? == anchor.sha256,
        "anchor text differs from expected sha256"
    );
    let text = snap.analysis.file_text(file_id)?;
    let range = anchor
        .range
        .map(|range| {
            let (start, end) = (range.start as usize, range.end as usize);
            anyhow::ensure!(
                start <= end
                    && end <= text.len()
                    && text.is_char_boundary(start)
                    && text.is_char_boundary(end),
                "anchor range is not a valid UTF-8 byte range"
            );
            Ok(TextRange::new(TextSize::from(range.start), TextSize::from(range.end)))
        })
        .transpose()?;
    let context_id = anchor
        .context_id
        .map(|id| {
            id.strip_prefix(&format!("{stamp}:")).map(str::to_owned).ok_or_else(|| {
                anyhow::anyhow!("context_id belongs to a different provider snapshot")
            })
        })
        .transpose()?;
    Ok(SignatureAnchor { file_id, range, context_id })
}
pub(crate) fn scope(
    snap: &GlobalStateSnapshot,
    input: wire::SearchScope,
    revisions: &mut SourceRevisions,
) -> anyhow::Result<SignatureSearchScope> {
    Ok(match input {
        wire::SearchScope::Workspace => SignatureSearchScope::Workspace,
        wire::SearchScope::Regions { regions } => {
            anyhow::ensure!(
                !regions.is_empty() && regions.len() <= 4096,
                "regions must contain between1 and4096 entries"
            );
            let mut resolved = Vec::new();
            for region in regions {
                let uri = region.uri.parse::<Uri>()?;
                let file = snap
                    .url_to_file_id(&uri)?
                    .ok_or_else(|| anyhow::anyhow!("scope URI absent from provider VFS"))?;
                anyhow::ensure!(
                    record_source(snap, file, revisions)? == region.sha256,
                    "scope source differs from expected sha256"
                );
                let range = region
                    .range
                    .map(|range| {
                        let text = snap.analysis.file_text(file)?;
                        anyhow::ensure!(
                            range.start <= range.end
                                && range.end as usize <= text.len()
                                && text.is_char_boundary(range.start as usize)
                                && text.is_char_boundary(range.end as usize),
                            "scope range is invalid"
                        );
                        Ok::<_, anyhow::Error>(TextRange::new(range.start.into(), range.end.into()))
                    })
                    .transpose()?;
                resolved.push((file, range));
            }
            SignatureSearchScope::Regions(resolved)
        }
    })
}

pub(crate) fn source(
    snap: &GlobalStateSnapshot,
    input: SignatureCandidateSource,
    revisions: &mut SourceRevisions,
) -> anyhow::Result<wire::CandidateSource> {
    Ok(match input {
        SignatureCandidateSource::Physical { range, name_offset } => {
            let uri = snap.file_id_to_url(range.file_id);
            let sha256 = record_source(snap, range.file_id, revisions)?;
            let index = snap.analysis.file_line_index(range.file_id)?;
            let point = index
                .to_wide(ide_db::line_index::WideEncoding::Utf16, index.line_col(name_offset))
                .ok_or_else(|| anyhow::anyhow!("invalid UTF16 source point"))?;
            wire::CandidateSource::Physical {
                source: wire::SignatureSource {
                    uri: uri.to_string(),
                    range: wire::ByteRange {
                        start: range.range.start().into(),
                        end: range.range.end().into(),
                    },
                    name_offset: name_offset.into(),
                    line: point.line + 1,
                    column: point.col + 1,
                    sha256,
                },
            }
        }
        SignatureCandidateSource::Nonphysical { file_id, reason, .. } => {
            wire::CandidateSource::Nonphysical {
                uri: file_id.map(|file| snap.file_id_to_url(file).to_string()),
                reason,
            }
        }
    })
}
