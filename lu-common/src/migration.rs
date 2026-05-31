//! v1.0.0-rc.1 RC1.6 — chained migration for lu-kb files.
//!
//! Per `memory/logicutils_version_rule.md` §3 (21E.2 option
//! 2-A'), every step is **preserved forever**. v0.x → v1.x is
//! the first converter shipped at v1.0.0-rc.1; v1.x → v2.x
//! ships when v2.0 actually lands; chained calls walk the
//! sequence one step at a time so a user file written under
//! v0.x can be migrated through v1.x to v2.x by invoking
//! `v0_to_v1` followed by `v1_to_v2`.
//!
//! Each converter accepts the source text + an optional file
//! origin annotation and produces the migrated text + a
//! summary of changes applied. The summary structure is the
//! same across every converter so downstream tooling
//! (`adsmt-lsp::migration_code_actions`, the CLI migrate
//! sub-command, …) can chain them mechanically.

use std::fmt;

/// Summary of what a migration step applied. Same shape across
/// every step in the chain so the LSP / CLI surface can render
/// them uniformly.
#[derive(Clone, Debug, Default)]
pub struct MigrationSummary {
    /// One human-readable line per change. Lines should be
    /// short enough to fit in a code-action menu (~80 chars).
    pub notes: Vec<String>,
}

impl fmt::Display for MigrationSummary {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        for (i, line) in self.notes.iter().enumerate() {
            if i > 0 { writeln!(f)?; }
            write!(f, "- {line}")?;
        }
        Ok(())
    }
}

/// Result of one migration step.
#[derive(Clone, Debug)]
pub struct MigrationOutput {
    pub text: String,
    pub summary: MigrationSummary,
}

/// v0.x → v1.x converter.
///
/// At v1.0.0-rc.1 the v0.x kb-syntax is identical to the v1.x
/// surface (the absorption was source-compatible — the
/// changes were workspace-level, not language-level). This
/// converter therefore performs **no rewrites**; it
/// announces the v0.x → v1.x audit so downstream tooling can
/// surface the no-op clearly to users.
///
/// When a future v1.x point release introduces a real kb
/// surface change, the converter learns the rewrite and the
/// summary grows accordingly.
pub fn v0_to_v1(source: &str) -> MigrationOutput {
    MigrationOutput {
        text: source.to_string(),
        summary: MigrationSummary {
            notes: vec![
                "v0.x → v1.x: kb surface unchanged at v1.0.0-rc.1; \
                 no rewrites applied"
                    .to_string(),
            ],
        },
    }
}

/// Walk every converter in the chain starting from `from_major`
/// up to `to_major - 1` (so `chain(0, 1)` calls just `v0_to_v1`;
/// `chain(0, 2)` would call `v0_to_v1` then `v1_to_v2` once
/// the latter exists).
///
/// Returns the cumulative migration output. The summary is the
/// concatenation of every step's summary in order.
pub fn chain(source: &str, from_major: u32, to_major: u32) -> MigrationOutput {
    let mut current_text = source.to_string();
    let mut combined_notes = Vec::new();
    for major in from_major..to_major {
        match major {
            0 => {
                let step = v0_to_v1(&current_text);
                current_text = step.text;
                combined_notes.extend(step.summary.notes);
            }
            // v1 → v2 etc. ship later — for now, anything past
            // v0 → v1 is a no-op that records the gap.
            n => {
                combined_notes.push(format!(
                    "v{n}.x → v{}.x: converter not yet shipped \
                     (lands when v{}.0 actually releases)",
                    n + 1,
                    n + 1,
                ));
            }
        }
    }
    MigrationOutput {
        text: current_text,
        summary: MigrationSummary { notes: combined_notes },
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn v0_to_v1_is_identity_at_rc1() {
        let src = "(kind T : *)\n(fn add ...)";
        let out = v0_to_v1(src);
        assert_eq!(out.text, src);
        assert!(!out.summary.notes.is_empty());
    }

    #[test]
    fn chain_zero_to_one_calls_v0_to_v1() {
        let src = "(kind T : *)";
        let out = chain(src, 0, 1);
        assert_eq!(out.text, src);
        assert_eq!(out.summary.notes.len(), 1);
        assert!(out.summary.notes[0].contains("v0.x → v1.x"));
    }

    #[test]
    fn chain_zero_to_two_includes_v1_to_v2_placeholder() {
        let src = "(kind T : *)";
        let out = chain(src, 0, 2);
        assert_eq!(out.summary.notes.len(), 2);
        assert!(out.summary.notes[0].contains("v0.x → v1.x"));
        assert!(out.summary.notes[1].contains("v1.x → v2.x"));
        assert!(out.summary.notes[1].contains("not yet shipped"));
    }

    #[test]
    fn chain_empty_range_yields_empty_summary() {
        let out = chain("(kind T : *)", 1, 1);
        assert!(out.summary.notes.is_empty());
        assert_eq!(out.text, "(kind T : *)");
    }

    #[test]
    fn migration_summary_renders_one_line_per_note() {
        let s = MigrationSummary {
            notes: vec!["a".to_string(), "b".to_string()],
        };
        let rendered = format!("{s}");
        assert!(rendered.contains("- a"));
        assert!(rendered.contains("- b"));
    }
}
