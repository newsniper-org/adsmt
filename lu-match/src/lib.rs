use std::collections::HashMap;
use std::path::Path;

/// A parsed pattern containing literal segments and named wildcards.
#[derive(Debug, Clone)]
pub struct Pattern {
    segments: Vec<PatternSegment>,
}

#[derive(Debug, Clone)]
enum PatternSegment {
    Literal(String),
    Wildcard { name: String, kind: WildcardKind },
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum WildcardKind {
    /// Default: matches one or more chars, greedy, no path separator
    Segment,
    /// Matches anything including path separators
    Any,
}

/// Variable bindings from a successful match.
pub type Bindings = HashMap<String, String>;

/// Parse a pattern string like `align-{X}-{Y}.bam` into a Pattern.
///
/// Syntax:
/// - `{NAME}` or `{NAME:segment}` — match one or more non-`/` characters
/// - `{NAME:any}` — match anything including `/`
pub fn parse_pattern(pat: &str) -> Result<Pattern, PatternError> {
    let mut segments = Vec::new();
    let mut chars = pat.chars().peekable();
    let mut literal = String::new();

    while let Some(&ch) = chars.peek() {
        if ch == '{' {
            chars.next();
            if !literal.is_empty() {
                segments.push(PatternSegment::Literal(std::mem::take(&mut literal)));
            }
            let mut name = String::new();
            let mut kind_str = String::new();
            let mut in_kind = false;
            loop {
                match chars.next() {
                    Some('}') => break,
                    Some(':') => in_kind = true,
                    Some(c) => {
                        if in_kind {
                            kind_str.push(c);
                        } else {
                            name.push(c);
                        }
                    }
                    None => return Err(PatternError::UnterminatedWildcard),
                }
            }
            if name.is_empty() {
                return Err(PatternError::EmptyWildcardName);
            }
            let kind = match kind_str.as_str() {
                "" | "segment" => WildcardKind::Segment,
                "any" => WildcardKind::Any,
                other => return Err(PatternError::UnknownWildcardKind(other.into())),
            };
            segments.push(PatternSegment::Wildcard { name, kind });
        } else {
            chars.next();
            literal.push(ch);
        }
    }
    if !literal.is_empty() {
        segments.push(PatternSegment::Literal(literal));
    }
    Ok(Pattern { segments })
}

/// Try to match an input string against a pattern, returning bindings on success.
pub fn match_pattern(pattern: &Pattern, input: &str) -> Option<Bindings> {
    let mut bindings = Bindings::new();
    if do_match(&pattern.segments, input, &mut bindings) {
        Some(bindings)
    } else {
        None
    }
}

/// Recursive backtracking matcher.
fn do_match(segments: &[PatternSegment], input: &str, bindings: &mut Bindings) -> bool {
    match segments.first() {
        None => input.is_empty(),
        Some(PatternSegment::Literal(lit)) => {
            if let Some(rest) = input.strip_prefix(lit.as_str()) {
                do_match(&segments[1..], rest, bindings)
            } else {
                false
            }
        }
        Some(PatternSegment::Wildcard { name, kind }) => {
            let remaining = &segments[1..];
            // Try matching 1..=n characters
            for end in 1..=input.len() {
                let candidate = &input[..end];

                // For segment kind, reject path separators
                if *kind == WildcardKind::Segment && candidate.contains('/') {
                    break;
                }

                // Check consistency: if this variable was already bound, it must match
                if let Some(existing) = bindings.get(name) {
                    if existing != candidate {
                        continue;
                    }
                }

                let old = bindings.insert(name.clone(), candidate.to_string());
                if do_match(remaining, &input[end..], bindings) {
                    return true;
                }
                // Backtrack
                match old {
                    Some(v) => bindings.insert(name.clone(), v),
                    None => bindings.remove(name),
                };
            }
            false
        }
    }
}

/// Expand a template string using bindings, replacing `{NAME}` with bound values.
pub fn expand_template(template: &str, bindings: &Bindings) -> String {
    let mut result = String::new();
    let mut chars = template.chars().peekable();
    while let Some(&ch) = chars.peek() {
        if ch == '{' {
            chars.next();
            let mut name = String::new();
            for c in chars.by_ref() {
                if c == '}' {
                    break;
                }
                // Ignore kind specifier in templates
                if c == ':' {
                    for c2 in chars.by_ref() {
                        if c2 == '}' {
                            break;
                        }
                    }
                    break;
                }
                name.push(c);
            }
            match bindings.get(&name) {
                Some(val) => result.push_str(val),
                None => {
                    result.push('{');
                    result.push_str(&name);
                    result.push('}');
                }
            }
        } else {
            chars.next();
            result.push(ch);
        }
    }
    result
}

/// Convert a pattern to a glob string (replace wildcards with `*`).
pub fn pattern_to_glob(pattern: &Pattern) -> String {
    let mut glob = String::new();
    for seg in &pattern.segments {
        match seg {
            PatternSegment::Literal(s) => glob.push_str(s),
            PatternSegment::Wildcard { kind, .. } => match kind {
                WildcardKind::Segment => glob.push('*'),
                WildcardKind::Any => glob.push_str("**"),
            },
        }
    }
    glob
}

/// List files matching a pattern using filesystem globbing, then match each against the pattern.
pub fn glob_match(pattern: &Pattern, base_dir: &Path) -> Vec<(String, Bindings)> {
    let glob_str = pattern_to_glob(pattern);
    let full_glob = if base_dir == Path::new("") || base_dir == Path::new(".") {
        glob_str
    } else {
        format!("{}/{}", base_dir.display(), glob_str)
    };

    let mut results = Vec::new();
    if let Ok(paths) = glob::glob(&full_glob) {
        for entry in paths.flatten() {
            let path_str = entry.to_string_lossy().into_owned();
            // Match against the relative part
            let candidate = if let Some(rel) = path_str.strip_prefix(&format!("{}/", base_dir.display())) {
                rel.to_string()
            } else {
                path_str.clone()
            };
            if let Some(bindings) = match_pattern(pattern, &candidate) {
                results.push((candidate, bindings));
            }
        }
    }
    results
}

/// Extract the list of wildcard names from a pattern, in order of first occurrence.
pub fn wildcard_names(pattern: &Pattern) -> Vec<String> {
    let mut names = Vec::new();
    for seg in &pattern.segments {
        if let PatternSegment::Wildcard { name, .. } = seg {
            if !names.contains(name) {
                names.push(name.clone());
            }
        }
    }
    names
}

#[derive(Debug, thiserror::Error)]
pub enum PatternError {
    #[error("unterminated wildcard (missing closing '}}')")]
    UnterminatedWildcard,
    #[error("empty wildcard name")]
    EmptyWildcardName,
    #[error("unknown wildcard kind: {0}")]
    UnknownWildcardKind(String),
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_pattern() {
        let pat = parse_pattern("{X}.txt").unwrap();
        let b = match_pattern(&pat, "hello.txt").unwrap();
        assert_eq!(b["X"], "hello");
    }

    #[test]
    fn test_multi_wildcard() {
        let pat = parse_pattern("align-{X}-{Y}.bam").unwrap();
        let b = match_pattern(&pat, "align-sample1-hg38.bam").unwrap();
        assert_eq!(b["X"], "sample1");
        assert_eq!(b["Y"], "hg38");
    }

    #[test]
    fn test_no_match() {
        let pat = parse_pattern("{X}.txt").unwrap();
        assert!(match_pattern(&pat, "hello.bam").is_none());
    }

    #[test]
    fn test_consistent_binding() {
        // Same variable used twice must bind to same value
        let pat = parse_pattern("{X}-{X}.txt").unwrap();
        let b = match_pattern(&pat, "foo-foo.txt").unwrap();
        assert_eq!(b["X"], "foo");

        // Inconsistent should fail
        assert!(match_pattern(&pat, "foo-bar.txt").is_none());
    }

    #[test]
    fn test_segment_no_slash() {
        let pat = parse_pattern("{X}.txt").unwrap();
        // Segment wildcard shouldn't cross path boundaries
        assert!(match_pattern(&pat, "a/b.txt").is_none());
    }

    #[test]
    fn test_any_wildcard_with_slash() {
        let pat = parse_pattern("{X:any}.txt").unwrap();
        let b = match_pattern(&pat, "a/b/c.txt").unwrap();
        assert_eq!(b["X"], "a/b/c");
    }

    #[test]
    fn test_expand_template() {
        let mut bindings = Bindings::new();
        bindings.insert("X".into(), "sample1".into());
        bindings.insert("Y".into(), "hg38".into());

        let result = expand_template("results/{X}-{Y}.bam", &bindings);
        assert_eq!(result, "results/sample1-hg38.bam");
    }

    #[test]
    fn test_expand_template_missing_var() {
        let bindings = Bindings::new();
        let result = expand_template("{X}-{Y}.txt", &bindings);
        assert_eq!(result, "{X}-{Y}.txt");
    }

    #[test]
    fn test_pattern_to_glob() {
        let pat = parse_pattern("data/{patient}-{tissue}.fastq").unwrap();
        assert_eq!(pattern_to_glob(&pat), "data/*-*.fastq");
    }

    #[test]
    fn test_wildcard_names() {
        let pat = parse_pattern("{A}-{B}-{A}.txt").unwrap();
        let names = wildcard_names(&pat);
        assert_eq!(names, vec!["A", "B"]);
    }

    #[test]
    fn test_three_wildcards() {
        let pat = parse_pattern("{A}_{B}_{C}.dat").unwrap();
        let b = match_pattern(&pat, "x_y_z.dat").unwrap();
        assert_eq!(b["A"], "x");
        assert_eq!(b["B"], "y");
        assert_eq!(b["C"], "z");
    }

    #[test]
    fn test_literal_only() {
        let pat = parse_pattern("exact.txt").unwrap();
        assert!(match_pattern(&pat, "exact.txt").is_some());
        assert!(match_pattern(&pat, "other.txt").is_none());
    }

    #[test]
    fn test_adjacent_wildcards() {
        let pat = parse_pattern("{A}{B}.txt").unwrap();
        // With greedy matching and backtracking, this should find a valid split
        let b = match_pattern(&pat, "ab.txt").unwrap();
        // "a" + "b" is one valid split
        assert_eq!(b["A"].len() + b["B"].len(), 2);
    }

    #[test]
    fn test_empty_input_no_match() {
        let pat = parse_pattern("{X}.txt").unwrap();
        assert!(match_pattern(&pat, "").is_none());
    }

    #[test]
    fn test_glob_match_filesystem() {
        let dir = tempfile::tempdir().unwrap();
        std::fs::write(dir.path().join("data-a-1.txt"), "").unwrap();
        std::fs::write(dir.path().join("data-b-2.txt"), "").unwrap();
        std::fs::write(dir.path().join("other.txt"), "").unwrap();

        let pat = parse_pattern("data-{X}-{Y}.txt").unwrap();
        let mut results = glob_match(&pat, dir.path());
        results.sort_by(|a, b| a.0.cmp(&b.0));
        assert_eq!(results.len(), 2);
        assert_eq!(results[0].1["X"], "a");
        assert_eq!(results[0].1["Y"], "1");
        assert_eq!(results[1].1["X"], "b");
        assert_eq!(results[1].1["Y"], "2");
    }
}
