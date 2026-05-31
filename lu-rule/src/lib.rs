use lu_match::Bindings;
use std::io::{self, BufRead};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum RuleError {
    #[error("IO error: {0}")]
    Io(#[from] io::Error),
    #[error("parse error at line {line}: {msg}")]
    Parse { line: usize, msg: String },
    #[error("no rule matches target: {0}")]
    NoMatch(String),
    #[error("pattern error: {0}")]
    Pattern(#[from] lu_match::PatternError),
}

/// A build rule with pattern, dependencies, recipe, and optional goal.
#[derive(Debug, Clone, serde::Serialize)]
pub struct Rule {
    pub pattern: String,
    pub deps: Vec<String>,
    pub recipe: String,
    pub goal: Option<String>,
}

/// Result of matching a rule against a target.
#[derive(Debug, Clone, serde::Serialize)]
pub struct RuleMatch {
    pub rule_index: usize,
    pub target: String,
    pub bindings: Bindings,
    pub expanded_deps: Vec<String>,
    pub expanded_recipe: String,
}

/// Parse a rule file.
///
/// Format:
/// ```text
/// pattern: align-{X}-{Y}.bam
/// deps: {X}.fa {Y}.fa
/// recipe: align {X}.fa {Y}.fa > align-{X}-{Y}.bam
/// goal: X != Y
/// ---
/// pattern: {base}.o
/// deps: {base}.c
/// recipe: cc -c {base}.c -o {base}.o
/// ```
pub fn parse_rules(input: &str) -> Result<Vec<Rule>, RuleError> {
    let mut rules = Vec::new();
    let mut current = RuleBuilder::new();
    let mut line_num = 0;

    for line in input.lines() {
        line_num += 1;
        let trimmed = line.trim();

        if trimmed.is_empty() || trimmed.starts_with('#') {
            continue;
        }

        if trimmed == "---" {
            if let Some(rule) = current.build(line_num)? {
                rules.push(rule);
            }
            current = RuleBuilder::new();
            continue;
        }

        if let Some(val) = trimmed.strip_prefix("pattern:") {
            current.pattern = Some(val.trim().to_string());
        } else if let Some(val) = trimmed.strip_prefix("deps:") {
            current.deps = Some(val.trim().to_string());
        } else if let Some(val) = trimmed.strip_prefix("recipe:") {
            current.recipe = Some(val.trim().to_string());
        } else if let Some(val) = trimmed.strip_prefix("goal:") {
            current.goal = Some(val.trim().to_string());
        } else {
            return Err(RuleError::Parse {
                line: line_num,
                msg: format!("unexpected line: {trimmed}"),
            });
        }
    }

    // Don't forget the last rule
    if let Some(rule) = current.build(line_num)? {
        rules.push(rule);
    }

    Ok(rules)
}

struct RuleBuilder {
    pattern: Option<String>,
    deps: Option<String>,
    recipe: Option<String>,
    goal: Option<String>,
}

impl RuleBuilder {
    fn new() -> Self {
        Self {
            pattern: None,
            deps: None,
            recipe: None,
            goal: None,
        }
    }

    fn build(self, _line: usize) -> Result<Option<Rule>, RuleError> {
        let pattern = match self.pattern {
            Some(p) => p,
            None => return Ok(None), // Empty builder
        };
        let recipe = self.recipe.unwrap_or_default();
        let deps_str = self.deps.unwrap_or_default();
        let deps: Vec<String> = if deps_str.is_empty() {
            Vec::new()
        } else {
            deps_str.split_whitespace().map(String::from).collect()
        };

        Ok(Some(Rule {
            pattern,
            deps,
            recipe,
            goal: self.goal,
        }))
    }
}

/// Try to match a target against a list of rules.
/// Returns the first match, or all matches if `find_all` is true.
pub fn match_rules(
    rules: &[Rule],
    target: &str,
    backtrack: bool,
) -> Result<Vec<RuleMatch>, RuleError> {
    let mut matches = Vec::new();

    for (i, rule) in rules.iter().enumerate() {
        let pattern = lu_match::parse_pattern(&rule.pattern)?;
        if let Some(bindings) = lu_match::match_pattern(&pattern, target) {
            // Check goal if present
            if let Some(ref goal) = rule.goal {
                if !evaluate_goal(goal, &bindings) {
                    if backtrack {
                        continue; // Try next rule
                    } else {
                        return Err(RuleError::NoMatch(target.into()));
                    }
                }
            }

            let expanded_deps: Vec<String> = rule
                .deps
                .iter()
                .map(|d| lu_match::expand_template(d, &bindings))
                .collect();
            let expanded_recipe = lu_match::expand_template(&rule.recipe, &bindings);

            matches.push(RuleMatch {
                rule_index: i,
                target: target.to_string(),
                bindings,
                expanded_deps,
                expanded_recipe,
            });

            if !backtrack {
                break; // Return first match
            }
        }
    }

    Ok(matches)
}

/// Simple goal evaluation: supports `VAR != VAR` and `VAR == VAR`.
fn evaluate_goal(goal: &str, bindings: &Bindings) -> bool {
    let goal = goal.trim();
    if let Some((left, right)) = goal.split_once("!=") {
        let left = left.trim();
        let right = right.trim();
        let lval = bindings.get(left).map(|s| s.as_str()).unwrap_or(left);
        let rval = bindings.get(right).map(|s| s.as_str()).unwrap_or(right);
        lval != rval
    } else if let Some((left, right)) = goal.split_once("==") {
        let left = left.trim();
        let right = right.trim();
        let lval = bindings.get(left).map(|s| s.as_str()).unwrap_or(left);
        let rval = bindings.get(right).map(|s| s.as_str()).unwrap_or(right);
        lval == rval
    } else {
        true // Unknown goal format, pass through
    }
}

/// Read rules from stdin or file.
pub fn read_rules(path: Option<&std::path::Path>) -> Result<Vec<Rule>, RuleError> {
    let input = if let Some(path) = path {
        std::fs::read_to_string(path)?
    } else {
        let stdin = io::stdin();
        let lines: Vec<String> = stdin.lock().lines().map_while(Result::ok).collect();
        lines.join("\n")
    };
    parse_rules(&input)
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sample_rules() -> Vec<Rule> {
        parse_rules(
            "\
pattern: align-{X}-{Y}.bam
deps: {X}.fa {Y}.fa
recipe: align {X}.fa {Y}.fa > align-{X}-{Y}.bam
goal: X != Y
---
pattern: {base}.o
deps: {base}.c
recipe: cc -c {base}.c -o {base}.o
",
        )
        .unwrap()
    }

    #[test]
    fn test_parse_rules() {
        let rules = sample_rules();
        assert_eq!(rules.len(), 2);
        assert_eq!(rules[0].pattern, "align-{X}-{Y}.bam");
        assert_eq!(rules[0].deps, vec!["{X}.fa", "{Y}.fa"]);
        assert_eq!(rules[1].pattern, "{base}.o");
    }

    #[test]
    fn test_match_alignment_rule() {
        let rules = sample_rules();
        let matches = match_rules(&rules, "align-sample1-hg38.bam", false).unwrap();
        assert_eq!(matches.len(), 1);
        assert_eq!(matches[0].bindings["X"], "sample1");
        assert_eq!(matches[0].bindings["Y"], "hg38");
        assert_eq!(matches[0].expanded_deps, vec!["sample1.fa", "hg38.fa"]);
    }

    #[test]
    fn test_match_c_rule() {
        let rules = sample_rules();
        let matches = match_rules(&rules, "main.o", false).unwrap();
        assert_eq!(matches.len(), 1);
        assert_eq!(matches[0].expanded_deps, vec!["main.c"]);
        assert_eq!(matches[0].expanded_recipe, "cc -c main.c -o main.o");
    }

    #[test]
    fn test_goal_rejection() {
        let rules = sample_rules();
        // X == Y should fail the goal X != Y
        let matches = match_rules(&rules, "align-hg38-hg38.bam", true).unwrap();
        // First rule fails goal, no second rule matches either
        assert!(matches.is_empty());
    }

    #[test]
    fn test_backtrack() {
        let rules = parse_rules(
            "\
pattern: {X}.out
deps: {X}.special
recipe: special_process {X}
goal: X == important
---
pattern: {X}.out
deps: {X}.in
recipe: generic_process {X}
",
        )
        .unwrap();

        // "important.out" should match first rule
        let matches = match_rules(&rules, "important.out", true).unwrap();
        assert_eq!(matches.len(), 2); // Both match with backtrack=true
        assert!(matches[0].expanded_recipe.contains("special_process"));

        // "normal.out" should skip first rule (goal fails), match second
        let matches = match_rules(&rules, "normal.out", true).unwrap();
        assert_eq!(matches.len(), 1);
        assert!(matches[0].expanded_recipe.contains("generic_process"));
    }

    #[test]
    fn test_no_match() {
        let rules = sample_rules();
        let matches = match_rules(&rules, "unknown.xyz", false).unwrap();
        assert!(matches.is_empty());
    }

    #[test]
    fn test_evaluate_goal() {
        let mut bindings = Bindings::new();
        bindings.insert("X".into(), "a".into());
        bindings.insert("Y".into(), "b".into());

        assert!(evaluate_goal("X != Y", &bindings));
        assert!(!evaluate_goal("X == Y", &bindings));
        assert!(evaluate_goal("X == X", &bindings)); // Same var
    }
}
