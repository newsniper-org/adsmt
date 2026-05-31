use std::collections::{HashMap, HashSet, VecDeque};
use thiserror::Error;

#[derive(Debug, Error)]
pub enum DepsError {
    #[error("IO error: {0}")]
    Io(#[from] std::io::Error),
    #[error("parse error at line {line}: {msg}")]
    Parse { line: usize, msg: String },
    #[error("cycle detected involving: {0}")]
    CycleDetected(String),
}

/// A dependency graph: target -> set of dependencies.
#[derive(Debug, Clone, Default)]
pub struct DepGraph {
    edges: HashMap<String, HashSet<String>>,
}

impl DepGraph {
    pub fn new() -> Self {
        Self::default()
    }

    /// Add a dependency: target depends on dep.
    pub fn add(&mut self, target: &str, dep: &str) {
        self.edges
            .entry(target.to_string())
            .or_default()
            .insert(dep.to_string());
        // Ensure dep exists as a node
        self.edges.entry(dep.to_string()).or_default();
    }

    /// Get direct dependencies of a target.
    pub fn deps_of(&self, target: &str) -> Option<&HashSet<String>> {
        self.edges.get(target)
    }

    /// Get all targets in the graph.
    pub fn targets(&self) -> Vec<&str> {
        self.edges.keys().map(|s| s.as_str()).collect()
    }

    /// Compute transitive closure of dependencies for a target.
    pub fn transitive_deps(&self, target: &str) -> HashSet<String> {
        let mut visited = HashSet::new();
        let mut queue = VecDeque::new();

        if let Some(deps) = self.edges.get(target) {
            for dep in deps {
                queue.push_back(dep.clone());
            }
        }

        while let Some(node) = queue.pop_front() {
            if visited.insert(node.clone()) {
                if let Some(deps) = self.edges.get(&node) {
                    for dep in deps {
                        if !visited.contains(dep) {
                            queue.push_back(dep.clone());
                        }
                    }
                }
            }
        }
        visited
    }

    /// Get reverse dependencies: what depends on the given target.
    pub fn reverse_deps(&self, target: &str) -> HashSet<String> {
        let mut result = HashSet::new();
        for (node, deps) in &self.edges {
            if deps.contains(target) {
                result.insert(node.clone());
            }
        }
        result
    }

    /// Topological sort. Returns error on cycle.
    pub fn topological_sort(&self) -> Result<Vec<String>, DepsError> {
        // in_degree = number of deps each target has
        // Build order: things with no deps come first
        let mut in_degree: HashMap<&str, usize> = HashMap::new();
        for (target, deps) in &self.edges {
            *in_degree.entry(target.as_str()).or_insert(0) = deps.len();
            for dep in deps {
                in_degree.entry(dep.as_str()).or_insert(0);
            }
        }

        let mut queue: VecDeque<&str> = in_degree
            .iter()
            .filter(|&(_, &deg)| deg == 0)
            .map(|(&id, _)| id)
            .collect();

        let mut order = Vec::new();
        while let Some(node) = queue.pop_front() {
            order.push(node.to_string());
            // For each target that depends on `node`, decrement their in_degree
            for (target, deps) in &self.edges {
                if deps.contains(node) {
                    let deg = in_degree.get_mut(target.as_str()).unwrap();
                    *deg -= 1;
                    if *deg == 0 {
                        queue.push_back(target.as_str());
                    }
                }
            }
        }

        if order.len() != in_degree.len() {
            let in_cycle = in_degree
                .iter()
                .find(|&(_, &deg)| deg > 0)
                .map(|(&id, _)| id)
                .unwrap_or("unknown");
            return Err(DepsError::CycleDetected(in_cycle.to_string()));
        }

        Ok(order)
    }
}

// === Parsers ===

/// Parse TSV format: `target\tdep` per line.
pub fn parse_tsv(input: &str) -> Result<DepGraph, DepsError> {
    let mut graph = DepGraph::new();
    for (i, line) in input.lines().enumerate() {
        let line = line.trim();
        if line.is_empty() || line.starts_with('#') {
            continue;
        }
        let parts: Vec<&str> = line.split('\t').collect();
        if parts.len() < 2 {
            return Err(DepsError::Parse {
                line: i + 1,
                msg: "expected target<TAB>dep".into(),
            });
        }
        graph.add(parts[0], parts[1]);
    }
    Ok(graph)
}

/// Parse GCC -M dependency output format.
pub fn parse_gcc(input: &str) -> Result<DepGraph, DepsError> {
    let mut graph = DepGraph::new();
    // Join continuation lines
    let joined = input.replace("\\\n", " ");
    for line in joined.lines() {
        let line = line.trim();
        if line.is_empty() {
            continue;
        }
        if let Some((target, deps)) = line.split_once(':') {
            let target = target.trim();
            for dep in deps.split_whitespace() {
                graph.add(target, dep);
            }
        }
    }
    Ok(graph)
}

// === Output formats ===

/// Output as TSV.
pub fn to_tsv(graph: &DepGraph) -> String {
    let mut lines = Vec::new();
    let mut targets: Vec<&str> = graph.edges.keys().map(|s| s.as_str()).collect();
    targets.sort();
    for target in targets {
        if let Some(deps) = graph.edges.get(target) {
            let mut deps: Vec<&str> = deps.iter().map(|s| s.as_str()).collect();
            deps.sort();
            for dep in deps {
                lines.push(format!("{target}\t{dep}"));
            }
        }
    }
    lines.join("\n")
}

/// Output as DOT (Graphviz).
pub fn to_dot(graph: &DepGraph) -> String {
    let mut lines = vec!["digraph deps {".to_string()];
    let mut targets: Vec<&str> = graph.edges.keys().map(|s| s.as_str()).collect();
    targets.sort();
    for target in targets {
        if let Some(deps) = graph.edges.get(target) {
            let mut deps: Vec<&str> = deps.iter().map(|s| s.as_str()).collect();
            deps.sort();
            for dep in deps {
                lines.push(format!("  \"{dep}\" -> \"{target}\";"));
            }
        }
    }
    lines.push("}".to_string());
    lines.join("\n")
}

/// Output as JSON.
pub fn to_json(graph: &DepGraph) -> String {
    let mut map: serde_json::Map<String, serde_json::Value> = serde_json::Map::new();
    let mut targets: Vec<&str> = graph.edges.keys().map(|s| s.as_str()).collect();
    targets.sort();
    for target in targets {
        if let Some(deps) = graph.edges.get(target) {
            let mut deps: Vec<&str> = deps.iter().map(|s| s.as_str()).collect();
            deps.sort();
            map.insert(
                target.to_string(),
                serde_json::Value::Array(
                    deps.iter()
                        .map(|d| serde_json::Value::String(d.to_string()))
                        .collect(),
                ),
            );
        }
    }
    serde_json::to_string_pretty(&map).unwrap_or_default()
}

/// Output as lu-par taskfile format: `ID\tDEPS\tCOMMAND`.
/// Command is a placeholder `make <target>`.
pub fn to_taskfile(graph: &DepGraph) -> Result<String, DepsError> {
    let order = graph.topological_sort()?;
    let mut lines = Vec::new();
    for target in &order {
        let deps = graph
            .deps_of(target)
            .map(|d| {
                let mut v: Vec<&str> = d.iter().map(|s| s.as_str()).collect();
                v.sort();
                v.join(",")
            })
            .unwrap_or_default();
        lines.push(format!("{target}\t{deps}\tmake {target}"));
    }
    Ok(lines.join("\n"))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_dep_graph_basic() {
        let mut g = DepGraph::new();
        g.add("main.o", "main.c");
        g.add("main.o", "header.h");

        let deps = g.deps_of("main.o").unwrap();
        assert!(deps.contains("main.c"));
        assert!(deps.contains("header.h"));
    }

    #[test]
    fn test_transitive_deps() {
        let mut g = DepGraph::new();
        g.add("app", "main.o");
        g.add("main.o", "main.c");
        g.add("main.o", "header.h");

        let trans = g.transitive_deps("app");
        assert!(trans.contains("main.o"));
        assert!(trans.contains("main.c"));
        assert!(trans.contains("header.h"));
    }

    #[test]
    fn test_reverse_deps() {
        let mut g = DepGraph::new();
        g.add("main.o", "header.h");
        g.add("utils.o", "header.h");

        let rev = g.reverse_deps("header.h");
        assert!(rev.contains("main.o"));
        assert!(rev.contains("utils.o"));
    }

    #[test]
    fn test_topological_sort() {
        let mut g = DepGraph::new();
        g.add("app", "main.o");
        g.add("main.o", "main.c");

        let order = g.topological_sort().unwrap();
        let pos_c = order.iter().position(|x| x == "main.c").unwrap();
        let pos_o = order.iter().position(|x| x == "main.o").unwrap();
        let pos_app = order.iter().position(|x| x == "app").unwrap();
        assert!(pos_c < pos_o);
        assert!(pos_o < pos_app);
    }

    #[test]
    fn test_cycle_detection() {
        let mut g = DepGraph::new();
        g.add("a", "b");
        g.add("b", "a");
        assert!(g.topological_sort().is_err());
    }

    #[test]
    fn test_parse_tsv() {
        let input = "main.o\tmain.c\nmain.o\theader.h\n";
        let g = parse_tsv(input).unwrap();
        assert!(g.deps_of("main.o").unwrap().contains("main.c"));
    }

    #[test]
    fn test_parse_gcc() {
        let input = "main.o: main.c header.h \\\n  utils.h\n";
        let g = parse_gcc(input).unwrap();
        let deps = g.deps_of("main.o").unwrap();
        assert!(deps.contains("main.c"));
        assert!(deps.contains("header.h"));
        assert!(deps.contains("utils.h"));
    }

    #[test]
    fn test_to_dot() {
        let mut g = DepGraph::new();
        g.add("b", "a");
        let dot = to_dot(&g);
        assert!(dot.contains("\"a\" -> \"b\""));
        assert!(dot.starts_with("digraph deps {"));
    }

    #[test]
    fn test_to_taskfile() {
        let mut g = DepGraph::new();
        g.add("app", "main.o");
        g.add("main.o", "main.c");
        let tf = to_taskfile(&g).unwrap();
        let lines: Vec<&str> = tf.lines().collect();
        // main.c should come before main.o, main.o before app
        let pos_c = lines.iter().position(|l| l.starts_with("main.c")).unwrap();
        let pos_o = lines.iter().position(|l| l.starts_with("main.o")).unwrap();
        let pos_app = lines.iter().position(|l| l.starts_with("app")).unwrap();
        assert!(pos_c < pos_o);
        assert!(pos_o < pos_app);
    }
}
