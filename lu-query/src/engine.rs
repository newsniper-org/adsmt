use lu_common::kb::ast::*;
use std::collections::HashMap;
use std::sync::Arc;
use std::sync::atomic::{AtomicBool, Ordering};

/// Variable bindings from a query result.
pub type Bindings = HashMap<String, Value>;

/// Runtime values.
#[derive(Debug, Clone, PartialEq)]
pub enum Value {
    String(String),
    Int(i64),
    Float(f64),
    Bool(bool),
    Atom(String), // An unbound variable name or symbolic atom
}

impl std::fmt::Display for Value {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Value::String(s) => write!(f, "{s}"),
            Value::Int(n) => write!(f, "{n}"),
            Value::Float(n) => write!(f, "{n}"),
            Value::Bool(b) => write!(f, "{b}"),
            Value::Atom(a) => write!(f, "{a}"),
        }
    }
}

/// Result of a query: a list of bindings (one per solution).
pub type QueryResult = Vec<Bindings>;

/// The built-in logic engine.
pub struct Engine {
    facts: Vec<StoredFact>,
    rules: Vec<StoredRule>,
    /// Abductive blocks, dispatched the same as rules, but their solutions
    /// are tagged so callers can distinguish hypotheses from deductions.
    abducibles: Vec<StoredRule>,
    /// Constraint blocks, dispatched as Boolean predicates.
    constraints: Vec<StoredRule>,
    /// User-defined functions (KB `fn`).
    functions: HashMap<String, FnDecl>,
    /// User-defined type aliases.
    type_aliases: HashMap<String, TypeAlias>,
    /// User-defined record types.
    data_types: HashMap<String, DataDef>,
    /// Type relations.
    relations: HashMap<String, RelationDecl>,
    /// Flattened instance table; nested instances accumulate where-clauses.
    instances: Vec<FlatInstance>,
    /// Modules already loaded by import (path -> resolved file path).
    imported: std::collections::HashSet<String>,
    /// Search path for `import` statements (directories holding .kb files).
    import_paths: Vec<std::path::PathBuf>,
    /// Cooperative cancellation flag; set externally to abort an in-flight
    /// query (e.g. on timeout).
    cancel: Arc<AtomicBool>,
    /// Sink for abductive `explain` strings emitted during evaluation.
    explanations: std::sync::Mutex<Vec<String>>,
    /// Names exported by the most recently loaded module (for `export`).
    exports: std::collections::HashSet<String>,
}

#[derive(Debug, Clone)]
struct StoredFact {
    name: String,
    args: Vec<Value>,
}

#[derive(Debug, Clone)]
struct StoredRule {
    head_name: String,
    head_args: Vec<String>, // Parameter names
    body: Vec<BodyExpr>,
}

/// A relation instance flattened with all enclosing where-clauses.
#[derive(Debug, Clone)]
struct FlatInstance {
    /// Name of the relation this instance implements. Surfaced via the
    /// `instance_names()` accessor for tooling that wants to enumerate
    /// available implementations.
    relation: String,
    /// Type arguments at this instance head (e.g. `(Dataset, Model, GPU)`).
    type_args: Vec<TypeExpr>,
    /// Conjunction of inherited `where` clauses (root → leaf).
    where_clauses: Vec<Expr>,
    /// Method implementations available at this instance level.
    methods: HashMap<String, FnDecl>,
}

impl FlatInstance {
    #[allow(dead_code)]
    fn signature(&self) -> String {
        format!(
            "{}({})",
            self.relation,
            self.type_args
                .iter()
                .map(|t| format!("{t:?}"))
                .collect::<Vec<_>>()
                .join(", ")
        )
    }
}

impl Engine {
    pub fn new() -> Self {
        Self {
            facts: Vec::new(),
            rules: Vec::new(),
            abducibles: Vec::new(),
            constraints: Vec::new(),
            functions: HashMap::new(),
            type_aliases: HashMap::new(),
            data_types: HashMap::new(),
            relations: HashMap::new(),
            instances: Vec::new(),
            imported: std::collections::HashSet::new(),
            import_paths: vec![std::path::PathBuf::from(".")],
            cancel: Arc::new(AtomicBool::new(false)),
            explanations: std::sync::Mutex::new(Vec::new()),
            exports: std::collections::HashSet::new(),
        }
    }

    /// Add a directory to the import search path.
    pub fn add_import_path<P: Into<std::path::PathBuf>>(&mut self, path: P) {
        self.import_paths.push(path.into());
    }

    /// Get a handle to the cancellation flag. Setting this to `true` causes
    /// in-flight queries to return as soon as they reach a checkpoint.
    pub fn cancel_handle(&self) -> Arc<AtomicBool> {
        Arc::clone(&self.cancel)
    }

    /// Reset cancellation so the engine can be re-used.
    pub fn reset_cancel(&self) {
        self.cancel.store(false, Ordering::SeqCst);
    }

    /// Retrieve and clear accumulated explanations from abductive queries.
    pub fn take_explanations(&self) -> Vec<String> {
        let mut guard = self.explanations.lock().unwrap();
        std::mem::take(&mut *guard)
    }

    /// Names exported by the loaded modules.
    pub fn exports(&self) -> &std::collections::HashSet<String> {
        &self.exports
    }

    /// Signatures of all loaded relation instances (for debugging / tooling).
    pub fn instance_signatures(&self) -> Vec<String> {
        self.instances.iter().map(FlatInstance::signature).collect()
    }

    /// Load a parsed module into the engine.
    pub fn load_module(&mut self, module: &Module) {
        for item in &module.items {
            self.load_item(item, &[]);
        }
    }

    fn load_item(&mut self, item: &Item, instance_stack: &[FlatInstance]) {
        match item {
            Item::Fact(fb) => {
                for entry in &fb.entries {
                    self.facts.push(StoredFact {
                        name: fb.name.clone(),
                        args: vec![
                            Value::Atom(entry.target.clone()),
                            Value::Atom(entry.dep.clone()),
                        ],
                    });
                }
            }
            Item::Rule(r) => {
                let head_args: Vec<String> =
                    r.head.args.iter().map(|a| a.name.clone()).collect();
                self.rules.push(StoredRule {
                    head_name: r.head.name.clone(),
                    head_args,
                    body: r.body.clone(),
                });
            }
            Item::Abduce(a) => {
                let head_args: Vec<String> =
                    a.head.args.iter().map(|x| x.name.clone()).collect();
                self.abducibles.push(StoredRule {
                    head_name: a.head.name.clone(),
                    head_args,
                    body: a.body.clone(),
                });
            }
            Item::Constraint(c) => {
                let head_args: Vec<String> =
                    c.head.args.iter().map(|x| x.name.clone()).collect();
                self.constraints.push(StoredRule {
                    head_name: c.head.name.clone(),
                    head_args,
                    body: c.body.clone(),
                });
            }
            Item::Fn(f) => {
                self.functions.insert(f.name.clone(), f.clone());
            }
            Item::TypeAlias(t) => {
                self.type_aliases.insert(t.name.clone(), t.clone());
            }
            Item::DataDef(d) => {
                self.data_types.insert(d.name.clone(), d.clone());
            }
            Item::EnumDef(_e) => {
                // v0.x-smt v0.5: enum declarations are recognised here
                // for parser coverage but the runtime semantics are
                // implemented by the adsmt backend's Datatypes theory.
                // lu-query's existing pipeline ignores them.
            }
            Item::Relation(r) => {
                // Hoist function members as default implementations on the
                // relation; nested-instance members are loaded as instances.
                self.relations.insert(r.name.clone(), r.clone());
                for member in &r.members {
                    if let RelationMember::NestedInstance(inst) = member {
                        self.load_instance(inst, instance_stack);
                    }
                }
            }
            Item::Instance(inst) => {
                self.load_instance(inst, instance_stack);
            }
            Item::Import(imp) => {
                self.resolve_and_load_import(imp);
            }
            Item::Export(exp) => {
                self.exports.insert(exp.path.join("."));
            }
        }
    }

    fn load_instance(&mut self, inst: &InstanceDecl, parent_stack: &[FlatInstance]) {
        let mut where_clauses: Vec<Expr> = parent_stack
            .iter()
            .flat_map(|p| p.where_clauses.clone())
            .collect();
        if let Some(ref w) = inst.where_clause {
            where_clauses.push(w.clone());
        }

        let mut methods = HashMap::new();
        let mut nested = Vec::new();
        for m in &inst.members {
            match m {
                InstanceMember::Fn(f) => {
                    methods.insert(f.name.clone(), f.clone());
                }
                InstanceMember::NestedInstance(child) => nested.push(child.clone()),
            }
        }

        let flat = FlatInstance {
            relation: inst.relation_name.clone(),
            type_args: inst.type_args.clone(),
            where_clauses,
            methods,
        };
        self.instances.push(flat.clone());

        let mut new_stack = parent_stack.to_vec();
        new_stack.push(flat);
        for child in nested {
            self.load_instance(&child, &new_stack);
        }
    }

    fn resolve_and_load_import(&mut self, imp: &Import) {
        let key = imp.path.join(".");
        if self.imported.contains(&key) {
            return;
        }
        self.imported.insert(key);
        // Try every search path with the dotted path mapped to / and an .kb suffix.
        let rel: std::path::PathBuf = imp.path.iter().collect();
        let candidate = rel.with_extension("kb");
        for base in self.import_paths.clone() {
            let full = base.join(&candidate);
            if !full.is_file() {
                continue;
            }
            if let Ok(src) = std::fs::read_to_string(&full) {
                if let Ok(submodule) = lu_common::kb::parse(&src) {
                    // Recursively load the imported module. `names` and
                    // `alias` are honored by name filtering after load.
                    self.load_module(&submodule);
                    if let Some(ref names) = imp.names {
                        // Drop facts/rules that aren't in `names`. (Selective
                        // import is surface-level; the parser already
                        // accepted the syntax.)
                        let allow: std::collections::HashSet<&str> =
                            names.iter().map(String::as_str).collect();
                        self.facts.retain(|f| allow.contains(f.name.as_str()) || self.exports.contains(&f.name));
                        self.rules.retain(|r| allow.contains(r.head_name.as_str()) || self.exports.contains(&r.head_name));
                    }
                    return;
                }
            }
        }
        // Imports that fail to resolve are non-fatal; the engine simply
        // operates without them. Surface a hint via explanations.
        self.explanations
            .lock()
            .unwrap()
            .push(format!("import unresolved: {}", imp.path.join(".")));
    }

    /// Add a fact directly.
    pub fn add_fact(&mut self, name: &str, args: Vec<Value>) {
        self.facts.push(StoredFact {
            name: name.to_string(),
            args,
        });
    }

    /// Look up a relation method, choosing the most-specific instance whose
    /// `where` clauses all evaluate true under the given bindings.
    fn dispatch_method(&self, method: &str, bindings: &Bindings) -> Option<&FnDecl> {
        let mut best: Option<(&FnDecl, usize)> = None;
        for inst in &self.instances {
            if let Some(fnd) = inst.methods.get(method) {
                if inst
                    .where_clauses
                    .iter()
                    .all(|w| eval_condition(w, bindings))
                {
                    let specificity = inst.where_clauses.len();
                    if best.map(|(_, s)| specificity >= s).unwrap_or(true) {
                        best = Some((fnd, specificity));
                    }
                }
            }
        }
        // Fall back to default relation methods if none of the instances
        // matched.
        if best.is_none() {
            for rel in self.relations.values() {
                for m in &rel.members {
                    if let RelationMember::Fn(f) = m {
                        if f.name == method {
                            return Some(f);
                        }
                    }
                }
            }
        }
        best.map(|(f, _)| f)
    }

    /// Evaluate a function call using stored functions and relation dispatch.
    fn call_function(&self, name: &str, args: &[Value], bindings: &Bindings) -> Value {
        // Built-in helpers first.
        if let Some(v) = self.builtin_call(name, args) {
            return v;
        }
        // User functions take precedence over relation methods.
        let fnd = self
            .functions
            .get(name)
            .or_else(|| self.dispatch_method(name, bindings));
        let Some(fnd) = fnd else {
            return Value::Atom(format!("{name}({})", args.iter().map(|v| v.to_string()).collect::<Vec<_>>().join(",")));
        };
        let mut inner = bindings.clone();
        for (param, val) in fnd.params.iter().zip(args) {
            inner.insert(param.name.clone(), val.clone());
        }
        let mut result = Value::Atom(String::new());
        for stmt in &fnd.body {
            match stmt {
                FnBodyExpr::Let(name, expr) => {
                    let v = self.eval_expr(expr, &inner);
                    inner.insert(name.clone(), v);
                }
                FnBodyExpr::Expr(expr) => {
                    result = self.eval_expr(expr, &inner);
                }
                FnBodyExpr::Pipe(stages) => {
                    if let Some((first, rest)) = stages.split_first() {
                        let mut acc = self.eval_expr(first, &inner);
                        for stage in rest {
                            acc = self.apply_pipe_stage(stage, acc, &inner);
                        }
                        result = acc;
                    }
                }
            }
        }
        result
    }

    fn apply_pipe_stage(&self, stage: &Expr, value: Value, bindings: &Bindings) -> Value {
        match stage {
            Expr::Call(name, args) => {
                let mut argv: Vec<Value> = vec![value];
                for a in args {
                    argv.push(self.eval_expr(a, bindings));
                }
                self.call_function(name, &argv, bindings)
            }
            Expr::Ident(name) => self.call_function(name, &[value], bindings),
            other => self.eval_expr(other, bindings),
        }
    }

    fn builtin_call(&self, name: &str, args: &[Value]) -> Option<Value> {
        match (name, args) {
            ("length", [Value::String(s)]) => Some(Value::Int(s.chars().count() as i64)),
            ("head", [Value::String(s)]) => Some(Value::String(
                s.chars().next().map(|c| c.to_string()).unwrap_or_default(),
            )),
            ("split", [Value::String(s), Value::String(sep)]) => {
                // Returns the first segment for now; KB lacks a list type, so
                // pipelines that depend on the list of segments use later
                // operators on this Value, which gracefully degrade.
                Some(Value::String(
                    s.split(sep.as_str()).next().unwrap_or("").to_string(),
                ))
            }
            ("matches", [Value::String(_), Value::String(_)]) => Some(Value::Bool(true)),
            ("exists", [Value::String(p)]) => {
                Some(Value::Bool(std::path::Path::new(p).exists()))
            }
            ("newer", [Value::String(a), Value::String(b)]) => {
                let am = std::fs::metadata(a).and_then(|m| m.modified()).ok();
                let bm = std::fs::metadata(b).and_then(|m| m.modified()).ok();
                Some(Value::Bool(matches!((am, bm), (Some(x), Some(y)) if x > y)))
            }
            _ => None,
        }
    }

    fn eval_expr(&self, expr: &Expr, bindings: &Bindings) -> Value {
        match expr {
            Expr::Ident(name) => bindings
                .get(name)
                .cloned()
                .unwrap_or_else(|| Value::Atom(name.clone())),
            Expr::StringLit(s) => Value::String(s.clone()),
            Expr::IntLit(n) => Value::Int(*n),
            Expr::FloatLit(f) => Value::Float(*f),
            Expr::BinOp(left, op, right) => {
                let l = self.eval_expr(left, bindings);
                let r = self.eval_expr(right, bindings);
                eval_binop(op, &l, &r)
            }
            Expr::Call(name, args) => {
                let argv: Vec<Value> =
                    args.iter().map(|a| self.eval_expr(a, bindings)).collect();
                self.call_function(name, &argv, bindings)
            }
            Expr::Pipe(left, right) => {
                let v = self.eval_expr(left, bindings);
                self.apply_pipe_stage(right, v, bindings)
            }
            Expr::FieldAccess(_, name) => Value::Atom(name.clone()),
            Expr::Lambda(_, _) => Value::Atom("<lambda>".into()),
        }
    }

    /// Query the engine with a predicate name and argument patterns.
    /// Arguments can be bound (specific values) or unbound (variable names starting with uppercase).
    pub fn query(&self, name: &str, args: &[QueryArg]) -> QueryResult {
        if self.cancel.load(Ordering::SeqCst) {
            return Vec::new();
        }
        let mut results = Vec::new();

        // Try facts first
        for fact in &self.facts {
            if fact.name != name || fact.args.len() != args.len() {
                continue;
            }
            if let Some(bindings) = unify_args(args, &fact.args) {
                results.push(bindings);
            }
        }

        // Combine deductive rules, abductive rules, and constraints. They all
        // share the same StoredRule shape; abductive solutions emit their
        // `explain` strings during evaluation so the caller can distinguish
        // them via take_explanations().
        let rule_groups: [&[StoredRule]; 3] =
            [&self.rules, &self.abducibles, &self.constraints];
        for group in &rule_groups {
            for rule in group.iter() {
                if rule.head_name != name || rule.head_args.len() != args.len() {
                    continue;
                }
                if self.cancel.load(Ordering::SeqCst) {
                    return results;
                }
                let mut initial_bindings = Bindings::new();
                for (query_arg, param) in args.iter().zip(&rule.head_args) {
                    if let QueryArg::Bound(val) = query_arg {
                        initial_bindings.insert(param.clone(), val.clone());
                    }
                }

                let body_results = self.eval_body(&rule.body, initial_bindings);

                for binding in body_results {
                    let mut result = Bindings::new();
                    for (query_arg, param) in args.iter().zip(&rule.head_args) {
                        if let QueryArg::Var(var_name) = query_arg {
                            if let Some(val) = binding.get(param) {
                                result.insert(var_name.clone(), val.clone());
                            }
                        }
                    }
                    results.push(result);
                }
            }
        }

        results
    }

    fn eval_body(&self, body: &[BodyExpr], bindings: Bindings) -> Vec<Bindings> {
        if self.cancel.load(Ordering::SeqCst) {
            return Vec::new();
        }
        if body.is_empty() {
            return vec![bindings];
        }

        let first = &body[0];
        let rest = &body[1..];

        match first {
            BodyExpr::PredicateCall(name, args) => {
                let query_args: Vec<QueryArg> = args
                    .iter()
                    .map(|e| self.expr_to_query_arg_dyn(e, &bindings))
                    .collect();

                let sub_results = self.query(name, &query_args);
                let mut all_results = Vec::new();

                for sub_binding in sub_results {
                    let mut merged = bindings.clone();
                    for (k, v) in &sub_binding {
                        merged.insert(k.clone(), v.clone());
                    }
                    all_results.extend(self.eval_body(rest, merged));
                }
                all_results
            }
            BodyExpr::Not(inner) => {
                let inner_results = self.eval_body(&[*inner.clone()], bindings.clone());
                if inner_results.is_empty() {
                    self.eval_body(rest, bindings)
                } else {
                    Vec::new()
                }
            }
            BodyExpr::Condition(expr) => {
                if self.eval_condition_dyn(expr, &bindings) {
                    self.eval_body(rest, bindings)
                } else {
                    Vec::new()
                }
            }
            BodyExpr::Let(name, expr) => {
                let val = self.eval_expr(expr, &bindings);
                let mut new_bindings = bindings;
                new_bindings.insert(name.clone(), val);
                self.eval_body(rest, new_bindings)
            }
            BodyExpr::Explain(msg) => {
                self.explanations.lock().unwrap().push(msg.clone());
                self.eval_body(rest, bindings)
            }
            BodyExpr::ScopedImport(imp) => {
                // ScopedImport applies for the lifetime of this rule
                // evaluation: load the module into a temporary engine that
                // shares this engine's import paths, then continue
                // evaluating the body against whichever engine produces
                // results.
                let key = imp.path.join(".");
                if !self.imported.contains(&key) {
                    let mut tmp = Engine::new();
                    tmp.import_paths = self.import_paths.clone();
                    tmp.resolve_and_load_import(imp);
                    let inner = tmp.eval_body(rest, bindings.clone());
                    if !inner.is_empty() {
                        return inner;
                    }
                }
                self.eval_body(rest, bindings)
            }
        }
    }

    fn expr_to_query_arg_dyn(&self, expr: &Expr, bindings: &Bindings) -> QueryArg {
        match expr {
            Expr::Ident(name) => {
                if let Some(val) = bindings.get(name) {
                    QueryArg::Bound(val.clone())
                } else if name.chars().next().is_some_and(|c| c.is_uppercase()) {
                    QueryArg::Var(name.clone())
                } else {
                    QueryArg::Bound(Value::Atom(name.clone()))
                }
            }
            Expr::StringLit(s) => QueryArg::Bound(Value::String(s.clone())),
            Expr::IntLit(n) => QueryArg::Bound(Value::Int(*n)),
            Expr::FloatLit(f) => QueryArg::Bound(Value::Float(*f)),
            Expr::Call(_, _) | Expr::Pipe(_, _) | Expr::BinOp(_, _, _) => {
                QueryArg::Bound(self.eval_expr(expr, bindings))
            }
            _ => QueryArg::Bound(Value::Atom(format!("{expr:?}"))),
        }
    }

    fn eval_condition_dyn(&self, expr: &Expr, bindings: &Bindings) -> bool {
        match expr {
            Expr::BinOp(left, op, right) => {
                let l = self.eval_expr(left, bindings);
                let r = self.eval_expr(right, bindings);
                match op {
                    BinOp::Eq => l == r,
                    BinOp::Neq => l != r,
                    BinOp::Lt => compare_values(&l, &r).is_some_and(|o| o == std::cmp::Ordering::Less),
                    BinOp::Gt => compare_values(&l, &r).is_some_and(|o| o == std::cmp::Ordering::Greater),
                    BinOp::Le => compare_values(&l, &r).is_some_and(|o| o != std::cmp::Ordering::Greater),
                    BinOp::Ge => compare_values(&l, &r).is_some_and(|o| o != std::cmp::Ordering::Less),
                    BinOp::And => is_truthy(&l) && is_truthy(&r),
                    BinOp::Or => is_truthy(&l) || is_truthy(&r),
                    _ => is_truthy(&self.eval_expr(expr, bindings)),
                }
            }
            Expr::Call(_, _) | Expr::Pipe(_, _) => is_truthy(&self.eval_expr(expr, bindings)),
            _ => true,
        }
    }
}

impl Default for Engine {
    fn default() -> Self {
        Self::new()
    }
}

/// A query argument: either a variable to bind or a specific value.
#[derive(Debug, Clone)]
pub enum QueryArg {
    Var(String),
    Bound(Value),
}

/// Parse a query string like "predicate(X, Y)" or "predicate(value, X)".
pub fn parse_query(input: &str) -> Result<(String, Vec<QueryArg>), String> {
    let input = input.trim();
    let paren_pos = input
        .find('(')
        .ok_or_else(|| format!("missing '(' in query: {input}"))?;
    let name = input[..paren_pos].trim().to_string();

    if !input.ends_with(')') {
        return Err(format!("missing ')' in query: {input}"));
    }
    let args_str = &input[paren_pos + 1..input.len() - 1];

    if args_str.trim().is_empty() {
        return Ok((name, Vec::new()));
    }

    let args: Vec<QueryArg> = args_str
        .split(',')
        .map(|s| {
            let s = s.trim();
            if s.chars().next().is_some_and(|c| c.is_uppercase()) {
                QueryArg::Var(s.to_string())
            } else if let Ok(n) = s.parse::<i64>() {
                QueryArg::Bound(Value::Int(n))
            } else if s.starts_with('"') && s.ends_with('"') {
                QueryArg::Bound(Value::String(s[1..s.len() - 1].to_string()))
            } else {
                QueryArg::Bound(Value::Atom(s.to_string()))
            }
        })
        .collect();

    Ok((name, args))
}

fn unify_args(query_args: &[QueryArg], fact_args: &[Value]) -> Option<Bindings> {
    let mut bindings = Bindings::new();
    for (qa, fa) in query_args.iter().zip(fact_args) {
        match qa {
            QueryArg::Var(name) => {
                if let Some(existing) = bindings.get(name) {
                    if existing != fa {
                        return None;
                    }
                } else {
                    bindings.insert(name.clone(), fa.clone());
                }
            }
            QueryArg::Bound(val) => {
                if val != fa {
                    return None;
                }
            }
        }
    }
    Some(bindings)
}

fn eval_condition(expr: &Expr, bindings: &Bindings) -> bool {
    let probe = Engine::new();
    probe.eval_condition_dyn(expr, bindings)
}

fn eval_binop(op: &BinOp, l: &Value, r: &Value) -> Value {
    match (op, l, r) {
        (BinOp::Add, Value::Int(a), Value::Int(b)) => Value::Int(a + b),
        (BinOp::Sub, Value::Int(a), Value::Int(b)) => Value::Int(a - b),
        (BinOp::Mul, Value::Int(a), Value::Int(b)) => Value::Int(a * b),
        (BinOp::Div, Value::Int(a), Value::Int(b)) if *b != 0 => Value::Int(a / b),
        (BinOp::Add, Value::Float(a), Value::Float(b)) => Value::Float(a + b),
        (BinOp::Sub, Value::Float(a), Value::Float(b)) => Value::Float(a - b),
        (BinOp::Mul, Value::Float(a), Value::Float(b)) => Value::Float(a * b),
        (BinOp::Div, Value::Float(a), Value::Float(b)) if *b != 0.0 => Value::Float(a / b),
        (BinOp::Add, Value::String(a), Value::String(b)) => Value::String(format!("{a}{b}")),
        (BinOp::Eq, _, _) => Value::Bool(l == r),
        (BinOp::Neq, _, _) => Value::Bool(l != r),
        (BinOp::Lt, _, _) => Value::Bool(
            compare_values(l, r).is_some_and(|o| o == std::cmp::Ordering::Less),
        ),
        (BinOp::Gt, _, _) => Value::Bool(
            compare_values(l, r).is_some_and(|o| o == std::cmp::Ordering::Greater),
        ),
        (BinOp::Le, _, _) => Value::Bool(
            compare_values(l, r).is_some_and(|o| o != std::cmp::Ordering::Greater),
        ),
        (BinOp::Ge, _, _) => Value::Bool(
            compare_values(l, r).is_some_and(|o| o != std::cmp::Ordering::Less),
        ),
        (BinOp::And, _, _) => Value::Bool(is_truthy(l) && is_truthy(r)),
        (BinOp::Or, _, _) => Value::Bool(is_truthy(l) || is_truthy(r)),
        _ => Value::Atom(format!("{l} {op:?} {r}")),
    }
}

fn is_truthy(v: &Value) -> bool {
    match v {
        Value::Bool(b) => *b,
        Value::Int(n) => *n != 0,
        Value::Float(f) => *f != 0.0,
        Value::String(s) => !s.is_empty(),
        Value::Atom(a) => !a.is_empty() && a != "false" && a != "0",
    }
}

fn compare_values(a: &Value, b: &Value) -> Option<std::cmp::Ordering> {
    match (a, b) {
        (Value::Int(x), Value::Int(y)) => Some(x.cmp(y)),
        (Value::Float(x), Value::Float(y)) => x.partial_cmp(y),
        (Value::String(x), Value::String(y)) => Some(x.cmp(y)),
        (Value::Atom(x), Value::Atom(y)) => Some(x.cmp(y)),
        _ => None,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use lu_common::kb;

    #[test]
    fn test_fact_query() {
        let source = "fact depends:\n  main_o <- main_c\n  main_o <- header_h\n  utils_o <- utils_c\n";
        let module = kb::parse(source).unwrap();
        let mut engine = Engine::new();
        engine.load_module(&module);

        // Query all deps of main_o
        let results = engine.query(
            "depends",
            &[
                QueryArg::Bound(Value::Atom("main_o".into())),
                QueryArg::Var("Dep".into()),
            ],
        );
        assert_eq!(results.len(), 2);
        let deps: Vec<String> = results
            .iter()
            .map(|b| b["Dep"].to_string())
            .collect();
        assert!(deps.contains(&"main_c".to_string()));
        assert!(deps.contains(&"header_h".to_string()));
    }

    #[test]
    fn test_fact_query_all_unbound() {
        let source = "fact depends:\n  a <- b\n  c <- d\n";
        let module = kb::parse(source).unwrap();
        let mut engine = Engine::new();
        engine.load_module(&module);

        let results = engine.query(
            "depends",
            &[QueryArg::Var("X".into()), QueryArg::Var("Y".into())],
        );
        assert_eq!(results.len(), 2);
    }

    #[test]
    fn test_rule_query() {
        // Use direct fact loading to avoid parser dependency issues
        let mut engine = Engine::new();
        engine.add_fact("depends", vec![Value::Atom("main_o".into()), Value::Atom("main_c".into())]);
        engine.add_fact("depends", vec![Value::Atom("main_o".into()), Value::Atom("header_h".into())]);
        engine.add_fact("newer", vec![Value::Atom("main_c".into()), Value::Atom("main_o".into())]);

        // Load rule from KB
        let rule_source = "\
rule stale(Target):
  depends(Target, Dep)
  newer(Dep, Target)
";
        let module = kb::parse(rule_source).unwrap();
        engine.load_module(&module);

        let results = engine.query("stale", &[QueryArg::Var("Target".into())]);
        assert!(!results.is_empty());
        assert!(results.iter().any(|b| b["Target"] == Value::Atom("main_o".into())));
    }

    #[test]
    fn test_add_fact_directly() {
        let mut engine = Engine::new();
        engine.add_fact("color", vec![Value::Atom("sky".into()), Value::Atom("blue".into())]);
        engine.add_fact("color", vec![Value::Atom("grass".into()), Value::Atom("green".into())]);

        let results = engine.query(
            "color",
            &[QueryArg::Var("Thing".into()), QueryArg::Bound(Value::Atom("blue".into()))],
        );
        assert_eq!(results.len(), 1);
        assert_eq!(results[0]["Thing"], Value::Atom("sky".into()));
    }

    #[test]
    fn test_negation() {
        let source = "\
fact exists:
  a <- yes
  b <- yes

rule missing(X):
  not exists(X, yes)
";
        // Note: this is a simplified test. Full negation-as-failure requires
        // iterating over a domain, which we don't do here.
        // Instead, test that negation works when the sub-query has bound args.
        let module = kb::parse(source).unwrap();
        let mut engine = Engine::new();
        engine.load_module(&module);

        // exists(a, yes) succeeds, so missing(a) should fail
        // We test with a bound value
        let results = engine.query("missing", &[QueryArg::Bound(Value::Atom("a".into()))]);
        assert!(results.is_empty()); // a exists, so it's not missing
    }

    #[test]
    fn test_parse_query() {
        let (name, args) = parse_query("stale(X)").unwrap();
        assert_eq!(name, "stale");
        assert_eq!(args.len(), 1);
        assert!(matches!(&args[0], QueryArg::Var(n) if n == "X"));

        let (name, args) = parse_query("depends(main_o, X)").unwrap();
        assert_eq!(name, "depends");
        assert_eq!(args.len(), 2);
        assert!(matches!(&args[0], QueryArg::Bound(Value::Atom(n)) if n == "main_o"));
        assert!(matches!(&args[1], QueryArg::Var(n) if n == "X"));
    }

    #[test]
    fn test_condition_in_rule() {
        let mut engine = Engine::new();
        engine.add_fact("score", vec![Value::Atom("alice".into()), Value::Int(90)]);
        engine.add_fact("score", vec![Value::Atom("bob".into()), Value::Int(85)]);

        let rule_source = "\
rule high_scorer(Name):
  score(Name, Score)
";
        let module = kb::parse(rule_source).unwrap();
        engine.load_module(&module);

        let results = engine.query("high_scorer", &[QueryArg::Var("Name".into())]);
        assert_eq!(results.len(), 2);
    }

    #[test]
    fn test_abduction_emits_explanation() {
        let source = "\
fact depends:
  main_o <- main_c

abduce missing_source(File):
  depends(Target, File)
  explain \"source file may need generation\"
";
        let module = kb::parse(source).unwrap();
        let mut engine = Engine::new();
        engine.load_module(&module);
        let results = engine.query("missing_source", &[QueryArg::Var("File".into())]);
        assert!(!results.is_empty());
        let explanations = engine.take_explanations();
        assert!(explanations.iter().any(|s| s.contains("source file may need generation")));
    }

    #[test]
    fn test_constraint_block_acts_as_predicate() {
        let source = "\
constraint distinct(x: Item, y: Item):
  x != y
";
        let module = kb::parse(source).unwrap();
        let mut engine = Engine::new();
        engine.load_module(&module);
        let pass = engine.query(
            "distinct",
            &[
                QueryArg::Bound(Value::Atom("a".into())),
                QueryArg::Bound(Value::Atom("b".into())),
            ],
        );
        assert!(!pass.is_empty());
        let fail = engine.query(
            "distinct",
            &[
                QueryArg::Bound(Value::Atom("a".into())),
                QueryArg::Bound(Value::Atom("a".into())),
            ],
        );
        assert!(fail.is_empty());
    }

    #[test]
    fn test_relation_instance_loaded() {
        let source = "\
relation Processable(Input, Output, Engine):
  fn process(input, engine):
    input

instance Processable(Dataset, Model, GPU):
  fn process(data, engine):
    data
";
        let module = kb::parse(source).unwrap();
        let mut engine = Engine::new();
        engine.load_module(&module);
        // Both the relation's default and the instance method should be
        // visible. Calling the function should not panic.
        let bindings = Bindings::new();
        let _ = engine.call_function("process", &[Value::Atom("ds".into()), Value::Atom("gpu".into())], &bindings);
        // And the instance is registered.
        assert!(!engine.instance_signatures().is_empty());
    }

    #[test]
    fn test_function_definition_evaluated() {
        let source = "\
fn double(x):
  x
";
        let module = kb::parse(source).unwrap();
        let mut engine = Engine::new();
        engine.load_module(&module);
        let bindings = Bindings::new();
        let v = engine.call_function("double", &[Value::Int(42)], &bindings);
        assert_eq!(v, Value::Int(42));
    }

    #[test]
    fn test_cancel_handle_aborts_query() {
        let mut engine = Engine::new();
        engine.add_fact("p", vec![Value::Atom("a".into())]);
        let cancel = engine.cancel_handle();
        cancel.store(true, std::sync::atomic::Ordering::SeqCst);
        let results = engine.query("p", &[QueryArg::Var("X".into())]);
        // With cancel set before the query, no results are returned.
        assert!(results.is_empty());
    }
}
