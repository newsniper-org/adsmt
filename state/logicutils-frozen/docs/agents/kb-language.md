# KB Language Reference

Indentation-sensitive logic + functional language consumed by
`lu-query` and `lu-rule`. This document is normative for parser
authors; for tutorial material see `docs/learning/`.

## Lexical structure

- UTF-8 source. Newlines `\n` or `\r\n`.
- Comments: `#` to end-of-line.
- Indentation: tokenized into `INDENT`/`DEDENT`. Mixing tabs and spaces
  within a single block is an error.
- Identifiers: `[a-zA-Z_][a-zA-Z_0-9]*`. Variables begin with an
  uppercase letter; identifiers beginning with a lowercase letter are
  atoms (or function/predicate names depending on context).
- String literals: `"…"` with `\"`, `\\`, `\n`, `\t` escapes.
- Number literals: integers and floats; floats require a `.`.

### Keywords

```
fact rule abduce constraint fn let type data relation instance
import export where not and or explain as
```

Three of these — `data`, `type`, `as` — are **contextual**: they are
keywords only at the start of an item or declaration. In expression
position they may be used as identifiers.

### Operators

```
==  !=  <=  >=  <  >        comparison
+   -   *   /   %           arithmetic
and or not                   boolean
<-                           fact arrow
->                           function return type / lambda body
=>                           lambda
|>                           pipe
```

## Items

A module is a sequence of items.

```
item ::= fact_block | rule_block | abduce_block | constraint_block
       | type_decl  | data_decl  | fn_decl
       | relation_decl | instance_decl
       | import_decl | export_decl
```

### Fact blocks

```
fact <ident>:
    INDENT
    (<atom> <- <atom> (<atom>)* NEWLINE)+
    DEDENT
```

Each line declares one ground tuple of the predicate.

### Rule blocks

```
rule <ident>(<param>(, <param>)*):
    INDENT
    body_expr+
    DEDENT

body_expr ::= predicate_call
            | "not" predicate_call
            | "let" <ident> "=" expr
            | "if" expr
            | "explain" string_literal
            | scoped_import
```

A rule succeeds when its body succeeds under some unifier extending
the head. Negation is *negation as failure*.

### Abductive blocks

Same shape as rules, but the head is a hypothesis: solving the body
explains the head rather than asserting it. `explain` lines provide
human-readable justifications attached to the abduced binding.

### Constraints

```
constraint <ident>(<typed_param>(, <typed_param>)*):
    INDENT
    body_expr+
    DEDENT
```

Constraints are checked when their referenced variables become
ground; failure prunes the search.

### Functions

```
fn <ident>(<param>(, <param>)*) ( -> <type_expr> )?:
    INDENT
    expr
    DEDENT
```

The body is a single expression. Lambdas: `(args) => expr`. Pipelines:
`a |> f |> g`. Function calls in expression position are
left-associative.

### Types

```
type <ident> = <type_expr>
data <ident>:
    INDENT
    (<field>: <type_expr> (where <expr>)? NEWLINE)+
    DEDENT
```

`type X = Y where E` introduces a refinement; runtime enforcement
depends on the engine.

### Relations and instances

```
relation_decl   ::= "relation" <ident>(<param_list>):
                        INDENT
                        (fn_signature NEWLINE)+
                        DEDENT
instance_decl   ::= "instance" <ident>(<arg_list>) ( "where" <expr> )?:
                        INDENT
                        (fn_decl | instance_decl)+
                        DEDENT
```

Instances may be declared at the top level or nested inside another
instance. A nested instance inherits **every** `where` clause of its
ancestors and adds its own. Multi-parameter dispatch chooses the most
specific instance for which all `where` clauses are satisfied.

### Imports / exports

```
import <module_path> ( "(" <ident_list> ")" )? ( "as" <ident> )?
export <module_path>
```

`import` may also appear as a `body_expr`, in which case its
introductions are scoped to the enclosing block (rule, function,
instance, …).

## Operational notes

- Built-in solver is depth-first with naive tabling for the rule head.
- `let` bindings are evaluated eagerly in the order written.
- Function calls inside rule bodies are evaluated by the host engine
  before the goal is checked.
- Constraints are watched: a constraint defers until all referenced
  variables are bound, then fires.

## Out of scope for the parser

- Effect tracking.
- Module resolution against the filesystem (the parser produces an AST
  with `import` items; the engine resolves them).
- Type inference; the parser only records type expressions verbatim.
