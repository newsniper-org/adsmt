# logicutils — Agent Reference

This directory contains structured, machine-friendly documentation for AI
coding agents (Claude Code, Aider, Cursor, etc.) that need to read,
extend, or use logicutils. Files here are deliberately terse, schema-like,
and free of marketing prose.

## Index

| File | Purpose |
| ---- | ------- |
| `architecture.md` | Workspace layout, crate dependency graph, design invariants. |
| `cli-protocol.md` | The CLI standard every utility must obey. |
| `kb-language.md` | Concise grammar and semantics of the KB language. |
| `utilities/*.md`  | One file per utility: signature, exit codes, edge cases. |
| `recipes.md`      | Composition patterns (build systems, pipelines, queues). |
| `extending.md`    | How to swap engines, add backends, add new utilities. |

## Reading order for a new agent

1. `architecture.md` — understand what crates exist and why.
2. `cli-protocol.md` — never violate this when emitting code.
3. `utilities/<name>.md` — the utility relevant to the user task.
4. `kb-language.md` — only when touching `lu-query` / `lu-rule`.

## Hard rules

- **Never invent flags.** If a behavior is not in the relevant
  `utilities/*.md`, add it deliberately rather than pretending it exists.
- **Exit codes are part of the API.** `0 = success / fresh / true`,
  `1 = expected negative result`, `2 = error`. Code that maps these to
  Rust `Result` must distinguish 1 from 2.
- **stdout is data, stderr is diagnostics.** No progress text on stdout.
- **No global state.** Every utility takes its store path as an argument
  (default `.lu-store/`). Don't read environment variables in the hot
  path.
