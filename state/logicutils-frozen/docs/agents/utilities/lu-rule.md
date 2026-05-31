# lu-rule

Match a target against pattern rules; emit bindings, deps, and recipe.

## Signature

```
lu-rule [OPTIONS] TARGET
```

## Rule file format

Plain text. Rules separated by `---` on their own line. Each rule has
fields:

```
pattern: <multi-wildcard pattern, lu-match syntax>
deps:    <whitespace-separated templates>
recipe:  <single-line shell command template>
goal:    <X != Y or X == Y, optional>
```

`pattern`, `deps`, and `recipe` may use `{NAME}` substitutions; the
bindings come from matching `pattern` against `TARGET`.

## Options

| Flag | Notes |
| ---- | ----- |
| `--rulefile=FILE`   | rule file; otherwise read stdin |
| `--all`             | emit every matching rule |
| `--backtrack`       | on goal failure, try the next rule |
| `--dry-run`         | print expanded recipe, exit 0 |
| `--format=`         | output format |

## Output

One record per matching rule, with fields `target`, `recipe`, `deps`,
plus every bound variable name from the pattern.

## Exit codes

0 on a matching rule, 1 if no rule matches (or all matched rules
failed their goal under backtracking), 2 on error.

## Edge cases

- `--all` implies `--backtrack`.
- A rule with no `goal` always passes the goal check.
- Unknown goal operators (anything other than `!=` and `==`) are
  treated as a pass-through `true` and a diagnostic is emitted.
