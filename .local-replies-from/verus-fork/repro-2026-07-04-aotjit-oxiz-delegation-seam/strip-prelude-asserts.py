#!/usr/bin/env python3
# The §3.5.H suppression simulator: keep declarations, drop top-level (assert …)
# forms from a verus-emitted prelude. Strip `;` comments BEFORE paren-scanning
# (a `(#0)` inside a `;;` comment otherwise parses as a top-level form).
import sys
src = ''.join(ln.split(';', 1)[0] for ln in open(sys.argv[1]))
forms, depth, start = [], 0, None
for i, ch in enumerate(src):
    if ch == '(':
        if depth == 0: start = i
        depth += 1
    elif ch == ')':
        depth -= 1
        if depth == 0 and start is not None:
            forms.append(src[start:i+1]); start = None
kept = [f for f in forms if not f.lstrip('( \t\n').startswith('assert')]
sys.stdout.write('\n'.join(kept) + '\n')
print(f"forms {len(forms)}, asserts dropped {len(forms)-len(kept)}", file=sys.stderr)
