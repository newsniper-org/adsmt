#!/usr/bin/env bash
#
# π peer: pre-commit hook for the 8-layer breaking-version
# safeguard. Refuses to commit when any version line has been
# REMOVED from any of the four peer sources (γ lockfile, ε
# manifest, τ Cargo.toml metadata, ι snapshot files).
#
# Installed by `just install-breaking-hook`. Bypass with the
# standard `git commit --no-verify` flag.
#
# The check uses a simple diff-side comparison: for every line
# of the form `^-X` in the staged change to any peer file,
# extract X and verify X is not a semver-shaped string. This is
# intentionally conservative — any deletion at all of a semver-
# shaped line aborts the commit.
set -uo pipefail

project_dir="${ADSMT_PROJECT_DIR:-$(git rev-parse --show-toplevel)}"
checker_dir="$project_dir/adsmt-heuristic-checker"

peer_paths=(
    "$checker_dir/.breaking-versions.lock"
    "$checker_dir/breaking_history.txt"
    "$checker_dir/Cargo.toml"
)

# Add every vendored snapshot file too.
if [ -d "$checker_dir/tests/snapshots" ]; then
    while IFS= read -r snap; do
        peer_paths+=("$snap")
    done < <(find "$checker_dir/tests/snapshots" -name "breaking-versions.txt")
fi

semver_pattern='^[0-9]+\.[0-9]+\.[0-9]+(-[A-Za-z0-9.-]+)?$'

aborted=0
for path in "${peer_paths[@]}"; do
    [ -f "$path" ] || continue
    rel="${path#$project_dir/}"
    # Only inspect staged changes.
    diff_output=$(git diff --cached --unified=0 -- "$rel" 2>/dev/null || true)
    [ -n "$diff_output" ] || continue
    while IFS= read -r line; do
        # Lines like `-X` (but not `---` diff headers) are
        # deletions. Bash 5.3 rejects `---*|--- *)` unquoted in
        # case patterns due to a leading-dash interaction; the
        # quoted form is equivalent and parses cleanly across
        # bash versions.
        case "$line" in
            '---'*|'--- '*) continue ;;
            -*)
                stripped="${line#-}"
                stripped="${stripped## }"
                stripped="${stripped%% *}"
                # Strip quotes (Cargo.toml metadata uses "X.Y.Z").
                stripped="${stripped//\"/}"
                stripped="${stripped//\'/}"
                stripped="${stripped//,/}"
                if [[ "$stripped" =~ $semver_pattern ]]; then
                    echo "✗ pre-commit: refused to remove semver line \`$stripped\` from $rel" >&2
                    aborted=1
                fi
                ;;
        esac
    done <<<"$diff_output"
done

if [ "$aborted" -eq 1 ]; then
    echo "" >&2
    echo "The 8-layer breaking-version safeguard prohibits removing" >&2
    echo "historical semver lines from any peer source. If this is" >&2
    echo "an intentional retraction (rare!), bypass with:" >&2
    echo "" >&2
    echo "    git commit --no-verify" >&2
    echo "" >&2
    exit 1
fi

exit 0
