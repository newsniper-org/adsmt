#!/usr/bin/env bash
#
# Emit a snapshot of adsmt main-project live progress to a shared
# read-only directory other Claude Code agents (and humans) can pull
# from. Designed to run in two ways:
#
#   * `just status` — manual refresh from the current working tree.
#   * git post-commit hook (opt-in) — install with
#     `just install-status-hook`; refreshes automatically after each
#     commit. Off by default because session-installed hooks survive
#     beyond the session; the user opts in explicitly.
#
# The snapshot lives outside the project tree on purpose: other
# agents may be operating in unrelated working directories and will
# not have permission to read paths under `~/AD1`. Default location
# is `~/adsmt-status/`, overridable via `$ADSMT_STATUS_DIR`.
#
# Files written:
#   README.md       — protocol description (only on first run)
#   snapshot.md     — human-readable status digest (always rewritten)
#   head.txt        — current HEAD SHA + branch
#   last-commit.txt — most recent commit subject + body
#   tests.txt       — last known workspace test count (cached)
#   task-list.txt   — current in-progress / pending task names
#   updated-at.txt  — UTC timestamp of this snapshot
#
# The script is idempotent and safe to run concurrently — writes go
# through temp files + atomic rename so partial reads from other
# agents see either old or new content, never a mix.
set -uo pipefail

project_dir="${ADSMT_PROJECT_DIR:-$HOME/AD1}"
status_dir="${ADSMT_STATUS_DIR:-$HOME/adsmt-status}"

mkdir -p "$status_dir" || exit 0

# Resolve git context.
branch="$(git -C "$project_dir" rev-parse --abbrev-ref HEAD 2>/dev/null || echo unknown)"
head_sha="$(git -C "$project_dir" rev-parse HEAD 2>/dev/null || echo unknown)"
head_short="$(git -C "$project_dir" rev-parse --short HEAD 2>/dev/null || echo unknown)"
ahead_behind="$(git -C "$project_dir" rev-list --left-right --count "@{u}...HEAD" 2>/dev/null || echo "?  ?")"
last_subject="$(git -C "$project_dir" log -1 --format=%s 2>/dev/null || echo unknown)"
last_body="$(git -C "$project_dir" log -1 --format=%b 2>/dev/null || echo "")"
last_commit_at="$(git -C "$project_dir" log -1 --format=%cI 2>/dev/null || echo unknown)"
log_oneline="$(git -C "$project_dir" log --oneline -5 main 2>/dev/null || git -C "$project_dir" log --oneline -5 2>/dev/null || echo "")"

dirty="$(git -C "$project_dir" status --porcelain 2>/dev/null | head -10)"
dirty_count="$(git -C "$project_dir" status --porcelain 2>/dev/null | wc -l | tr -d ' ')"

now="$(date -u +%Y-%m-%dT%H:%M:%SZ)"

atom_write() {
    local target="$1"
    local content="$2"
    local tmp
    tmp="$(mktemp "${target}.XXXXXX")" || return 1
    printf '%s' "$content" > "$tmp"
    mv -f "$tmp" "$target"
}

# README only on first run (other agents see the protocol).
if [ ! -f "$status_dir/README.md" ]; then
    atom_write "$status_dir/README.md" "$(cat <<EOF
# adsmt main-project live status

This directory is a read-only window into the adsmt main project at
\`$project_dir\`. It is regenerated automatically on every commit
(via a git post-commit hook) and can also be refreshed on demand
with \`just status\` from the project root.

## Files

| File | Content |
|---|---|
| \`snapshot.md\` | Human-readable digest. Read this first. |
| \`head.txt\` | One line: \`<branch> <full-SHA>\`. |
| \`last-commit.txt\` | Most recent commit subject + body. |
| \`tests.txt\` | Cached workspace test count (\`cargo test --workspace --all-features\`). |
| \`task-list.txt\` | Active task names (best-effort, may lag in-conversation state). |
| \`updated-at.txt\` | UTC timestamp of this snapshot generation. |

## Protocol for other Claude Code agents

- This directory is read-only from your perspective. Never write
  to it; the adsmt session manages it.
- Snapshots are *eventually* consistent. After a commit it can
  take up to a few seconds for the snapshot to refresh.
- The HEAD SHA in \`head.txt\` is authoritative for "what state
  of adsmt is currently published". If you need newer state,
  the snapshot has not landed yet; check again later.
- If you need a deeper view than what's exposed here, ask the
  user — do not attempt to read files under \`$project_dir\`
  unless they have granted explicit access.
EOF
)"
fi

# snapshot.md — the human digest.
snapshot_md="$(cat <<EOF
# adsmt status snapshot

- **Branch**: \`$branch\`
- **HEAD**: \`$head_short\` (\`$head_sha\`)
- **Ahead/behind upstream**: $ahead_behind
- **Last commit**: $last_commit_at
- **Updated at**: $now (UTC)
- **Working-tree changes**: $dirty_count file(s) modified or untracked

## Last commit

> $last_subject

EOF
)"

if [ -n "$last_body" ]; then
    snapshot_md="${snapshot_md}
$last_body
"
fi

snapshot_md="${snapshot_md}
## Recent commits (oneline)

\`\`\`
$log_oneline
\`\`\`
"

if [ "$dirty_count" -gt 0 ]; then
    snapshot_md="${snapshot_md}
## Working tree (top 10)

\`\`\`
$dirty
\`\`\`
"
fi

atom_write "$status_dir/snapshot.md" "$snapshot_md"
atom_write "$status_dir/head.txt" "$branch $head_sha"$'\n'
atom_write "$status_dir/last-commit.txt" "${last_subject}
${last_body}"
atom_write "$status_dir/updated-at.txt" "$now"$'\n'

# tests.txt — best-effort cached test count from the most recent
# successful build artifact. We do NOT run `cargo test` from this
# script because it would block commits. The post-commit hook just
# captures whatever was last written; manual refresh via `just
# status-tests` runs the suite explicitly.
if [ ! -f "$status_dir/tests.txt" ]; then
    atom_write "$status_dir/tests.txt" "unknown — run \`just status-tests\` to populate"$'\n'
fi

# task-list.txt — placeholder; the session can override.
if [ ! -f "$status_dir/task-list.txt" ]; then
    atom_write "$status_dir/task-list.txt" "task list not yet populated"$'\n'
fi

exit 0
