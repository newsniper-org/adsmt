#!/usr/bin/env bash
#
# Claude Code PreCompact hook — append the current conversation to a
# rolling Markdown backup BEFORE Claude compacts it. The backup file
# is append-only by design: each compaction event adds a new section
# to the end. Prior sections are never rewritten.
#
# Triggered automatically by Claude Code when the conversation is
# about to be compacted (both auto and manual triggers). The hook
# receives a JSON object on stdin with at least:
#   { "transcript_path": "<jsonl path>",
#     "session_id":      "<uuid>",
#     "trigger":         "manual" | "auto",
#     "cwd":             "<project dir>",
#     "hook_event_name": "PreCompact" }
#
# Failure modes are non-fatal: we exit 0 on any error so a hook
# malfunction never blocks compaction.
set -uo pipefail

# Where to store the rolling backup. Tied to the project workspace.
project_dir="${CLAUDE_PROJECT_DIR:-$(pwd)}"
backup_dir="${project_dir}/.claude-conversations"
backup_file="${backup_dir}/precompact-backups.md"

mkdir -p "$backup_dir" || exit 0

# Read the JSON envelope from stdin.
json="$(cat)" || exit 0

transcript_path="$(printf '%s' "$json" | jq -r '.transcript_path // empty')"
session_id="$(printf '%s' "$json" | jq -r '.session_id // empty')"
trigger="$(printf '%s' "$json" | jq -r '.trigger // "unknown"')"
now="$(date -Iseconds)"

# Append the section header even if the transcript turns out to be
# unreadable — the timestamped entry is itself evidence that the
# hook fired.
{
    printf '\n---\n\n'
    printf '## Pre-compact backup — %s\n\n' "$now"
    printf -- '- session_id: `%s`\n' "$session_id"
    printf -- '- trigger: `%s`\n' "$trigger"
    printf -- '- transcript_path: `%s`\n\n' "$transcript_path"
} >> "$backup_file"

if [ -n "$transcript_path" ] && [ -f "$transcript_path" ]; then
    {
        printf '<details><summary>Conversation transcript (raw JSONL)</summary>\n\n'
        printf '```jsonl\n'
        cat -- "$transcript_path"
        printf '\n```\n\n'
        printf '</details>\n'
    } >> "$backup_file"
else
    printf -- '*(transcript file unavailable at hook time)*\n' >> "$backup_file"
fi

exit 0
