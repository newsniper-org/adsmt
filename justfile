# adsmt project tasks

# Path to Claude Code's auto-memory dir for this project.
# Derived from the absolute project path by replacing `/` with `-`,
# matching the encoding Claude Code uses under ~/.claude/projects/.
_memory_dir := env_var("HOME") + "/.claude/projects/" + replace(justfile_directory(), "/", "-") + "/memory"

# Latest session UUID is mirrored to a stable path for resume helpers.
_session_file := justfile_directory() + "/.claude-latest-session-id"

# Default: list available recipes.
default:
    @just --list

# Mirror Claude Code's auto-memory into .claude-memories/ for version control.
# Safe to re-run; uses rsync so updates are incremental.
mirror-memory:
    @mkdir -p .claude-memories
    @if [ -d "{{_memory_dir}}" ] && [ -n "$(ls -A '{{_memory_dir}}' 2>/dev/null)" ]; then \
        rsync -a --delete '{{_memory_dir}}/' .claude-memories/ ; \
        echo "✓ Mirrored {{_memory_dir}} → .claude-memories/" ; \
    else \
        echo "⚠ {{_memory_dir}} is empty or missing — nothing to mirror" ; \
    fi

# Restore Claude Code memory from .claude-memories/ and print resume hint.
# Use after a system update or fresh checkout to pick up where you left off.
claude-resume:
    @echo "=== adsmt: Claude Code resume helper ==="
    @echo ""
    @if [ -d .claude-memories ] && [ -n "$(ls -A .claude-memories 2>/dev/null)" ]; then \
        mkdir -p '{{_memory_dir}}' ; \
        rsync -a .claude-memories/ '{{_memory_dir}}/' ; \
        echo "✓ Restored .claude-memories/ → {{_memory_dir}}" ; \
    else \
        echo "⚠ .claude-memories/ empty or missing — nothing to restore" ; \
    fi
    @echo ""
    @latest=$(ls -t .claude-conversations/*.md 2>/dev/null | head -1); \
    if [ -n "$latest" ]; then \
        echo "Latest design conversation: $latest" ; \
        echo "  Size: $(wc -l < "$latest") lines" ; \
    else \
        echo "No .claude-conversations/ logs found." ; \
    fi
    @echo ""
    @if [ -f "{{_session_file}}" ]; then \
        echo "Last recorded session: $(cat '{{_session_file}}')" ; \
    fi
    @echo ""
    @echo "To resume context, start Claude Code in this directory and ask:"
    @echo "  \"Read the latest file in .claude-conversations/ and continue.\""

# Refresh the read-only status snapshot at ~/adsmt-status/. Other
# Claude Code agents (operating in unrelated working directories)
# pull the snapshot from there on demand. Always safe to run.
status:
    @scripts/snapshot-status.sh
    @echo "✓ Snapshot refreshed at ${ADSMT_STATUS_DIR:-$HOME/adsmt-status}/"
    @echo "  HEAD: $(cat ${ADSMT_STATUS_DIR:-$HOME/adsmt-status}/head.txt)"

# Run the workspace test suite and update the cached tests.txt
# entry in the snapshot. Slow — run it before sharing the snapshot
# externally if the count matters to the consumer.
status-tests:
    @echo "Running cargo test --workspace --all-features (this takes a minute)..."
    @count=$(cargo test --workspace --all-features 2>&1 | awk '/^test result/ { ok+=$4 } END { print ok }'); \
        echo "$count tests passing as of $(date -u +%Y-%m-%dT%H:%M:%SZ)" \
            > "${ADSMT_STATUS_DIR:-$HOME/adsmt-status}/tests.txt" ; \
        echo "✓ tests.txt updated: $count passing"
    @just status

# (Optional, manual) Wire snapshot-status.sh into the local git
# post-commit hook so every commit auto-refreshes ~/adsmt-status/.
# This is OFF by default — the user must explicitly opt in by
# running `just install-status-hook`. Uninstall with the matching
# `just uninstall-status-hook` recipe.
install-status-hook:
    @mkdir -p .git/hooks
    @printf '#!/usr/bin/env bash\nset +e\n"$(git rev-parse --show-toplevel)/scripts/snapshot-status.sh" 2>/dev/null\nexit 0\n' \
        > .git/hooks/post-commit
    @chmod +x .git/hooks/post-commit
    @echo "✓ Installed .git/hooks/post-commit — snapshot will refresh after every commit"

uninstall-status-hook:
    @if [ -f .git/hooks/post-commit ]; then \
        rm -f .git/hooks/post-commit ; \
        echo "✓ Removed .git/hooks/post-commit" ; \
    else \
        echo "⚠ No .git/hooks/post-commit installed" ; \
    fi
