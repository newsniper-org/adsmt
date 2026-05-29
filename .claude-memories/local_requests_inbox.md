---
name: Inbox + outbox for cross-project requests/replies with other local repos
description: Other locally-developed projects drop request files into <adsmt root>/.local-requests-from/<sender-id>/; replies land in <adsmt root>/.local-replies-to/<recipient-id>/ and are mirrored via the `just mirror-local-replies-to <recipient> <target>` recipe.
type: reference
originSessionId: 32a1dc0d-7730-4862-8df4-6958199ce84f
---
# Cross-project local request inbox + reply outbox

## Inbox (incoming requests)

**Path**: `<adsmt main root>/.local-requests-from/<sender-id>/`
i.e. `/home/ybi/AD1/.local-requests-from/<sender-id>/`.

Other locally-developed projects (run in their own Claude Code
sessions or by the user directly) drop request files into a
sub-directory named after the sending project. The adsmt session
is expected to read these on its own initiative — periodically
during work, not only when the user prompts — so cross-project
asks don't block waiting for the user to mention them.

### Inbox convention

- Sender owns its own sub-directory: `.local-requests-from/<sender-id>/`.
- File format / cadence: not pre-specified — the sender decides.
- Directory may not yet exist; create it lazily only if writing
  a reply (not just to poll).

### How to use during a session

1. List the inbox occasionally:
   `ls /home/ybi/AD1/.local-requests-from/ 2>/dev/null`.
2. If a sender sub-directory has new content, read the files
   and decide whether to address the request inline or surface
   it to the user.

## Outbox (outgoing replies)

**Path**: `<adsmt main root>/.local-replies-to/<recipient-id>/`
i.e. `/home/ybi/AD1/.local-replies-to/<recipient-id>/`.

Replies addressed to other local projects are drafted here and
committed alongside any related code/policy changes. After commit,
the just recipe `mirror-local-replies-to` rsyncs the sub-directory
to the recipient project's `.local-replies-from/adsmt/` slot:

```bash
just mirror-local-replies-to <recipient-id> <target absolute path>
# example:
just mirror-local-replies-to ypeg ~/ypeg/.local-replies-from/adsmt/
```

The recipe depends on `mirror-memory` so memory snapshots ride
along consistently.

### Outbox convention

- Adsmt owns the sub-directory `.local-replies-to/<recipient-id>/`.
- File naming: `<YYYY-MM-DD>-<topic-slug>-<status>.md`
  (e.g. `2026-05-29-classical-axiom-on-demand-acceptance.md`).
- Status suffixes: `acceptance / counter-proposal / rejection /
  question / status-update`.
- Front-matter: `from: adsmt`, `to: <recipient>`, `date`,
  `title`, `status`, `references` (paths to the originating
  request file and any code refs).

## Audit

- Established 2026-05-29 by user note (inbox).
- Outbox convention added 2026-05-29 alongside the first
  outgoing reply (to ypeg, on the classical-axiom-on-demand
  request).
