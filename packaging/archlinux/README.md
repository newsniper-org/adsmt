# Arch Linux packaging — channel × variant matrix

adsmt v1.0+ ships nine PKGBUILDs covering all combinations of three
release channels (`stable`, `testing`, `git`/unstable) × three build
variants (`default`, `hpc`, `multi`).

Design discussion: `docs/thoughts/archlinux-pkgbuild-plan.md`.

## Matrix

|              | default features        | HPC (slurm/sge/pbs/sha3) | multi (slim multicall)  |
|--------------|-------------------------|--------------------------|--------------------------|
| **stable**   | `adsmt-meta/`           | `adsmt-hpc-meta/`        | `adsmt-multi-meta/`      |
| **testing**  | `adsmt-meta-testing/`   | `adsmt-hpc-meta-testing/`| `adsmt-multi-meta-testing/`|
| **git**      | `adsmt-meta-git/`       | `adsmt-hpc-meta-git/`    | `adsmt-multi-meta-git/`  |

Each cell is a single `pkgbase` producing multiple split packages.

## Split packages by pkgbase

### Default pkgbase (per channel) — 6 split packages
- `logicutils[-testing|-git]` — lu-* / freshcheck / stamp utilities
- `adsmt-cli[-testing|-git]` — lu-smt SMT solver CLI
- `adsmt-lsp[-testing|-git]` — tower-lsp server (no variant — owned only here)
- `adsmt-ffi[-testing|-git]` — C ABI: libadsmt_ffi.{so,a} + adsmt.h (no variant)
- `adsmt-src[-testing|-git]` — workspace source tree (no variant)
- `adsmt-meta[-testing|-git]` — meta-package, depends on above (except `-src`)

### HPC pkgbase (per channel) — 3 split packages
- `logicutils-hpc[-testing|-git]` — utilities with SLURM/SGE/PBS + SHA3 features
- `adsmt-cli-hpc[-testing|-git]` — lu-smt with HPC features
- `adsmt-hpc-meta[-testing|-git]` — meta-package, depends on hpc CLI splits + non-variant splits from default pkgbase

### Multi pkgbase (per channel) — 3 split packages
- `logicutils-multi[-testing|-git]` — lu-multi multicall + 9 symlinks (busybox-style)
- `adsmt-cli-multi[-testing|-git]` — slim lu-smt (--no-default-features)
- `adsmt-multi-meta[-testing|-git]` — meta-package, depends on multi CLI splits + non-variant splits from default pkgbase

**Total packages**: 11 (default) + 3 (hpc) + 3 (multi) = 17 per channel × 3 channels = **33 packages**.

## Choosing the right package

```
                 ┌──── stable ────┐ ┌─── testing ───┐ ┌───── git ──────┐
default flavor:  │ adsmt-meta     │ │ adsmt-meta-   │ │ adsmt-meta-git │
                 │                │ │   testing     │ │                │
HPC flavor:      │ adsmt-hpc-meta │ │ adsmt-hpc-    │ │ adsmt-hpc-meta │
                 │                │ │   meta-testing│ │   -git         │
Slim flavor:     │ adsmt-multi-   │ │ adsmt-multi-  │ │ adsmt-multi-   │
                 │   meta         │ │   meta-testing│ │   meta-git     │
                 └────────────────┘ └───────────────┘ └────────────────┘
```

- **End user, workstation**: `adsmt-meta` (stable, default)
- **HPC cluster head node**: `adsmt-hpc-meta` (stable, HPC)
- **Container / CI / embedded**: `adsmt-multi-meta` (stable, slim)
- **Pre-release tester**: `*-meta-testing` (testing channel)
- **Developer / bleeding edge**: `*-meta-git` (main branch)

Source tree only (no binaries):
- `adsmt-src` (stable), `adsmt-src-testing` (testing branch),
  `adsmt-src-git` (main branch)

## Build instructions

```bash
# Single pkgbase build
cd packaging/archlinux/adsmt-meta
makepkg --syncdeps --noconfirm

# All nine pkgbases (when packaging tests resume post-v1.0.0)
for d in packaging/archlinux/adsmt-*meta*; do
  (cd "$d" && makepkg --syncdeps --noconfirm)
done
```

## Conflict matrix

Variants of the same package (e.g. `logicutils` vs `logicutils-hpc` vs
`logicutils-multi`) share the same `/usr/bin/<binary>` paths, so all
nine variants of `logicutils*` mutually conflict. Same for
`adsmt-cli*`, `adsmt-lsp*`, `adsmt-ffi*`, `adsmt-src*`, and meta
packages.

Channel suffix (`-testing`, `-git`) does not provide a meaningful
side-by-side install — they all conflict with the no-suffix stable
package. Pick a single channel × variant combination per system.

## Inheritance from logicutils v0.x

The `logicutils*` split packages here are the named successors of the
v0.x packages (`logicutils`, `logicutils-hpc`, `logicutils-multi` and
their `-git` counterparts). A `pacman -Syu` from a v0.x install
transparently upgrades to the v1.0+ namespakes via the matching
package name. Version jump 0.2.0 → 1.0.0+; no epoch needed
(0.2.0 < 1.0.0).

The new splits (`adsmt-cli*`, `adsmt-lsp*`, `adsmt-ffi*`,
`adsmt-src*`, `adsmt-*-meta`) are net-new — no v0.x equivalent.

## Status (2026-06-01)

Per `memory/v1_0_0_scope_expansion.md`: actual `makepkg` testing is
deferred until adsmt v1.0.0 stable cut commits. The nine PKGBUILDs
here are reviewed and ready to exercise once the cut lands.
