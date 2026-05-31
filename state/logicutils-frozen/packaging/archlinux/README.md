# Arch / CachyOS packaging

Six PKGBUILDs cover a 3 × 2 matrix: three feature variants, each in
*tagged-release* and *git-main* flavours.

| Directory                 | Package               | Source         | Variant       |
| ------------------------- | --------------------- | -------------- | ------------- |
| `./` (this dir)           | `logicutils`          | tagged release | Default — individual binaries, BLAKE3+CRC32+local queue. |
| `logicutils-git/`         | `logicutils-git`      | git `main`     | Default, tracking main. |
| `logicutils-multi/`       | `logicutils-multi`    | tagged release | Tier 1 — single multicall binary with symlinks, no crypto/cluster. |
| `logicutils-multi-git/`   | `logicutils-multi-git`| git `main`     | Tier 1, tracking main. |
| `logicutils-hpc/`         | `logicutils-hpc`      | tagged release | HPC — SLURM/SGE/PBS + SHA3 compiled in. |
| `logicutils-hpc-git/`     | `logicutils-hpc-git`  | git `main`     | HPC, tracking main. |

All six packages `conflict` with each other on purpose — install only one
at a time. Each `-git` package additionally `provides=` its tagged
counterpart, so dependents that ask for `logicutils-multi` are satisfied
by `logicutils-multi-git` etc.

## Build & install

Standard `makepkg` flow. From whichever directory you chose:

```sh
makepkg -si        # build, install via pacman
makepkg -fC        # rebuild from clean state
```

For repeatable builds drop into a clean chroot:

```sh
extra-x86_64-build         # CachyOS uses devtools-style chroots
```

## Internal repository

If you maintain an in-house pacman repository, after `makepkg`:

```sh
repo-add /srv/pkg/lu/lu.db.tar.zst logicutils-*.pkg.tar.zst
```

and add the repo to `/etc/pacman.conf` on consuming machines:

```ini
[lu]
SigLevel = Optional TrustAll
Server   = file:///srv/pkg/lu     # or rsync://… or https://…
```

## Notes

- `pkgver` in the release PKGBUILD is updated by hand on each tag; bump
  `pkgrel` for packaging-only fixes.
- The tag-based PKGBUILDs leave `sha256sums=('SKIP')` for in-house use.
  Replace with the actual sum (`updpkgsums`) before publishing externally.
- `optdepends` lists cluster client tools only — they are runtime concerns,
  not build-time. The `slurm`/`sge`/`pbs` Cargo features still need to be
  enabled at build time if you want those engines compiled in; the
  baseline PKGBUILD builds with default features (BLAKE3 + CRC32 +
  built-in logic engine + local queue).
- For an HPC build add `--features slurm,sge,pbs` (or whichever subset
  you actually use) to the `cargo build` line in the relevant PKGBUILD.
- The multicall package builds with `--no-default-features` to keep the
  binary small. If you need BLAKE3 there too, add `--features blake3`.
