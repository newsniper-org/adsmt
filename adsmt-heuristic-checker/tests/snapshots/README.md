# Breaking-version snapshots (ι peer)

Each subdirectory `vX.Y.Z/` holds a frozen copy of the
breaking-version list that was current as of the corresponding
shipped version of `adsmt-heuristic-checker`. The snapshot test
(`tests/snapshot_regression.rs`) walks every snapshot and
asserts that the current version's breaking-version set is a
**superset** of every snapshot's set.

## Layout

```
tests/snapshots/
  README.md                — this file
  v0.17.0/
    breaking-versions.txt  — empty (no breakings at v0.17.0)
```

## Adding a snapshot

When the crate ships a new released version, copy
`.breaking-versions.lock`'s content into a new
`tests/snapshots/vX.Y.Z/breaking-versions.txt` file. The
property test (`tests/property_versions.rs`) and snapshot
regression test (`tests/snapshot_regression.rs`) will pick it up
automatically. Removing a historical snapshot — or removing any
version line that appears in it — fails the test suite.
