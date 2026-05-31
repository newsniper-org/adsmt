# Composition Recipes

Patterns that show up repeatedly. Use these as starting points; do not
treat them as the only valid composition.

## Hash-driven incremental compile

```makefile
%.o: %.c
	@freshcheck --method=hash $@ $< || $(CC) -c $< -o $@
	@stamp record --method=hash $@
```

The `||` short-circuit drops the recipe when `freshcheck` returns 0.
After a successful build, `stamp record` updates the signature so the
next run can shortcut.

## Multi-wildcard alignment matrix

```bash
lu-expand --var 'S=s1,s2,s3' --var 'R=hg38,mm10' \
  --filter 'S != R' \
  'align-{S}-{R}.bam' \
| while read tgt; do
    lu-rule --rulefile=rules.txt --dry-run "$tgt"
  done
```

Combines `lu-expand` (combinatorial generation) with `lu-rule`
(per-target recipe lookup).

## Dependency-aware parallel build

```bash
gcc -M *.c \
| lu-deps --from=gcc --to=taskfile \
| awk -F'\t' 'BEGIN{OFS="\t"} {print $1, $2, "make " $1}' \
| lu-par -j 8 --progress
```

`lu-deps` produces a taskfile skeleton; `awk` fills in the command
column; `lu-par` schedules respecting the DAG.

## SLURM pipeline driven by shell

```bash
declare -a jobs
for s in $(lu-expand --var 'S=s1,s2,s3' '{S}'); do
  jid=$(lu-queue submit --engine=slurm --slots=4 --mem=16G \
        -- align "$s" hg38)
  jobs+=("$jid")
done
lu-queue wait "${jobs[@]}"
```

Each `submit` prints a job ID; the array of IDs is passed to `wait`.

## Logic-driven target selection

```bash
lu-query --kb project.kb --all 'stale(T)' --format=tsv \
| tail -n +2 \
| while IFS=$'\t' read T; do
    lu-par --taskfile <(lu-deps --reverse "$T" --to=taskfile)
  done
```

Use the logic engine to identify what is stale; then build the reverse
cone of every stale target in parallel.

## Transactional batch

```bash
lu-par --transaction --taskfile=batch.tsv
```

If any task fails, `lu-par` rolls back signatures recorded by
already-completed tasks via `stamp`. The batch behaves atomically with
respect to the freshness store.
