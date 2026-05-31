# lu-queue

Submit/inspect/cancel jobs against local or cluster queues.

## Subcommands

```
lu-queue submit [OPTIONS] -- COMMAND [ARG...]
lu-queue status JOBID
lu-queue wait   JOBID...
lu-queue cancel JOBID...
lu-queue list
```

The `--` separator before `COMMAND` is required when `COMMAND` itself
takes flags.

## Options

| Flag | Applies to | Notes |
| ---- | ---------- | ----- |
| `--engine=local\|slurm\|sge\|pbs` | all | local default; cluster engines gated by Cargo features |
| `--slots=N`              | submit | CPU slots |
| `--mem=SIZE`             | submit | e.g. `8G` |
| `--time=DURATION`        | submit | e.g. `2h30m` |
| `--deps=JOBID[,…]`       | submit | wait-for predecessors |

## Output

- `submit`: job ID on stdout, ready to capture into a shell variable.
- `status`: one of `pending`, `running`, `done`, `failed`.
- `list`: TSV (or chosen `--format`) of `JOBID\tSTATUS\tCOMMAND`.

## Exit codes

- `submit`: 0 if accepted by backend, 2 on error.
- `status`: 0 for `done`, 1 for `failed`, 2 on error or missing job.
- `wait`: 0 if all jobs reached `done`, 1 if any reached `failed`, 2 on
  error.
- `cancel`: 0 on success, 2 on error.

## Engine mapping

| Generic flag | SLURM         | SGE            | PBS              |
| ------------ | ------------- | -------------- | ---------------- |
| `--slots=N`  | `-c N`        | `-pe smp N`    | `-l ncpus=N`     |
| `--mem=8G`   | `--mem=8G`    | `-l h_vmem=8G` | `-l mem=8gb`     |
| `--time=2h`  | `--time=02:00:00` | `-l h_rt=02:00:00` | `-l walltime=02:00:00` |
| `--deps=A,B` | `-d afterok:A:B` | `-hold_jid A,B` | `-W depend=afterok:A:B` |
