// datatypes-match-2: field-bearing 4-variant enum (state machine), nested
// Option-like enum over it, struct field reasoning, match-with-binders,
// assert-in-body case analysis and lemma-calls-lemma proofs.
use vstd::prelude::*;

verus! {

enum Status {
    Idle,
    Running(u64),
    Done(u64),
    Failed,
}

enum MaybeStatus {
    Nothing,
    Just(Status),
}

struct Task {
    id: u64,
    status: Status,
}

spec fn progress(s: Status) -> int {
    match s {
        Status::Idle => 0,
        Status::Running(p) => p as int,
        Status::Done(t) => t as int,
        Status::Failed => 0,
    }
}

spec fn wf(s: Status) -> bool {
    match s {
        Status::Running(p) => p <= 10,
        Status::Done(t) => t <= 10,
        _ => true,
    }
}

spec fn advance(s: Status) -> Status {
    match s {
        Status::Idle => Status::Running(0),
        Status::Running(p) => if p < 10 {
            Status::Running((p + 1) as u64)
        } else {
            Status::Done(p)
        },
        Status::Done(t) => Status::Done(t),
        Status::Failed => Status::Failed,
    }
}

spec fn progress_or(m: MaybeStatus, dflt: int) -> int {
    match m {
        MaybeStatus::Nothing => dflt,
        MaybeStatus::Just(s) => progress(s),
    }
}

spec fn step_task(t: Task) -> Task {
    Task { id: t.id, status: advance(t.status) }
}

// assert-in-body: match statement in the proof body, one assert per arm
proof fn lemma_progress_bounded(s: Status)
    requires
        wf(s),
    ensures
        0 <= progress(s) <= 10,
{
    match s {
        Status::Running(p) => {
            assert(p <= 10);
        },
        Status::Done(t) => {
            assert(progress(s) == t as int);
        },
        _ => {
            assert(progress(s) == 0);
        },
    }
}

// direct ensures: advancing preserves well-formedness and never loses progress
proof fn lemma_advance_wf(s: Status)
    requires
        wf(s),
    ensures
        wf(advance(s)),
        progress(advance(s)) >= progress(s),
{
}

// lemma-calls-lemma through a struct field update
proof fn lemma_step_task_preserves(t: Task)
    requires
        wf(t.status),
        t.id >= 1,
    ensures
        wf(step_task(t).status),
        step_task(t).id == t.id,
        step_task(t).id >= 1,
{
    lemma_advance_wf(t.status);
}

// nested enum: match in requires, match in body dispatching to a lemma
proof fn lemma_progress_or_bounded(m: MaybeStatus)
    requires
        match m {
            MaybeStatus::Nothing => true,
            MaybeStatus::Just(s) => wf(s),
        },
    ensures
        progress_or(m, 0) <= 10,
{
    match m {
        MaybeStatus::Nothing => {},
        MaybeStatus::Just(s) => {
            lemma_progress_bounded(s);
        },
    }
}

// exec match with binders on field-bearing variants refines the spec fn
fn progress_of(s: Status) -> (r: u64)
    ensures
        r as int == progress(s),
{
    match s {
        Status::Idle => 0,
        Status::Running(p) => p,
        Status::Done(t) => t,
        Status::Failed => 0,
    }
}

fn main() {}

} // verus!
