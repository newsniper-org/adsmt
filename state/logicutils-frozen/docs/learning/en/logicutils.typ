// Compile with Typst >= 0.14.x:  typst compile logicutils.typ
#set document(title: "logicutils — A Gentle Introduction", author: "NEWSNIPER")
#set page(paper: "a4", margin: 2.2cm, numbering: "1")
#set par(justify: true, leading: 0.7em)
#set text(font: "New Computer Modern", size: 11pt, lang: "en")
#set heading(numbering: "1.1")
#show heading.where(level: 1): it => [
  #pagebreak(weak: true)
  #block(below: 1.0em, text(weight: "bold", size: 18pt, it.body))
]
#show raw.where(block: true): it => block(
  fill: luma(245), inset: 8pt, radius: 3pt, width: 100%, it
)

#align(center)[
  #text(size: 22pt, weight: "bold")[logicutils]
  #v(0.4em)
  #text(size: 14pt)[A Gentle Introduction for Beginners]
  #v(2em)
]

#outline(indent: auto)

= Why does this project exist?

You may already have written your first programs.  Perhaps a small C program
that you compiled with `gcc`, or a Python script that you ran with `python3`.
At first these programs are tiny and you compile or run them by hand.  Quite
soon, however, every project grows large enough that doing things by hand
becomes painful.  Three particular pains appear over and over again:

+ *Repetition*. You change one source file and have to remember which
  outputs depend on it so that you can rebuild only those.
+ *Patterns*. Many tasks share the same shape ("compile every `.c` file in
  this directory into a `.o`"); writing each one by hand is silly.
+ *Bookkeeping*. You want to know whether a file is "up-to-date" without
  guessing.  In a team, "up-to-date according to whom?" becomes a real
  question.

The classical answer to all three is a _build system_ such as Make.  Make is
about fifty years old.  It works, and you should learn it, but it has known
weaknesses: its decisions about what to rebuild are usually based only on
file modification times; its language is small and brittle; and extending
it for, say, scientific pipelines or AI training jobs is awkward.

A more modern answer is BioMake, an experimental tool from bioinformatics
that fixes some of those weaknesses by adding _logic programming_ on top of
Make.  Logic programming, which you may meet later under the name "Prolog",
lets you describe what counts as a valid build configuration in terms of
rules and facts and let a search engine find the answer.  BioMake is
brilliantly designed but suffers from a different problem: it is a single
big tool that wants to replace Make instead of cooperating with it.

*logicutils* is an attempt to keep the good ideas from BioMake — multi-wild­
card patterns, content-based freshness checks, logic programming, cluster
support — and reshape them into a _toolkit_ that cooperates with whatever
build system or shell you already use.  Each tool in the kit does one thing
well, in the spirit of the classical Unix philosophy.  Together they cover
the same ground as a build system, but you compose them yourself.

This document teaches you what those tools are and how to think with them.
It assumes you can read a small shell script and recognise basic algorithm
ideas (graphs, hashing, recursion).  It does *not* assume any background in
build systems, logic programming, or cluster computing.  We will introduce
those ideas as we need them.

= A short tour of the building blocks

#figure(
  table(
    columns: (auto, 1fr),
    align: (left, left),
    inset: 6pt,
    stroke: 0.5pt + luma(180),
    [*Tool*], [*One-line idea*],
    [`freshcheck`], [Decide whether a target is up-to-date.],
    [`stamp`],      [Record file signatures (hashes, sizes, …).],
    [`lu-match`],   [Match a pattern with named wildcards against a string.],
    [`lu-expand`],  [Generate combinations from sets of values.],
    [`lu-query`],   [Ask logical questions about facts and rules.],
    [`lu-rule`],    [Find a rule that builds a given target.],
    [`lu-queue`],   [Submit jobs to local or cluster schedulers.],
    [`lu-par`],     [Run a graph of dependent tasks in parallel.],
    [`lu-deps`],    [Read, transform, and analyse dependency graphs.],
    [`lu-multi`],   [One binary that contains all of the above.],
  ),
  caption: [The nine utilities (and the multicall binary).],
)

The rest of this document explains, for each tool, the problem it solves,
the underlying idea in plain language, and a small example.  Wherever an
idea is bigger than a paragraph (such as content-based freshness or logic
programming) we pause and explain it from first principles.

= Knowing whether a file is fresh

== The naïve approach

When `make` decides whether to rebuild `main.o`, it compares the modification
time of `main.o` against the modification time of `main.c`.  If `main.c` is
newer, `main.o` is rebuilt.  This rule is fast (the operating system already
remembers modification times) and it usually works.

It also fails in surprising ways.  Suppose your editor saves `main.c` even
though you only opened it to look around.  Make will rebuild `main.o`
although the contents are identical.  Suppose you copy a file from a
different machine using a tool that resets timestamps.  Make may think the
copy is older than the output and skip the rebuild even though the copy
contains different bytes.  Build systems for scientific work and AI ran
into these problems early, and a different idea — _content-based freshness_
— gradually became standard.

== Content-based freshness

Instead of comparing timestamps, compare the _contents_ of files.  We
cannot afford to read the whole file every time, so we summarise it with a
fixed-size fingerprint called a _hash_.  A good cryptographic hash, such as
BLAKE3 or SHA3, has the property that any change in the file produces a
completely different fingerprint.  If the fingerprint of `main.c` matches
the fingerprint we recorded the last time we built `main.o`, we can skip
the rebuild even if the timestamp says otherwise.

The catch is that we need somewhere to remember last time's fingerprint.
That is what `stamp` does: it stores fingerprints in a small directory
called `.lu-store/`, which lives next to the project.  And `freshcheck` is
the tool that asks `stamp` "is this file's recorded fingerprint still
current?"

== A first example

```sh
# Rebuild main.o only when the contents of main.c actually changed.
freshcheck --method=hash main.o main.c || gcc -c main.c -o main.o
stamp record --method=hash main.o
```

`freshcheck` is silent on success and exits with status 0; on failure
it exits with status 1.  This means the shell short-circuit `||` runs the
compile command only when the file is stale.  After the build,
`stamp record` updates the fingerprint so the next run can skip again.

You may wonder why we need both a separate `stamp` and `freshcheck`.  The
reason is the Unix design rule: each tool does one job.  `stamp` knows
about the storage; `freshcheck` knows about the policy.  If you want to
combine timestamps with sizes and hashes, you change `freshcheck`'s flags
without touching the storage backend.

== Different ways to compare

`freshcheck` accepts several methods, possibly stacked together with
`--combine=any` or `--combine=all`:

- `timestamp`: the classic Make approach — fast, sometimes wrong.
- `hash`: the content-based approach above.  Very strong, slightly slower.
- `checksum`: a faster but weaker fingerprint (CRC-32).  Useful in
  resource-constrained environments where cryptographic hashing is too
  expensive.
- `size`: the file's byte length.  Trivial, but a useful tie-breaker
  combined with `timestamp` to detect "the file changed but the timestamp
  was reset".
- `always`: never trust anything; rebuild every time.  Used during
  debugging.

= Naming many files at once

== Patterns are everywhere

Software projects rarely deal with a single file in isolation.  Compiling
"every `.c` to a `.o`" or "every input FASTQ file to an output BAM file"
is the rule, not the exception.  Make has a primitive form of this with
`%`-rules, but `%` only stands for one wildcard, and many real problems
need two or more.

Consider a bioinformatics workflow.  You have many _samples_ and several
_references_, and for each (sample, reference) pair you produce an aligned
file:

```
align-sample1-hg38.bam
align-sample1-mm10.bam
align-sample2-hg38.bam
align-sample2-mm10.bam
…
```

You would like to write _one_ rule whose pattern says "given any sample $X$
and any reference $Y$, the file `align-X-Y.bam` is built from `X.fastq` and
`Y.fa`".  In Make this is awkward; in `lu-match` it is straightforward.

== `lu-match` syntax

A pattern is a string in which `\u{7B}NAME\u{7D}` (curly braces around an identifier)
denotes a named wildcard.  By default a wildcard matches one path segment
(no slashes).  Other forms exist, but for now think of `\u{7B}X\u{7D}` as "any chunk
of letters and digits".

Match a pattern against a single input:

```sh
$ lu-match 'align-{X}-{Y}.bam' align-sample1-hg38.bam
X=sample1
Y=hg38
```

Notice that the same name may appear twice, in which case the matcher
requires both occurrences to bind to the same value:

```sh
$ lu-match '{stem}.tar.{stem}'   # exotic: same word at start and end
```

This kind of equality check is called _unification_ and is the central
operation of logic programming.  We will meet it again in `lu-query`.

== `lu-expand`: making the matrix

`lu-match` answers "given a name, what wildcards does it bind?".
`lu-expand` answers the opposite: "given some wildcard values, what names
should I generate?".

```sh
lu-expand --var 'S=s1,s2,s3' --var 'R=hg38,mm10' \
          --filter 'S != R' \
          'align-{S}-{R}.bam'
```

This prints the Cartesian product of $S$ and $R$ minus the rows where the
filter `S != R` is false.  Cartesian product is exactly what you wrote on
paper in your discrete-math course: a set of pairs.  `lu-expand` walks the
pairs in the order of an odometer, the rightmost variable changing fastest.

`lu-match` and `lu-expand` together form the pattern layer of the toolkit.
You either go from concrete file names to wildcard values (matching) or
from wildcard values to concrete file names (expansion).

= From rules to logic

== Rules in the small

A traditional Makefile rule is a triple of pattern, dependencies, and a
recipe:

```
%.o: %.c
	$(CC) -c $< -o $@
```

`lu-rule` raises this to multiple wildcards:

```
pattern: align-{X}-{Y}.bam
deps:    {X}.fastq {Y}.fa
recipe:  bwa mem {Y}.fa {X}.fastq > align-{X}-{Y}.bam
goal:    X != Y
```

The optional `goal` line is a side condition.  When `lu-rule` looks at a
target like `align-sample1-hg38.bam`, it (i) tries to match the pattern,
(ii) checks that `goal` holds for the resulting bindings, and only then
(iii) emits the expanded `deps` and `recipe`.

The `goal` field is a hint that more is going on.  `goal: X != Y` is a tiny
logical formula.  What if we wanted longer formulae?  What if `goal` could
call other rules?  What if, instead of a single Boolean, the engine could
enumerate _all_ the assignments that make the goal true?

That is logic programming.  It deserves its own section.

== A small detour into logic programming

Logic programming asks you to describe the world declaratively, in terms of
_facts_ and _rules_, and then asks _queries_ to which the engine searches
for answers.  The most famous logic programming language is Prolog; the
ideas here are similar but not identical.

A *fact* is a statement we accept as true:

```
parent(alice, bob)
parent(bob,   carol)
```

A *rule* derives new facts from existing ones:

```
rule grandparent(X, Z):
    parent(X, Y)
    parent(Y, Z)
```

A *query* asks a question:

```
?  grandparent(alice, Who)
```

The engine searches for assignments to `Who` that make `grandparent(alice,
Who)` true.  Here it finds `Who = carol`.  The engine works by trying
candidates and _unifying_ each variable with concrete values; this is the
same unification we saw in `lu-match`.

logicutils ships a knowledge-base language called _KB_ (described in detail
in #link(<kb-language>)[Section 7]) and a tool called `lu-query` that reads KB files and
answers queries.  KB has facts and rules like Prolog, plus three additional
ideas you will not find in standard Prolog: _abduction_, _constraints_, and
_type relations_.

== Abduction in one paragraph

Deduction goes from rules and facts to conclusions.  _Abduction_ goes the
other way: given a conclusion you would like to be true and the rules of
the world, propose facts that — if true — would explain the conclusion.
In a build context this is exactly the question "what would I need to do
to make this target up-to-date?"  KB exposes abduction directly with the
`abduce` keyword:

```
abduce missing_source(File):
    depends(Target, File)
    not exists(File)
    explain "source file may need generation"
```

== Constraints

A constraint is a logical condition that the engine watches as variables
become bound.  As soon as a watched variable is determined and the
condition is violated, the search backtracks.  Constraints make it natural
to express things like "this analysis is only valid if `quality >= 30`",
and the engine applies them as early as possible rather than only at the
final step.

== Why this matters for builds

A build system is, fundamentally, a logical theory: targets exist, files
depend on each other, recipes build files, freshness implies skipping the
recipe.  Once you have a logic engine you can ask interesting queries:

- _Which targets are stale?_
- _What is the smallest set of files I would need to regenerate to make
  target $T$ up-to-date?_
- _Why is target $T$ being rebuilt?  What did the engine deduce?_

Every classical build system answers a fixed subset of these questions.
With `lu-query` you ask whichever question fits today.

= The KB language <kb-language>

== The shape of a KB file

The KB language is whitespace-sensitive, like Python.  Indentation opens a
block; dedenting closes it.  Lines starting with `#` are comments.  Each
top-level construct begins with a keyword: `fact`, `rule`, `abduce`,
`constraint`, `fn`, `type`, `data`, `relation`, `instance`, `import`,
`export`.

```
fact depends:
    main.o    <- main.c
    main.o    <- header.h
    parser.o  <- parser.c

rule stale(Target):
    depends(Target, Dep)
    newer(Dep, Target)

constraint valid_alignment(x: SampleId, y: Reference):
    x != y
    exists("{x}.fastq")
```

== Functional programming in KB

Most logic problems contain a few "purely computational" steps that have
nothing to do with search.  KB lets you write those as functions, with a
small functional sub-language that is similar in feel to Haskell or Scala
but much smaller.  Functions are pure (they do not perform input or output)
and may use lambdas (`x => expr`) and a left-to-right pipeline operator
`|>`:

```
fn stem(path):
    path |> split(".") |> head

fn align_cmd(sample, ref):
    "bwa mem {ref}.fa {sample}.fastq"
```

You can call functions from inside rule bodies, allowing logical and
computational steps to interleave naturally.

== Gradual typing

Types are optional.  When you write them, the parser checks that calls
agree with declarations.  When you do not, the engine treats values
dynamically.  This _gradual_ approach lets beginners start without types
and add them later as confidence grows:

```
fn align_cmd(sample: String, ref: String) -> Command:
    "bwa mem {ref}.fa {sample}.fastq"

type SampleId = String where matches("[A-Z]{2}[0-9]+")
```

The `where` clause attaches a refinement: a `SampleId` is a string that
also matches the given regular expression.  Refinements compose with
constraints: when a value flows into a position typed `SampleId`, the
engine asserts the refinement.

== Type relations and nested instances

Suppose you want to write a function that aligns reads, but the way you
align them depends on the queue you are using (local, SLURM, GPU, …).
Many languages solve this by defining an interface or trait; KB calls the
mechanism a _relation_ and it can take more than one type parameter at
once:

```
relation Processable(Input, Output, Engine):
    fn process(input: Input, engine: Engine) -> Output
```

You then provide _instances_ of the relation.  An instance for a specific
combination of types implements the function.  Instances may be declared
anywhere — they need not be inside the relation block — and they may be
_nested_:

```
instance Processable(Dataset, Model, GPU):
    fn process(data, engine):
        train(data)

    instance Batchable(Dataset, Model) where Engine == GPU:
        fn batch_size(input): estimate_vram(input)

        instance Shardable(Dataset) where Dataset == LargeDataset:
            fn shard_count(input): input.size / max_shard_size
```

A nested instance inherits _every_ `where` clause of its ancestors.  The
innermost instance applies only when `Engine == GPU` _and_
`Dataset == LargeDataset`.  This lets you express layered preconditions
without writing them out repeatedly.

== Imports and modules

A KB file is a module.  You can split a project across files and pull
parts into scope:

```
import bio.alignment (align, index)
import utils.paths   as P
```

`import` may also appear inside any block.  When it does, the bindings it
introduces only live as long as that block.  This is useful for keeping
big projects from accidentally pulling everything into the global
namespace.

= Running things in parallel

== From a graph to a plan

Once you know which targets are stale and which depend on which, you have
a directed acyclic graph (DAG).  Building it efficiently means scheduling
the nodes so that dependencies finish before their dependants and so that
independent work runs in parallel.  This is exactly what `lu-par` does.

The input to `lu-par` is a small text file with one line per task:

```
ID<TAB>DEP1,DEP2<TAB>COMMAND
```

`lu-par` validates that the graph is acyclic (using Kahn's algorithm, which
you may have met as topological sort), then dispatches tasks to a pool of
worker threads.  When a worker finishes, the in-degree of every successor
is decremented; successors that reach in-degree zero become eligible.

== Recovering from failure

Real workflows fail occasionally.  `lu-par` offers three useful behaviors:

- `--retry=N` re-runs a failed task up to $N$ times.  Useful for flaky
  tests or transient network errors.
- `--keep-going` allows independent branches of the DAG to continue even
  after a sibling fails, instead of stopping the world.
- `--transaction` treats the whole DAG as one atomic operation: if any
  task fails after retries, the freshness records of completed tasks are
  rolled back via `stamp`, so the next run sees those targets as stale
  again.  Used together with content-based freshness this is a small
  but powerful safety net.

== Beyond one machine: queues

When the machine in front of you is not big enough, you submit work to a
cluster.  A cluster is, abstractly, a queue: you hand it a description of
what to run and it gives you back an identifier that you can use to ask
about the job's progress.  Different cluster systems (SLURM, SGE, PBS, …)
have different commands and flags, but the idea is the same.

`lu-queue` puts the same idea behind a single CLI:

```sh
JID=$(lu-queue submit --engine=slurm --slots=4 --mem=16G -- \
      align sample1 hg38)
lu-queue wait "$JID"
```

The flag `--engine=local` schedules in worker threads of the current
process; `--engine=slurm` translates the generic flags to native SLURM
options.  Switching from a laptop to a cluster becomes a one-flag change.

= A worked example

We close with one example that ties most of the pieces together: a small
build that compiles every C file into an object file using content
fingerprints to decide what is stale, and then runs the compilation in
parallel.

== The setup

```
project/
├── src/main.c
├── src/util.c
└── include/util.h
```

== Step 1: produce a dependency graph

We use `gcc` to learn which `.c` files include which `.h` files:

```sh
gcc -M -MM -Iinclude src/*.c
```

`gcc` prints rules of the form `main.o: src/main.c include/util.h`.  We
pipe this into `lu-deps` to convert it to the format `lu-par` expects:

```sh
gcc -M -MM -Iinclude src/*.c \
| lu-deps --from=gcc --to=tsv > deps.tsv
```

`deps.tsv` now has one line per object file with its dependencies.

== Step 2: turn it into runnable tasks

Each line of `deps.tsv` is missing a command column.  A short `awk`
program inserts the compile command and the freshness check:

```sh
awk -F'\t' 'BEGIN{OFS="\t"} {
    cmd = "freshcheck --method=hash " $1 " " $2 \
          " || gcc -c " $1 ".c -o " $1
    print $1, $2, cmd
}' deps.tsv > tasks.tsv
```

== Step 3: run the build in parallel

```sh
lu-par -j 4 --progress --transaction --taskfile tasks.tsv
```

`-j 4` says four workers; `--progress` prints task starts and finishes to
standard error; `--transaction` rolls back the freshness store on
failure.

== Step 4: record the new fingerprints

After a clean run, record the new content fingerprints so the next run can
skip:

```sh
stamp record --method=hash *.o
```

Reading the four steps end-to-end, you can see the philosophy at work: no
single tool was responsible for the whole job; instead, each tool did one
small thing and the shell composed them.  When tomorrow's task is
different — say, you need to dispatch the compiles to a SLURM cluster — you
swap one of the tools (`lu-par` for `lu-queue`) and the rest stays the
same.

= Where to go next

== Read the man pages

Each utility ships with a man page in `docs/man/`.  They are concise but
authoritative.

== Read the agent reference

The directory `docs/agents/` contains a structured reference written for
machine-readable consumption (AI assistants and the like).  Humans can
read it too; it is a useful complement to this gentle introduction
because it lists every flag and edge case in one place.

== Try the KB language

Run the test suite with `cargo test --workspace` to see the parser in
action, then write a small KB file and ask `lu-query` questions about it.
Start with deductive rules; once those feel familiar, try abduction and
constraints.

== Build something

The toolkit is most useful when you have a real problem to solve.  Pick a
small project — maybe a build for a multi-language repository, or a data
pipeline — and try to express it with the toolkit.  When you encounter
something the toolkit cannot do directly, ask whether the gap belongs in
your shell glue or in a new tool.  That is the same question Unix
programmers have been answering for fifty years.
