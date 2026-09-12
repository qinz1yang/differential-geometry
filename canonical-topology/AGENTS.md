# Poincare checkpoint agent instructions

## Required study

Before work, read [PROJECT_CONTEXT.md](PROJECT_CONTEXT.md), this file,
[NAMING.md](NAMING.md), [STRUCTURE.md](STRUCTURE.md), and the package README.
The enclosing controller's [canonical AGENTS.md](../../AGENTS.md) governs the
mandatory repository study. Every agent must personally read its current skills:

1. [prove-theorem-suite](../../skills/prove-theorem-suite/SKILL.md) and
   [statement audit](../../skills/prove-theorem-suite/references/statement-audit.md).
2. [audit-lean-theorem-suite](../../skills/audit-lean-theorem-suite/SKILL.md) and
   [acceptance gate](../../skills/audit-lean-theorem-suite/references/acceptance-gate.md).
3. Both skills' agent metadata:
   [proof metadata](../../skills/prove-theorem-suite/agents/openai.yaml) and
   [audit metadata](../../skills/audit-lean-theorem-suite/agents/openai.yaml).

Inspect that skills directory for additional instructions and required
references. Read the current [active plan](../../plan/plan_smooth_schoenflies.md),
[two-project prompt](../../plan/della_two_projects_prompt.md),
[topology brief](../../plan/CANONICAL_TOPOLOGY_SPINOFF_BRIEF.md), and the exact
assigned source. These links refer to the enclosing Della controller checkout;
they are not bundled package dependencies. A standalone copy must obtain those
instructions before resuming the combined task. After a context reset, reread
the skills and active plan. A parent agent's summary is not a substitute.

## Mathematical and source policy

Preserve the Poincare objects, namespaces, exact dependency pins and separate
project. Search the existing project, pinned Mathlib and appropriate upstream
source before creating new APIs. Put reusable mathematics in its natural topic
home, keep one-proof mechanics private, and register public leaves in the flat
`Poincare.lean` aggregate.

Treat source TeX and historical records as mathematical/reference material.
Never add `sorry`, `admit`, new axioms, opaque proof substitutes or hypotheses
that package the requested conclusion. Closed foundations require transitive
axioms contained in `propext`, `Classical.choice` and `Quot.sound`. The missing
frozen contract cannot be replaced by an invented interface or new deferrals.

Preserve inherited source documentation and third-party attribution. The
attribution/change notice in `Poincare/Analysis/LocalDerivativeHomotopy.lean` is required
for its adapted upstream source. New original Lean code follows the enclosing
project's source discipline. Retain strict source and declaration linters;
repair diagnostics instead of suppressing them or raising proof budgets.

Use narrow checks during development. Before accepting a checkpoint, verify
fresh changed sources, affected dependents, the package root, public consumers,
exact signatures and transitive axioms on the same final snapshot. Normal build
progress is permitted; unsolicited diagnostics are not. Run `git diff --check`
and inspect the complete intended diff. A source check is not an aggregate build.

## Current Della execution and delivery authority

The owner's 2026-09-12 instructions supersede historical machine and publication
directions in the recovered provenance records. Keep the lightweight controller
in the existing Della tmux session. Never retry SSH to `della-vis1`.

All sustained compilation, Kimina and Lean REPL checks run under Slurm on CPU
compute nodes, using `--account=karthikn --partition=cpu --qos=short`, one CPU,
and memory sized from measured requirements. No GPU is needed. Keep
`LEAN_NUM_THREADS=1` and one active proof check across both projects. Reuse the
long-lived shared allocation and distinct warm project sessions; the main
controller owns Slurm, services, queue operations and allocation renewal.
Do not submit a separate allocation for each check or duplicate a pending job.

Reuse the existing exact sources and caches offline. Do not download, upgrade,
delete installations, alter existing dependency remotes or activate a different
toolchain. The owner's exception permits a separate Kimina/runtime installation
only if absent. Local path manifests and writable artifacts remain ignored and
separate from the portable package configuration.

The owner authorizes verified additive checkpoints on the existing `ayush`
branch of `https://github.com/qinz1yang/differential-geometry-dev`. The main
controller performs commits and pushes after review. Never push the recovered
Poincare root history over this branch, force-push, or replace the existing
Schoenflies project. Preserve unrelated changes.

Keep the existing combined goal active while useful independent work remains.
A status question does not pause proof development, and missing topology
handoff material does not pause Schoenflies. Do not create a duplicate goal.
