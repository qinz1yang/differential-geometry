# Four-lane round workflow

Effective 2026-09-19 UTC, following the owner's supplied four-lane workflow.
This file governs coordination; mathematical status remains in the integration
handoff and the individual lane handoffs.

## Ownership and round boundaries

- F: projected embedded disks and source-faithful double-cover reduction,
  gpt-6-astra, max.
- h: repair the Moise252/331/351 contracts and regular-neighborhood witnesses,
  gpt-5.6-sol, max.
- E3: Moise 30.4 assembly, starting with the 30.3 splitting/separation step,
  gpt-5.6-sol, max.
- S: mapping-torus, Moebius, and orientation constructions, gpt-6-astra, max.
- The coordinator validates, integrates, records decisions, and supplies exact
  interfaces. It does not write the main mathematical proofs.

The owner upgraded h and E3 to Sol max for subsequent assignments on 2026-09-19
UTC. Apply the explicit model and effort on their next dispatch; do not interrupt
an active round merely to change its setting.

Use the four existing tasks, with one lane per task. Do not create subagents.
Give each lane a dependency-aware mathematical round, normally 15--60 minutes of
work, rather than requiring a new assignment for every small lemma. This is a
planning scale, not a forced time limit. Checkpoint each dependency-closed,
compile-clean layer and continue within the assigned round. Report a completed
round or the first genuine mathematical/API blocker. Do not manufacture another
conditional wrapper merely to keep a blocked lane active.

Do not interrupt a running lane for status. Handoff at delivery or for an urgent
stop/restart. Interface corrections that would invalidate active work qualify
as urgent; routine requests and unchanged reports do not. While waiting for
verification, continue independent source work when possible. Never count an
active turn containing waits as continuous mathematical work.

## Assignment and evidence

Each assignment supplies the mathematical endpoint, current actual signatures,
known false routes, allowed files, other lanes' ownership, verification rules,
and remaining obligations. The coordinator searches current source first.
The lane searches by content and type shape, reads constructions, checks search
exit codes, and checks a concrete nondegenerate instance before proving a new
interface. Reuse existing producers before adding infrastructure.

Consume another lane's source only through the integration branch. Merge the
integration branch after preserving the lane's own clean checkpoint. Keep one
handoff file per lane. Changes to a shared public signature must update and
verify its actual consumers, including fixed-length destructuring patterns.
Do not assume that strengthening a conclusion preserves all consumers.

Required copyright/authors headers and brief module documentation are allowed
by the owner's explicit exception. Other project source and soundness rules
remain binding. Register new leaves in the flat root aggregate. Keep diagnostic
Lean probes outside the project tree. These current rules supersede the older
workflow's no-header, no-root-import, and in-tree-scratch instructions.

## Compiler trial

The independent full-source build continues with one Lean worker. The trial
allows at most two lane checkers and three total Lean processes, below the
owner's ceiling of four. Each lane has at most one checker. A named mutex and
per-process reservations coordinate admission; at least 12 GiB of free commit
headroom and 4 GiB of free physical memory are required before another checker
starts, with a 4 GiB reservation for each pending startup.

The checker waits for resources itself, for at most ten minutes per invocation.
Do not use repeated model turns to poll for a token. A round authorization
covers its named mathematical module family and private output directory;
it is not permission to edit another lane's files. Authorization is recorded
under `.lake/round-compiler-leases/`. The helper is
`C:/Users/liao9/AppData/Local/Temp/codex-moise-lane-check-round.ps1`.

Shared artifacts remain read-only. Private import overrides require successful
receipts and exact current source hashes. Recompile affected consumers after a
public change. The trial preserves strict header/long-line checks, the standard
syntax lint set, and all 13 applicable environment linters. Only docBlame and
docBlameThm are excluded. Every nonautomatic completed declaration and critical
reused producer must pass the transitive foundational-axiom audit.

The admission helper passed an external Lean probe with exit 0 and zero
diagnostics on 2026-09-19 UTC. Its actual concurrent resource behavior remains
a trial to be assessed at delivery boundaries, without routine lane interruption.

## Integration and accounting

Review the complete scoped diff, worktree ownership, source provenance, branch
and remote state, prohibited constructs, and exact mathematical claims.
Recompile every changed leaf in the integration checkout, and audit cross-import
compatibility. Keep local verification separate from the continuing independent
full-source gate. Preserve raw and normalized source identities when Windows
line endings differ. A clean Git push is archival evidence, not proof evidence.

Report exact declarations, check durations and exit codes, audit coverage, and
remaining obligations. Distinguish newly written source, verified deliveries,
unverified drafts, and completed headline theorems. Commit counts and module
counts are not proof-completion percentages. Record decisions, corrections,
and negative results with enough evidence to avoid repeating a false route.
