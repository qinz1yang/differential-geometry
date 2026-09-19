# Claude takeover: Moise integration

Prepared 2026-09-19 around 23:40 UTC after the owner requested that Codex stop
because usage is almost exhausted and hand the project to Claude. This is a
takeover checkpoint, not a new theorem acceptance. Codex automation `moise`
is PAUSED. All five existing tasks have received an explicit stop instruction.
No Lean or Lake process was present in the 23:39:49 UTC process snapshot.
Do not reactivate Codex tasks or its automation during Claude's takeover.

## Paste this prompt into Claude

You are taking over the Moise Lean integration project. Continue the owner's
mathematical work from the saved state below, preserving all uncommitted work.
First reconcile current files, receipts and paused-worker reports. Do not start
with a full-library rebuild, reset a worktree, delete an artifact directory or
overwrite a whole shared module from another checkout.

Integrate only in `D:\differential-geometry-moise-int`, branch
`codex/moise-integration`. The latest published checkpoint before this handoff
is `cd3b182bf0db20a18b25122e61216209d6f2e5d2`; the last independently accepted
Lean checkpoint is `08248ce9d78ede909d88e657872b48abe2fc8034`.
Later commits may archive this handoff without accepting the currently dirty
Lean source. Check the actual HEAD and complete diff first.

Read in order:

1. This file, then `.lake/claude-handoff-state-20260919.json` for the final
   per-worktree snapshot and received pause acknowledgments.
2. `DifferentialGeometry/Topology/PiecewiseLinear/MOISE_PLAN.md` top live
   frontier, `LOOP_THEOREM_RISK_PLAN_20260919.md`, `FOUR_LANE_WORKFLOW.md`, and
   the latest `HANDOFF_CODEX_INTEGRATION.md` sections 95--98.
3. `.lake/coordination-current.json`, `.lake/resumed-stage-20260919.json`,
   `.lake/compiler-policy.json`, and `.lake/round-compiler-leases/*.json`.
4. The repository AGENTS.md, NAMING.md and STRUCTURE.md. The owner also asked
   that dictionary.md, AGENT.md, CLAUDE.md, convention.md, BOOK24_LEAN_STATUS.md,
   lessons.md and important_lesson.md be consulted; their original named paths
   are in `E:\differential-geometry-dev`. Resolve conflicting historical plans
   by the owner's latest decisions, current source and evidence.

Required headers/module docstrings are allowed; other non-vendored Lean
comments/docstrings, new proof debt, resource overrides and linter suppression
are not. Exact declarations/proofs and compiler/axiom evidence outrank plans
and author reports. Preserve old public signatures unless a deliberate,
coherent generalization is recorded. No scratch probes in the project tree.

### First local action: finish or honestly preserve batch 64

Four integration Lean files are dirty, copied from the exact frozen F commit
`fad7930be31bdbcc77b97e63cbae2aca339abe6e`:

- GeneralPosition.lean
- HeightProjection.lean
- SingularGeneralPosition.lean
- LoopTheorem/ProjectedSheetPerturbation.lean

All paths are under `DifferentialGeometry/Topology/PiecewiseLinear`.
Do not revert them or replace them with F's newer active files. They are the
protected-polyhedron relative-general-position layer. Seven modules have
already compiled successfully with zero diagnostics: these four plus the old
HalfSpacePerturbation, HalfSpaceGeneralPosition and ProjectedBoundaryPosition
consumers. The combined audit also completed successfully at 23:30:05 UTC:
322 nonautomatic native declarations, 10 critical reuses, 13 probe declarations,
13 applicable environment linters, only foundational axioms. Probe categories
are five positive geometry assertions, six helpers and two generated macros;
they are not 13 full NormalSystem models.

Evidence directory:
`C:\Users\liao9\AppData\Local\Temp\codex-integration-sixtyfourth-batch-20260919`.
Read `module-scope.json`, `changed-source.json`, `author-evidence-manifest.json`,
`compile-timings.json`, `external-audit.json`, `audit-timing.json`, `census.json`,
`expected-census.json`, `private-prerequisite-reuse.json`, and the actual setup
files. The independent audit took 57.9625805 seconds; exact module timings are
in the receipt file. No full-root build was run, and no shared artifacts changed.

The audit was finished before the pause; the final source/signature review,
canonical setup binding review, final acceptance receipt, documentation,
staging, commit and push of batch64 are NOT finished. Do not report it as
independently accepted yet. Complete those remaining inexpensive checks
against the frozen source and existing successful outputs before deciding
whether a rerun is necessary. Use batch63's review scripts as a template, not
as an unmodified script: this batch has four changed modules, 322 declarations,
five new public theorems and an explicitly authorized removal of the unused
FiniteDimensional instance on `neighbors_eq_pair_of_transverse_cofaces`.
All its native calls are in GeneralPosition. HeightProjection and
SingularGeneralPosition have identical noncomment/nonwhitespace tokens to
the previous integration source; their changes are authorized wrapping and
required headers. Other old public signatures were source-compared unchanged.
The actual old/new scopes still need the final recorded review.

Mathematical scope: the general producer fixes an actual closed polyhedron Q,
constructs the compatible subdivision itself and gives crossings outside Q.
The flat-core consumer also retains crossings on the protected core using
the actual simultaneous flat sheets and quantitative displacement. The final
disk consumer assumes its support lies in the interior and preserves the
original boundary pointwise. This does not yet handle arbitrary boundary
charts or complete global projected-disk normalization. Later F commits
478a65991/0c080405f and its current dirty half-space extension are outside this
batch and require separate frozen-source acceptance.

### Highest-risk mathematics: 25.2

The owner explicitly increased 25.2's weight. The intended allocation is four
lanes on the Loop Theorem and one on independent compact PL smoothing. This
is a mathematical plan for Claude; the Codex tasks are now paused.

- F: normalize the actual projection of an upstairs embedded disk, preserving
  the same cover, domain/boundary and subgroup avoidance. Finish full jointly
  selected protection/transition/core coverage, normal crossings and the
  one-dimensional singular set.
- M304: upstairs Lemma2/L2 surgery. It was formally transferred at the complete
  e8dc3d37d delivery and has begun ambient deck and intersection producers.
- h: whole-branch simultaneous two-sheet PL slab charts, correct endpoint
  faces and deck-conjugate side choices. It was formally transferred at its
  5fb0d0617 delivery during the last heartbeat and merged the integration
  branch. It must not resume the old 35.1 lane by default.
- E3: after safely preserving its current Q.2b work, sphere-base/tower-interface
  assembly. This change had not been sent before the global stop.
- S: preserve the independent compact smoothing lane, currently actual
  branch/gamma gluing and relative original-function normal form.

Do not revive arbitrary raw-NormalSystem normalization as the main path.
Actual EmbeddedDisk projection already gives local injectivity, fibers at
most two, exact boundary trace, subgroup avoidance and the double-point
cover. Normal crossings and genuine whole-branch geometry are additional.
SphereNeighborhood finite complementary disks and SphereCase inward-push /
EmbeddedDisk / original-boundary return producers already exist. The
orientable Moise252 essential-boundary contract is already repaired.

Keep tower vertex-collision complexity distinct from normal-disk branch
complexity. Upstairs surgery must construct an embedded replacement, actual
intersection control, boundary-word avoidance and strict branch descent; two
named embedded sheets do not automatically give transversality or no new
branches. Reuse the canonical projection once rather than rebuilding its
bookkeeping per case. The existing induction's NonsingularCell has a fixed
target triangulation; the actual EmbeddedDisk output and properness/basepoint
invariants still need a natural, compatible assembly.

New precise M304 interface finding, not yet resolved: DoubleCoverDiagram's
actual covering domain is T.ambientComplex.space, whereas EmbeddedDisk T and
the current canonical projection consumers restrict the disk to
T.manifoldComplex.space and its boundary to T.boundaryNeighborhoodSpace.
Deck-transformed pieces are not known to remain in those smaller neighborhoods.
The natural upstairs L2 support may instead be the actual whole cover with
boundary in the preimage of the original downstairs boundary neighborhood.
Do not assume deck invariance of T's smaller regular neighborhood. M304 is
first proving ambient deck/intersection facts in new leaves, with a later
minimal projection generalization only if needed, preserving old statements
as corollaries. No edit permission to F's canonical projection files was
granted for this potential change, and no new avoidance producer is proved.

### Worktrees and verification frontiers

All five worktrees belong to the same repository but contain independent
unmerged work. Never hard-reset, clean or overwrite them to synchronize.
The final state JSON refreshes these snapshots after pause acknowledgments.

| Lane | Checkout | Snapshot HEAD | Independently accepted author frontier |
| --- | --- | --- | --- |
| F | D:\differential-geometry-moise-plan | 0c080405fa4c35d22db981b2060399dd06321ffb | d68c5adc5 in integration08248ce9d; fad is current unfinished batch64 |
| h | D:\differential-geometry-moise-h | 10264ff04200cb2859fd13aa1abc481093065e28 | e85a235df; later72/c1bd/055/b123/5fb pending |
| E3 | D:\differential-geometry-moise-e3 | 1dff5b63c34cb7cd5aa1bacf28aa8aa3e0b17665 | 1dff in integrationeab23c739 |
| S | D:\differential-geometry-moise-s | e24808bcef043e8048572025c351fe35584a5d41 | c0f4df1b1; later5b/c011/2544/876/c60/e248 pending |
| M304 | C:\Users\liao9\.codex\worktrees\ef23\differential-geometry-dev | 1fb9a99d97bc2d72391708ac5e46cca9f1badc3f | 3717074e9 in integrationf7cd03685; later6f/823/878/546/e8 pending |

At 23:39 UTC F had dirty HalfSpaceGeneralPosition/HalfSpacePerturbation;
E3 had untracked AnnularExhaustion; S had a dirty root plus untracked
Analysis/ODE/InvariantAxis, Topology/Manifold/IntegralCurveCoordinates and
Topology/Morse/SaddleConnectionAxis. M304 had untracked LoopTheorem/DoubleCoverDeck,
LoopTheorem/DoubleCoverIntersection, CylindricalTorus and SurfaceSphereCompression.
The latter two are deliberately preserved old torus drafts. h was clean.
No dirty file is automatically a passing or completed proof.

Frozen evidence:

- Batch63: `C:\Users\liao9\AppData\Local\Temp\codex-integration-sixtythird-batch-20260919`.
  Includes M304 shell-homology's 330 files/52 source-receipt groups and S's
  e248 exact evidence plus objects. The old M304 unresolved-root checkpoint
  is invalid; use only recognition-final/sphere-exclusion/Hurewicz-one/
  shell-homology checkpoints identified in the ledger.
- Batch64: same prefix with `sixtyfourth`; includes F353 exact sources/audit,
  h's new 5fb chain source/compile-object freeze and the h risk dispatch.
  h's separate new strict audit files still need locating before independent
  replay; native compile receipts alone are not complete acceptance.
- F later raw author evidence: `C:\Users\liao9\AppData\Local\Temp\moise-f-boundary-20260918`,
  AuditF354/F355 and exact `*-F354-final.*` / `*-F355-final.*` snapshots.

M304's conditional sphere endpoint is accepted: actual
`moise304_of_moise252`, original shell/targets, least-Betti separator and
strict compression descent. Kernel type and proof-body traversals omit
Moise303 and wide Moise264. Moise252 remains unresolved; tame305 retains its
outer-frontier bicollar, and wild305 remains open. Later actual Betti2/Euler0
toroidal-shell separators are not PL torus recognition. 25.2 is not the sole
remaining input of all section34 or compact smoothing.

S's small prescribed-frame cancellation counterexample remains valid.
Later enlarged-strip cubic cancellation and the actual descending-branch
producer need adequate support, compact inward barriers and adapted local
field geometry. The latter are explicit inputs, not yet supplied by the
compact smoothing endpoint. Preserve the original f/atlas/v/gamma and actual
branch. A radial-line equation alone does not identify gamma with the other
radial side; the local invariant-axis work addresses this real gap.

### Running and resuming checks

The owner stopped Codex use, including automatic checks. Leases are paused
for the handoff. Claude may resume authorized work after checking ownership
and explicitly reissuing the relevant local administrative lease; do not
resume the Codex automation. Compiler policy remains at most two private
checkers, one per lane; root at most one worker; total Lean at most three.
Do not launch a full root build unless actual compatibility requires it.
There is no time-based rebuild trigger and no current user deadline.

Canonical helper:
`C:\Users\liao9\AppData\Local\Temp\codex-moise-lane-check-round.ps1`.
For independent integration use the corrected `integration-checker.ps1` in
batch64. It binds each override only to that batch's canonical
OutputRoot/module.olean and the matching integration source/receipt.
Do not recursively select objects from frozen author or previous-attempt
directories. Reuse objects only with matching accepted source and object
hashes. Keep exact raw and normalized source identities separate.

The latest narrow additional grants before pause were S's new exact
Analysis.ODE.InvariantAxis leaf and M304's read-only private compile of
Topology.Covering.EmbeddedProjection. The latter's raw SHA256 is
87206dfa81f15e34615e2308bccc762cc274e26ecf91dbce7f1ddcff5d735ad6.
These grants do not permit broad writes or extra workers. Substantial shared
public-interface changes still require checking actual ownership.

When a layer passes actual statement/model review, complete module compilation,
all nonautomatic declarations and critical-reuse axiom closure, applicable
standard lint and consumer/root-registration review, checkpoint only its
intended dependency-closed files and push the feature branch normally.
Never force-push or treat green compilation, code volume, conditional consumers
or an author's report as a completed headline theorem. Record remaining
mathematical gates precisely and update the live plan and resumed-stage ledger.

## Final pause reconciliation

All five tasks were confirmed idle by the app after the stop instruction.
Automation moise is PAUSED; all seven lane/integration compiler leases are
paused. The final state file includes current HEADs, complete dirty-file lists,
raw hashes, and preserved copies plus binary Git patches under batch64
claude-handoff-snapshots. No theorem was accepted during this archival step.

M304 additionally delivered HANDOFF_CLAUDE_M304_PAUSED_20260919.md in its
author checkout. Its last checker had already failed at DoubleCoverDeck:78
(hfiber set-equality transport); DoubleCoverIntersection has never compiled.
Its four untracked Lean drafts remain unverified and uncommitted.
