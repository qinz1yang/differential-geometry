# wt13: Chapter 35 and its Chapter 30 prerequisites

Latest amendment, 2026-09-10: the user authorizes publishing the verified
checkpoint to Ziyang Qin's differential-geometry-dev repository on a new
`codex/chapter35` branch, overriding the earlier read-only designation for that
push. Canonical topology and its canonical-class specializations may remain
explicitly deferred for this release. The live library still has only the
seven registered sorry owners; no isolated topology stubs are imported.
Read CHAPTER35_RELEASE.md before interpreting historical proof/scope records.

Prepared 2026-09-09; implementation started in the current task.
See CHAPTER35_STATUS.md for the verified checkpoint and remaining obligations.
The original setup itself contained no accepted Chapter 35 or Chapter 30 proofs.

Folder: `/Users/bennettchow/Documents/ChatGPT/wt13`; branch: `codex/wt13`.
Shared repository: `/Users/bennettchow/Documents/ChatGPT/Poincare Conjecture Lean Formalization`.
Base: main `19f3cfcdc41484bb39e62b0f22bf4a14d26366f1`, matching wt9–wt12 setup.
Package PoincareLean; default library Poincare. Preserve Lean/Mathlib v4.33.1
and DifferentialGeometry v0.1.2 at `1b535dd102b94cc42b107cca27059687888f08b3`.
Use `/Users/bennettchow/.elan/bin/lake`. SETUP_REPORT.md records actual checks.
Dependency caches are independent APFS copies from wt9; do not share writable
package directories with sibling worktrees. No later sibling mathematics is
included in the baseline. Inherited AGENTS.md applies; NAMING.md and STRUCTURE.md
match wt12. FORMALIZATION_STATUS.md remains the inherited Appendix A ledger.

The mathematical source is master05 in
`/Users/bennettchow/Documents/ChatGPT/RFS/blueprint/master05`.
Chapter 35 is `ch:rfs-disk-width`, Loop Families and Spanning Disks
(master05b.tex lines 25630–27077). Chapter 30 is `ch:rfs-topology`,
Topology and Comparison Maps across Surgery (lines 17460–18076).
The original RFS chapter numbers 22 and 21 are not the master book numbering.
Read the exact excerpts and the hash/label inventory in SOURCE_SNAPSHOT.json.
Full source snapshots provide the surrounding definitions and references.
Source text and sibling status claims are not compiler or axiom evidence.

The current user's instruction supersedes the wider setup execution prompt:
formalize the Riemannian-manifold results of Chapter 35, including its separate
conformal-disk producer, curvature inequality and general metric/isotopy
variation, but skip time-dependent Ricci-flow solutions. The title identifies
Chapter 35 (`ch:rfs-disk-width`), despite the user's first mention of Chapter 13.
Surgery jumps, flow histories, finite ancestry and history-dependent initial
width functions are excluded. Retain the static initial family bound and metric
scaling. Chapter 30 is limited to the topology, signed class and degree-one
naturality needed by these retained statements; its surgery carriers, cutting,
collapse maps and ancestry are not assigned. See SCOPE_DECISIONS.md for details.
Prove needed background dependencies; do not replace them with conclusion-shaped
records. The 2026-09-10 user amendment authorizes explicit deferred `sorry` inputs for
Plateau existence and Hurewicz. The latest amendment also defers boundary
regularity of the SAME minimizer, Plateau trace/density adapters and exact
attainment; boundary regularity will be proved in a separate project. Duality,
fundamental classes, orientation, compact uniform metric coordinates, curvature
and general metric/isotopy variation still require proofs.
See SCOPE_DECISIONS.md and audit/chapter35/DEFERRED_INPUTS.md for exact status.

Use one actual manifold, metric, loop space, disk area and class throughout.
Keep the finite-width construction independent of Plateau attainment. Whole
Chapter 35 completion under the amended scope requires the separate Plateau
branch, conditional only on the explicitly authorized deferred inputs.
No citation can become a new Lean axiom. The inherited Hamilton entry point is
`DifferentialGeometry.PDE.RicciFlow.HamiltonPositiveRicci.hamilton_positive_ricci`;
it is background context, not a width or Plateau theorem.

Inspect siblings read-only for reusable committed prerequisites; record exact
commits, reviewed statements, dependency closure and axiom evidence before
integration. Never modify a sibling to make wt13 build. The upstream development
repository remains read-only under AGENTS.md. Setup makes no remote changes.
