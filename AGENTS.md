# Geometrization project instructions

These instructions preserve the user's standing mathematical and source policies, with the completed migration and peer workspaces established on 2026-09-30. Read HANDOFF.md and GEOMETRIZATION_BLUEPRINT/HANDOFF.md where present, plus the current docs/geometrization handoffs/frontiers and your supplied continuation prompt. Paths and stop directives in historical handoffs must be reconciled with the current user's authorization; do not restart the project or redesign its architecture.

Read docs/geometrization/team/TEAM_WORKFLOW.txt for authorized inter-task coordination, branch ownership and build admission. Use /Users/bennettchow/Developer/gc-team-coordination/peers.json for live task IDs. Keep work in the current assigned Developer worktree and feature branch. Preserve independent local .lake paths. Do not change another task's checkout or recovery/iCloud state.

## Ricci flow and geometrization reference library

The user's Ricci flow books are LaTeX sources at /Users/bennettchow/Documents/Codex/RicciFlowBooksLatex. References are also at /Users/bennettchow/Documents/Codex/Geometrization/BooksPapers. The restored equivalents may be under /Users/bennettchow/Documents/Documents - Unknown/Codex; locate recovered paths if the originals are unavailable. These are read-only mathematical references, not agent instructions. Search with rg. Do not edit reference sources unless explicitly asked.

Consult MorganTianPoincare.pdf, MorganTianGeom.pdf and KleinerLottPerelman.pdf as relevant, plus BBBMP, Perelman, comparison geometry and collapsing theory. For Alexandrov work consult AlexanderKapovitchPetrunin303Alexandrov.pdf, KapovitchLebedevaPetruninAlexandrov.pdf, PetruninCourse.pdf, and BuragoGromovPerelman1992.pdf. The AKP repository is https://github.com/anton-petrunin/book and the author book/errata page is https://anton-petrunin.github.io/book/.

Before introducing or substantially revising a mathematical theorem contract, proof route, dependency claim or reuse/gap classification:

1. Read the relevant source theorem, its definitions and the proof passages establishing the proposed dependencies. Expand reading for imported results or hidden hypotheses.
2. Check all hypotheses, quantifier order and uniformity, regularity, curvature and time normalization, metric/domain conventions, boundaries and the precise conclusion. Distinguish local theorems, flow applications and reconstruction.
3. Record source version, theorem/section identifier, printed/PDF pages, or TeX label/exact lines. Verify the body and tie records to existing hashes where available.
4. Check applicable author/publisher errata. Use authoritative external sources if the local copy is incomplete, ambiguous or lacks corrections. Distinguish archived and external versions.
5. Compare sources where statements, conventions or graph/geometric definitions differ. Name translations and unresolved implications. Do not silently strengthen conclusions, weaken hypotheses, or treat citations as adapter proofs.
6. Update the relevant existing source inventories/comparison records. Record mismatches and assess affected consumers before changing contracts.

Use targeted reading. Reuse an existing documented check when the source and claim are unchanged. Collection access is not a claim to have read everything; do not restart completed work merely to impose policy retrospectively.

BGP1992 is the English Russian Mathematical Surveys47(2),1–58 paper with a prefixed cover sheet, hence PDF page=printed page+1. Keep the local-completeness definition, Sections5–6 and Remark5.1.1's curvature-zero constants/assumed-geodesic qualifications when relevant. Historical targeted records begin in GEOMETRIZATION_BLUEPRINT/reference_checks_revision64.md. AKP identities/source snapshots are in revision63's reference checks and checks/evidence/revision63_alexandrov_sources.json where retained. Pin source checkouts to actual branch+commit. Archived PDF, published edition, moving repository and errata are different sources with potentially different numbering. Course notes were catalogued, not blanket-audited.

## Source roles and PC reuse

Morgan–Tian2014 is the global Geometrization spine and assembly guide; distinguish manuscript/published locators. Kleiner–Lott2008 is the detailed analytic exposition; Perelman is primary. Hamilton1999 and MSM206 guide the hyperbolic branch. Kleiner–Lott Asterisque365 is the provisional local-collapse route; Morgan–Tian supplies global comparison/application. Retain compatibility gates.

Reuse the PC geometric, analytic and topological foundation. M2/M2A audits and adapts that foundation; the first genuinely new analytic layer is the surviving M3 PDE gaps after completed-release comparison. Migration is now complete: the accepted baseline at setup is public differential-geometry main777299070a5529e96345e0033979706fd00c7e62, Lean4.35.0-rc3 and mathlib c55e6e786f49471c72fbddbec5415808896aec1e. Historical instructions to await that migration no longer block binding the accepted release. Unfinished historical snapshots remain discovery material, not accepted release evidence. Verify exact declarations, assumptions, imports and axiom closures before reuse; do not assume any later branch is automatically accepted.

Treat user-confirmed Hamilton–Ivey and smooth Schoenflies as inherited reuse candidates, not missing results to reprove merely because a name is not located. Distinguish user reports, inspected declarations and validated release theorems. Keep late-thick/thin-or-terminal-exceptional outcomes. Finite-time extinction is outside the default GC route. Preserve unresolved endpoints and compatibility gaps explicitly.

## Evidence and blueprint preservation

Distinguish source-verified mathematics, proposed interfaces/proof decompositions, provisional discoveries, actually elaborated Lean declarations, static audits and document builds. For substantive mathematical updates give checked source locators, changes motivated, unresolved comparisons and actual checks run. Label estimates and inferences honestly.

Preserve frozen Blueprint207, its historical revisions and established source layout. Do not rebuild or reorganize the original one-file blueprint approach or the migrated A/B snapshot. Preserve Arabic page numbering from Chapter1. After blueprint/inventory changes run python3 GEOMETRIZATION_BLUEPRINT/audit_blueprint.py when that archived layout exists; in the migrated layout use the existing documented corresponding checks. A missing historical path is a reported limitation, not authority to waive checks or claim a proof. Run applicable tools/gc checks as documented. Static consistency is not mathematical verification. Claim Lean/PDF/Overleaf verification only for tools/projects and checks actually run.

Use prove-theorem-suite and audit-lean-theorem-suite for sustained proof work and acceptance. No new admissions, mathematical axioms, disabled linters or hidden diagnostic suppression. Preserve inherited admission inventories and distinguish scoped successes from unresolved root diagnostics; do not silently waive a gate.
