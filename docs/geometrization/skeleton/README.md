> **Current integration:** The user accepted the migrated 4.35.0-rc3 baseline. This folder’s source manifest and Lean declaration line locators now describe the integration checkout; historical receipts below remain scoped to their original environment. Use [the joint integration record](../integration/README.md) and `python3 tools/gc/check_integration.py` for the combined tree. The original 4.33 manifest and crosswalks are preserved under `integration/historical/skeleton_67f27962`. Current integration verification is still in progress.

# Blueprint 207 Lean skeleton

The September 30 improvement is a **partially completed skeleton-improvement task**, not a proof of Geometrization. The unchanged endpoint still depends on registered `sorry` theorems. The current manifest contains 48 mathematical modules, 214 authored declarations, and **22 direct admissions**. All 155 protected foundation modules and the three Blueprint 207 TeX files are preserved.

Work is in `GC_BASELINE_EXPORT`, private branch `codex/geometrization-blueprint-skeleton-207`, using Lean 4.33.1 and Mathlib `0df444a360eaa60ab8c11dca51a86af692955474`. No migration or second foundation is used. The manifest pins the baseline, toolchain, Mathlib, Lake configuration and audit implementation. No gate result here covers the separate 4.35 checkouts.

Read the [improvement report](IMPROVEMENT_REPORT_2026_09_30.md), [exact statement changes](STATEMENT_CHANGES_2026_09_30.md), [current receipt](evidence/verification.json), [full build](evidence/build.log), [fresh audit](evidence/fresh_audit.log), [public axiom output](evidence/improvement/axioms.log), and [module-scoped lint output](evidence/improvement/lint.log). Each receipt identifies its exact manifest and crosswalk hashes. A replayed Lake audit is distinguished from the separately requested fresh Lean elaboration.

The historical [mathematical review](review_for_chow_lu/geometrization_skeleton_mathematical_review.md) describes frozen commit `ea0fae60`; its counts and admission status are not current.

## Main changes

- The shifted area contradiction, curvature-radius positivity/infinity characterization, the LC89 common derivative function, and disk-area continuity from local disk comparisons have actual proofs. Compact derivative bounds, boundary matching, monotonicity, and disk/ambient transport have proved adapters.
- The selected-flow theorem is a proved composition of seven admissions: a profile-retaining flow, persistent late cut geometry, whole-ball derivative tests, a primitive meridian, attained disks, local disk comparisons, and upper barriers. The approved analytic-admissibility contract records the additional KL85/86.9 controls.
- The closed threshold is derived from a finite-curvature-scale threshold and the separate nonnegative branch. Nonnegative classification now returns a complete spherical, spherical-product, or flat model metric; three separate graph-recognition admissions are consumed by the original theorem.
- Closed raw-graph prime decomposition is derived from prime existence and graph closure for a specified sphere summand carrying an actual oriented finite connected-sum reconstruction.
- `GC.Topology` owns torus decomposition vocabulary. The capstone is in `Geometry/Flow/RicciFlow/LongTime/Geometrization.lean`. Numerical constants and dimension-generic compact manifold vocabulary replace accidental literals and duplicated surface data.

The flow order is **K → one flow → any cofinal nonempty regular-slice sequence → one A → tolerance/tail**. Curvature-scale collapse, the uncapped whole-ball test, the closed nonnegative alternative, actual ambient π₁-injection, and the original complete-interior endpoint remain intact. Physical disk area uses post-event metrics; normalized slice metrics are g(t)/t, and the curvature-one convention is g(t)/(4t).

## Remaining scope

The mixed refinement and prime graph geometric supplier remain coarse admissions. Task 5's full good-block/Seifert/relative-cap vocabulary, model-specific E1 suppliers, and local-fibration/cloud/collar splits are incomplete. Finite-order compactness and pullback admissions remain, and the finite-C cusp-error realization proof is not installed. These omissions are recorded in the report; no abstract “good block” alias or conclusion-shaped placeholder has been substituted for them.

## Source and trust records

| Family | Review | Crosswalk |
| --- | --- | --- |
| Flow | [review](flow_review.md) | [JSON](flow_declarations.json) |
| Collapse | [review](collapse_review.md) | [JSON](collapse_review.json) |
| Topology | [review](topology_review.md) | [JSON](topology_declarations.json) |
| Hyperbolic/disk | [review](hyperbolic_review.md) | [JSON](hyperbolic_crosswalk.json) |
| Finite regularity | [review](finite_regularity_review.md) | [JSON](finite_regularity_declarations.json) |

[Source checks](evidence/source_checks_2026_09_29.json) distinguish newly read primary passages, reused records, and Blueprint-only adapters. KL14 Theorem 16.1 is cited only through the Blueprint record. The numerical locator validator checks every file, label, title ID, reading range and source hash; it is not a mathematical proof.

Run `python3 tools/gc/check_skeleton.py --prepare` after source/crosswalk changes, then `python3 tools/gc/check_skeleton.py --full-root --fresh-audit`. The source gate rejects nonregistered admissions, admissions outside a theorem's sole body, comments, prohibited commands, and every option except `autoImplicit false`. The compiled declaration audit checks authored and generated declarations, declaration types, checked-environment membership and transitive axiom closures. [Negative fixtures](evidence/negative_tests.json) demonstrate all requested error paths; `skipKernelTC` is rejected by the static source layer, since the environment-only check cannot detect it. [Interface applications](evidence/interfaces/verification.json) include three positive markers and a complete type-equality check.

The admission-aware gate is distinct from literal silent-build acceptance: admitted leaves emit `declaration uses sorry`, and unchanged foundation modules replay existing style warnings. Those warnings are recorded, not suppressed or relabeled as silence. Proof-only direct leaf runs and selected lint results have separate logs.
