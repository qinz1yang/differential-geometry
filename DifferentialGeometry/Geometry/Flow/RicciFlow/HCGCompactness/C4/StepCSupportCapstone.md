# Source-local finite-support capstone

## Purpose

`StepCSupportCapstone.lean` is the upper B/C assembly layer.  It imports the
producer chain and the support-local branch readout without reversing either
dependency.  A source slot owns its normal chart and limit-weight family; an
actual interacting target remains an old-`L` `InterSlot`.  The file never
defines a glued weight, an overlap-compatibility theorem, or a pointwise chart
selector.

## Checked result

- `HasSuppCmFin` records the finite source-patch cover, patch-to-hat
  containment, chart-local `WeightDataOn`, positive active radii, a common
  epsilon-dependent radius tail, and one common pair-index tail for the
  selected-branch root, invertible derivative, and strict local solution.
- `HasSourceCmFin` is the global-ball existential-source form.
- `HasSuppCmFin.toSource` derives the latter with the same threshold by using
  the finite cover; the source chart remains an existential witness.
- `MetricCompactBase.exists_supp_cm_fin` first selects the common minimizing
  scale, then chooses the divisor once, instantiates packing, obtains one
  stable net and one master subsequence, and finally takes finite maxima over
  target and source slots.
- `MetricCompactBase.exists_cm_on_source` is the global-ball corollary.

The source-local capstone and its global corollary are focused-green and have
no local warnings.  The preceding fused producer was strengthened only by the
derived patch-to-hat containment; no new input was added.

## Honest frontier and accounting

The final implication still consumes `StrictDistInput`.  The branch-native
Hessian/Neumann and strict-IFT output is now retained all the way through the
finite cover; producing `StrictDistInput` from a uniform positive Hessian lower
bound and geodesic strict convexity remains independent.  No endpoint radius
hypothesis was introduced.

- This conditional source-local/global capstone theorem: **100%**.
- Dedicated source-cover, sparse-point, and pair-to-capstone machinery:
  **100%** for the approved architecture.
- Concrete `StepB1RawInput` producer: **0%**; textbook B1 theorem: **0%**.
- Selected-branch Hessian/Neumann support route: **100%**.
- `StrictDistInput` producer: theorem-level **0%**.
- Dedicated Step-B/B1 machinery: about **90%**.
- Chapter 4 machinery: about **83%**.
- Whole HCG machinery: about **55%**.
- Conditional/unconditional compactness endpoints and `ham3_cgh_limit`:
  **0%** proved.

The smallest remaining analytic producer is the support-uniform
`lbl413 → StrictDistInput` comparison theorem at the already selected physical
scale.  This is a substantial analytic/API frontier, not a local coercion or
tactic repair.

## 2026-07-14 unconditional intrinsic-join capstone

This section supersedes the honest-frontier accounting above.  The canonical
`HasSuppCmFin` and `HasSourceCmFin` predicates now use the intrinsic
`minJoin`; they no longer expose an arbitrary join or a downstream
`StrictDistInput` continuation.  `MetricCompactBase.exists_supp_cm_fin` calls
the direct `exists_hat_cm_min` producer, and the finite source maximum and
global-ball existential-source corollary keep the approved local-patch
architecture unchanged.

Focused verification passed without local warnings or `sorry`.  The approved
source-cover, sparse-point, active-radius, Hessian/strict-convexity, and
pair-to-capstone machinery is **100%**.  The concrete `StepB1RawInput`
producer and textbook B1 theorem remain theorem-level **0%**, as do the
conditional and unconditional compactness endpoints.  Dedicated Step-B/B1
machinery is about **94%**, Chapter 4 machinery about **86%**, and whole-HCG
machinery about **57%**.

## 2026-07-14 convergence-data retention

`MetricCompactBase.exists_supp_cm_fin` now retains `Jinf`, `Jbarinf`, and the
full `HasSuppConvData` package on exactly the same master subsequence as its
finite source-patch strict center solutions.  The global-ball corollary keeps
its public conclusion unchanged and simply forgets this internal evidence.

Focused verification passed without local warnings.  The capstone now exposes
the convergence and cover data required for the next compact-patch stage, but
still does not produce a single cross-manifold map, an all-pairs sequence tail,
or arbitrary-order metric-error bounds.  Accordingly `StepB1RawInput`, the
textbook B1 theorem, and every compactness endpoint remain theorem-level
**0%**; the running machinery estimates remain about **94%** for dedicated
Step-B/B1 work, **86%** for Chapter 4, and **57%** for whole HCG.

The producer now also supplies `HasCompactCover` on the same frozen-stage
tail, and `exists_supp_cm_fin` retains it unchanged beside the strict center
capstone.  Focused verification passed.  This closes the compact-domain
preparation only; it does not change any theorem-level completion percentage.

## 2026-07-15 nested-core propagation

`MetricCompactBase.exists_supp_cm_fin` now returns the fixed nested coordinate
cores `C0` and `C1` inside its retained `HasSuppConvData` package.  Thus the
strict-inner-core source cover survives on exactly the same master subsequence
as the source-local center solutions; `exists_cm_on_source` intentionally
forgets the extra data and preserves its public conclusion.

Focused verification passed.  This closes the remaining routine data-erasure
seam before the moving-stage argument.  It does not provide the support-smooth
target tuple, a common-domain moving implicit solver, or an all-pairs chart
tail.  `StepB1RawInput`, textbook B1, and all compactness endpoints remain 0%;
the rounded machinery estimates remain 94% / 86% / 57%.

## 2026-07-16 radius-aligned capstone data

`exists_supp_cm_fin` now retains `qAcc` and both phase/inverse-error budgets in
addition to `qWide`, and proves the derived alignment
`C1 alpha ⊆ ball 0 (q alpha / 2)`. Focused verification passed. This closes a
data-loss seam only; the all-pairs chart tail and `StepB1RawInput` remain 0%.

## 2026-07-18 canonical framed-coordinate migration

Every selected source-local patch in this capstone now uses `framedChartAt`.
The four direct two-stage point families use `framedTransition` at both moving
stages, with the corresponding bundled manifold instances installed locally.
The already framed `normalCoordMetric` interface is unchanged.  No chart
selector, cross-chart weight compatibility, radius assumption, or legacy raw
normal-coordinate wrapper was added.

Focused verification passed after the separately owned
`NormalPhaseSmallness` object was refreshed, and the source diff contains no
remaining `normalChartAt` or `normalTransition` occurrence.  This file's
framed migration is therefore 100% revalidated.  It does not by itself
revalidate the full downstream B/C chain: the previously proved raw B1
producer remains subject to that chain-wide framed refresh, while the
separately named textbook B1 theorem and unconditional compactness endpoints
remain theorem-level 0%.  The whole-HCG machinery estimate remains about 60%.

## 2026-07-18 exact refresh frontier

The authorized exact refresh was attempted immediately after
`StepCStageCenter` became exact-green. It did not reach this file's source:
the build stopped in `Geometry/Comparison/Volume/RadialGronwall.lean` because
the installed `JacobiVariation.olean` did not yet export
`DifferentialGeometry.Geometry.Riemannian.exists_jacobi_diff`.

The live `JacobiVariation.lean` source does contain that public theorem, and
the source was newer than its installed object. This is therefore a stale
upstream artifact in the separately owned H6 Jacobi lane, not a local proof or
mathematical regression in `StepCSupportCapstone`. Exact validation of this
capstone remains pending the coordinated Jacobi/Radial refresh; no endpoint
radius assumption or compatibility wrapper was introduced.

The coordinated Jacobi and Radial refresh then succeeded. The next exact
attempt again stopped before reaching this file, now in the owning module
`StepCCmDomain.lean`. That module still mixed raw fixed-base
`normalChartAt` center configurations with the canonical framed
`chartCmEqnB` and selected diagonal branch. The build reported deterministic
normalization timeouts at those mismatched interfaces and a concrete failed
rewrite at the final `centerReadoutB_min` proof. The smallest repair is the
canonical fixed-base framed migration in `StepCCmDomain`; moving-base inverse
tangent readouts remain raw. `StepCSupportCapstone` exact validation is still
pending, while its own focused-green framed source status is unchanged.

## 2026-07-18 exact framed-chain closure

The upstream blockers above are now resolved.  The fixed-base configuration
API in `StepCCmDomain`, the minimizing Cage and Hat readouts, and the
normal-metric live diagonal were refreshed on their canonical framed and
`expRadiusGp` semantics.  `StepCSupportCapstone` then passed both its focused
check and the exact module refresh; the latter rebuilt the full selected
transition/atom/source-cover dependency chain through this capstone.

This establishes the support-local capstone as checked on the live framed
tree.  It does not prove the independent quantitative producer for
`NormalRadiusProfile.le_exp_radius`, nor does it finish the downstream
all-pairs stage-map and metric-carrier validation.  The source proof body of
`MetricCompactBase.exists_b1_raw` is complete but still awaits those remaining
checks.  The separately named textbook B1 theorem and unconditional endpoints
remain theorem-level 0%; rounded machinery estimates remain B1 95%, C4 87%,
whole HCG 60%.
