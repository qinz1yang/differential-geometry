# StepCAtomPackage

## Purpose

`StepCAtomPackage.lean` is the concrete finite-family consumer of
`existsLiveJointH6`.  It keeps the honest eventual geometry, discards one common
finite prefix, assigns genuine zero limits to dead slots, and packages the
actual chart-pulled atoms and normalized base-killed weights as Pi-valued
`C^infty`-convergent families.

## Current state

- `existsAtomWeightH6` is implemented and verified against the live
  `StepCAtomJoin`, `stepCAtom_conv`, `seqAtoms_conv`, and `cutWeights_conv`
  interfaces.
- The exact-one input is not assumed abstractly: it is derived from the
  beta-chart image containment in `hatSourceBall` and `innerBall_cover`.
- The target theorem remains infrastructure for the B1/Step-C assembly; the
  final compactness endpoint is not proved by this package.

## Progress estimate

- `existsAtomWeightH6` theorem: 100%; focused verification passed.
- Dedicated atom/weight assembly machinery: 100% for the fixed-source package.
- Step-B/B1 dedicated machinery: about 84%.
- Chapter 4 machinery: about 80%.
- Whole HCG compactness machinery: about 53%; endpoint theorem completion: 0%.

## 2026-07-13 scale tail joins the existing refinement

`existsAtomWeightLim` now consumes `Item3GpScaleTail`. That tail is pulled
back along the already selected `psi0` and included in the same finite common
tail as the chart-domain, beta-image, and inner-cover facts. The existing
single shift `tau k = k + N` therefore yields `Item3GpScaleAt` at every index
of `Lpsi`; no second subsequence or all-index scale assumption is introduced.

Focused verification and the narrow refresh passed. The fixed-source
atom/weight package remains 100% as machinery. `StepB1RawInput` production and
textbook B1 remain 0%; Step-B/B1 machinery is about 80%, Chapter 4 machinery
about 76%, whole-HCG machinery about 53%, and compactness endpoints remain 0%.

## 2026-07-13 H6 package entrypoint

The long atom/weight assembly now lives in the private
`existsAtomWeightCore`, which consumes an already-extracted live joint and a
pure exponential-source containment. After the finite diagonal migrated, a
zero-consumer audit allowed the old S6 compatibility theorem
`existsAtomWeightLim` to be removed. `existsAtomWeightH6` is now the canonical
public path and feeds the checked H6 live joint into the same core without
`ExpInverseDerivBoundInput`. Focused verification after the cleanup passed.

Focused verification passed. Honest status: the fixed-source H6 consumer chain
through atom and normalized-weight limits, including the finite source-slot
diagonal, is canonical. Endpoint S6-field removal and `StepB1RawInput` remain
separate and at 0% theorem completion.

The endpoint S6 field has since been removed.  The canonical fixed-source H6
package and finite diagonal remain checked; the next issue is the package's
all-live-target overlap quantifier.  Stable noninteracting targets now have a
proved zero-limit route in `StepCAtomConv`, and interacting targets are indexed
by `InterSlot`, but combining those branches into the support-local capstone is
still pending.  This does not change endpoint theorem completion (0%).

## 2026-07-13 inner-cover seam

Added `existsAtomWeightH6_of_innerCover`. The private core now consumes the
actual premise used by atom normalization: the source chart maps into the union
of strict inner balls. The existing `existsAtomWeightH6` statement is preserved
as a compatibility corollary using `innerBall_cover`. Focused verification
passed. The explicitly named targeted refresh exceeded the verification time
window without reporting a Lean error; downstream focused verification did not
depend on that refresh.

This seam adds no input field or radius assumption. It also does not solve the
separate all-live-target transition quantifier; the honest sparse producer must
still combine `InterSlot` transitions with the stable-disjoint zero branch.

## 2026-07-13 reusable atom-to-weight package

The normalization half of the private core is now the public lower-layer theorem
`atomWeight_of_atoms`. It consumes only the per-slot atom convergence and
smoothness facts, the dead-slot zero limit, the existing item-3 scale fact at
each stage, and direct chart-image containment in the strict inner-ball union.
It returns the same Pi-valued atom and normalized-weight limit package used by
the H6 consumers. The private core now performs subsequence and atom extraction
and calls this theorem once; the normalization proof is no longer duplicated.

`HasAtomWeightLim.of_atoms` cannot live in this module because
`HasAtomWeightLim` is defined in the downstream `StepCAtomDiagonal` layer. That
layer can wrap `atomWeight_of_atoms` directly when it has fixed `L`, `beta`, and
`aInf`; no transition or all-live-target assumption is part of the reusable
theorem. Focused verification passed. This API refactor changes no endpoint
percentage: the final compactness theorem remains unstated/unproved (0%), while
whole-project machinery remains about 53%.
