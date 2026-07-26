# B1 join — live handoff (2026-07-11)

> **Superseded for the live stage-map route (2026-07-15).**  Resume from
> `B1_STAGE_MAP_RULING.md`.  The historical checklist below predates the
> canonical global finite-stage map and the current analytic stop point.

Work in `E:\testdifferential-geometry`, branch `short-time-existence`.  Read
`AGENTS.md`, `important_lesson.md`, `lessons.md`, `PROJECT_MAP.md`, and the
same-name notes before editing.  Use `scripts/lake-locked.ps1`; claim Lean files,
prefer focused checks, and do not force-release stale locks.

## Honest status

- Textbook B1 theorem: 0%.
- Concrete `StepB1RawInput` producer: 0%.
- Checked conditional assemblies: `stepB1_of_raw`, `stepB1_of_bounds`.
- Dedicated Step-B1 machinery: about 77%.
- Chapter 4 machinery: about 74%.
- Whole HCG compactness machinery: about 51%.
- Conditional/final compactness endpoints: 0%.

Do not report a checked wrapper or local green module as completion of B1.

## What is now checked

- `GoodCoveringSeq.inner_cover`: eventual `3 * lamInf` cover inside the existing
  `4 * lamInf` hats.
- `StepCAtoms`: intrinsic quadratic atoms, inner-one and hat-support facts,
  eventual `WeightDataOn`, canonical zero slot, and basepoint delta weights.
- `StepCAtomConv`: quadratic readout calculus, live/dead sequence atom limits,
  normalized-weight `C^infty` convergence, finite live-slot origin-metric
  extraction, and dead-slot zero overwrite.
- `StepCAtomJoin.existsLiveJoint`: one strict subsequence carries the live-slot
  origin metrics and the one-sided transition family, with eventual geometry
  and a common finite tail.
- `StepCAtomPackage.existsAtomWeightLim`: genuine dead-slot zero limits, smooth
  atom and normalized base-killed weight families, and Pi-valued `C^infty`
  convergence; exact-one is derived from the intrinsic cover.
- `MapCInfConvOnCompacts.congr_eventually`: tail locality for stabilized slots.
- `StepCCmDomain`: the actual center on an admissible set, the analytic
  `cmExt_contDiffOn` interface, the compact pinned-root gluing theorem, subtype
  center continuity, injectivity-based agreement, and the generic conditional
  `centerReadout_zero` producer.  The latter has not yet been instantiated on
  the finite-hat configuration family.
- `exists_diagInvDom` / `exists_readoutDom`: real finite-order open branch
  domains with off-diagonal smoothness and pointwise inverse/projection facts.
- `exists_diagInvDom_inf` / `exists_readoutDom_inf`: one common all-order open
  branch/readout domain for the existing `diagExpInv`.
- `exists_readoutEBall`: a finite positive branch radius for each fixed
  `(M, g, p)`.  `centerPairs_lt_of`, `centerPairs_lt_le`, and `centerPairs_lt`
  close the local center/point containment ledger, including the cage-facing
  sufficient bound `R + 2 * r < δ` with `R = 4 * lambda` available later.
- `exists_halfSqDist_md`: fixed-target local differentiability of
  `halfSqDist`; `expDiffeoRadius`, `expDiffeo_mem_of_lt`, and
  `diagInv_eq_normal_lt`: pointwise intrinsic/realized branch identification
  below a named radius.  Their finite-hat source/smallness hypotheses are not
  yet instantiated.
- `NormalPhaseEndpoint.exists_normal_diag` now combines the bilateral normal
  flow, quantitative inverse, explicit target-ball radius, and exact
  commutative square with intrinsic `diagExp`.  `normal_inv_eq` proves equality
  with the existing `diagExpInv` under concrete branch-domain identities and
  two `expDiffeoRadius` smallness inequalities.
- `DiagExpDerivative.diagExpInv_diagExp` supplies the source-side IFT germ, so
  compatibility of the two branches on a verified overlap is no longer open.
- The explicit-branch architecture is now checked: `DiagInvBranch`,
  `DiagInvReadout`, `stdBranch`, the branch-parametric center equation and
  smoothness consumers, `normalDiagAtFull`, `IsNormalDiag.toBranch`, and
  `IsNormalDiag.full_transport`.  The latter exposes exact source/target image
  equalities and the inverse formula on the whole quantitative target.
- `exists_phase_scale` and `normalBrAccept` choose global positive coefficients
  `aq`, `aδ`, and `aρ`; for each exhaustion radius they choose `q` and `δ`
  before the sequence index and center, retain the whole `δ` target ball and
  inverse formula, and provide a common branch domain of radius `aρ * mu R`.
  `normalBrScale` is the checked compatibility projection; `normalBrHat` is the
  direct finite-hat scale inequality.
- `NormalDiagBranch.exists_pair_branch` carries one branch over any controlled
  family of point pairs.  `NormalBranchCage.seqCenterD_dist_le`,
  `liveCenters_cage`, and `exists_live_dom` put every stabilized live center in
  one fixed sublevel and one selected relative branch domain on a common tail.
  `exists_cm_branch` is now checked for the whole finite center/point family in
  `B.readDom`.
- `centerReadoutB_zero` consumes that `readDom` membership directly.  It derives
  the fixed-trivialization base condition and branch/normal-coordinate equality
  internally, leaving only the genuine named-radius and first-variation inputs.

## Next tasks, in order

1. Resolve the quantitative intrinsic/realized-exp compatibility design in
   `B1_INTRINSIC_REALIZED_CONSULT.md`.  The current `expDiffeoRadius` contains a
   pointwise qualitative agreement radius with no `NormalRadiusProfile` floor;
   do not hide it behind a new consumer assumption.
2. On the chosen route, produce uniform reverse-chart/half-squared-distance
   differentiability and center-equation control for the concrete finite-hat
   family.  This must discharge both `hreal` and `centerOfMass.eqnRadius`, not
   merely rename them.
3. Finish the physical large-`D`/`radSeq` ledger using `normalBrHat` and the
   explicit coefficient returned by `normalBrScale`.
4. Supply the book-scale Hessian/Neumann input, instantiate
   `existsCmExtension`, upgrade the ambient root with `cmExt_contDiffOn`, and
   compose it with the verified atom/weight/target limits.
5. Use the resulting C-track estimates, local diffeomorphism/injectivity, and
   basepoint delta identity to construct `StepB1RawInput`.

## Current mathematical frontier

Pinned-map extraction, compact gluing, subtype continuity, selected quantitative
branch construction, and finite-family `B.readDom` containment are implemented
and verified.  Do not restart any of those stages.

The current stop is quantitative compatibility, not domain membership.
`expDiffeoRadius` is defined as the minimum of `expRadiusGp` and a
`Classical.choose` radius witnessing `expMapIntrinsic = expMap`.  The H6
`NormalRadiusProfile` controls `expRadiusGp`, but it gives no lower bound for the
chosen agreement radius.  Consequently the selected branch source and the
large-`D` scalar ledger cannot prove `centerReadoutB_zero`'s `hreal`.

Three routes were audited.  A branch-source estimate still needs the missing
agreement lower bound; global equality of the exponentials enters the unfinished
cross-chart maximal-geodesic continuation layer; and a center equation stated
directly for the intrinsic branch needs a new quantitative minimizing/first-
variation theorem because the current `HalfSqDistGrad` route uses the same
qualitative radius.  This is a design/API consult point.  The book-scale
Hessian/Neumann producer remains an independent honest frontier;
`CmHessianBoundInput.toInv` is only a projection from it.

## Forbidden routes

- Do not resurrect the false P-only `stepB1_approxIso` statement.
- Do not require `CenterInput` on the whole configuration vector space.
- Do not require `CenterInput` on an ambient open neighborhood of a sparse or
  delta weight; the nonnegative simplex has boundary there.
- Do not run metric/transition extraction over dead fallback centers.
- Do not require live-slot geometry at every index; stabilization only supplies
  the genuine centres eventually.
- Do not request reverse transitions or cocycles from the fixed-source Step-C
  atom join; those belong to the atlas-transition lane.
- Do not add consumer-side assumptions that merely rename `hsm`, `hinv`, or
  `hzero` as a polished endpoint.
- Do not glue roots with a partition of unity; it does not preserve the root
  equation.  Use the pinned-map injectivity neighborhood.
- Do not replace the intrinsic atoms by the old fixed-psi `bumpNumConv` route.
- Do not infer a uniform branch radius from uniform `metricC`; the radius field
  itself is only pointwise positive.
- Do not add a consumer-side `branchRadius` or fixed-trivialization assumption.
  The relative scale and chart containment are already produced.
- Do not add a uniform lower bound for `expDiffeoRadius` as a new endpoint or
  finite-hat assumption.  Prove the compatibility geometrically or change the
  canonical construction after an explicit architecture decision.

## Acceptance criteria for the next brick

- Preserve the explicit `DiagInvBranch` architecture and the checked
  `normalBrScale` quantifier order; do not return to order-dependent
  neighborhoods or the qualitative `exists_readoutEBall` route.
- Preserve the checked selected branch and `B.readDom` finite-family theorem.
- Choose and justify one route that removes the unquantified
  intrinsic/realized-exp agreement radius from the B1 critical path.
- Then prove the concrete finite-hat configurations lie below the resulting
  center-equation and differentiability scales, so `centerReadoutB_zero`
  discharges the root equation without a renamed consumer assumption.
- Keep the independent Hessian/Neumann producer visible if it is not discharged
  in the same brick, and update the same-name note plus `PROJECT_MAP.md` with
  theorem completion separated from machinery progress.
