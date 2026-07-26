# GPT Pro consultation: quantitative intrinsic/realized exponential compatibility

Work against the repository's **`short-time-existence` branch**.  The checked
local state described below is newer than any public index, so treat the listed
declarations as the source of truth if you cannot mount the Windows worktree at
`E:\testdifferential-geometry`.

## Goal

Recommend the smallest mathematically honest producer theorem that removes a
pointwise qualitative exponential-agreement radius from the HCG Step-B1
critical path.  We need a sequence-uniform finite-hat center equation on the
already constructed quantitative selected branch.  Do not solve this by adding
a new consumer or endpoint assumption equivalent to a uniform agreement radius.

## Checked state

The following is implemented and focused-checked:

1. `NormalPhase*` constructs a quantitative normal-coordinate phase flow and a
   time-one endpoint approximating the flat unipotent map on one explicit ball.
2. `NormalDiagAt.normalDiagAt` turns this into one quantitative model partial
   homeomorphism with smooth forward and inverse maps and an explicit target
   ball.
3. `NormalDiagBranch.IsNormalDiag.toBranch` transports that same branch to an
   intrinsic `DiagInvBranch`; `NormalBranchScale.normalBrScale` chooses global
   positive relative coefficients before the stage and center.
4. `NormalCoordinates.expMapDiffeo` now chooses from
   `exists_exp_pd_chart`, and `exp_target_sub_chart` exposes that its target is
   contained in the base chart.
5. `HasNormalBranchDom.exists_pair_readout` and
   `NormalBranchCage.exists_cm_branch` place the complete finite center/point
   family in one selected `B.readDom` on the common tail.
6. `DiagInvBranch.inv_eq_normal_lt` proves
   `B.inv (y,q) = <y, normalChartAt g y q>` from `(y,q) in B.dom` plus
   ```lean
   sqrt (g.inner y (B.inv (y,q)).snd (B.inv (y,q)).snd)
     < expDiffeoRadius g hEnorm y.
   ```
7. `StepCCmDomain.centerReadoutB_zero` now directly consumes `B.readDom` and
   the displayed smallness.  It derives fixed-trivialization base membership
   and the branch/normal-coordinate equality internally, then invokes the
   checked center first-variation equation.

`StepB1RawInput` and the textbook B1 theorem are still 0% proved.  The work
above is dedicated machinery only.

## Exact obstruction

The realized exponential is

```lean
def expMap g p v := maximalGeodesic g p v 1
```

while the selected quantitative phase branch realizes `expMapIntrinsic`.
The current bridge is only local and qualitative:

```lean
exists_expMapIntrinsic_eq_expMap_radius :
  exists rho > 0, forall v, sqrt (g_p v v) < rho ->
    expMapIntrinsic g hEnorm p v = expMap g p v
```

and

```lean
def expDiffeoRadius g hEnorm p :=
  min (Classical.choose (exists_expMapIntrinsic_eq_expMap_radius ...))
      (expRadiusGp g p)
```

`NormalRadiusProfile` gives a sequence-relative H6 lower floor for the normal
metric-control radius and `expMapC2Radius`/`expRadiusGp`.  It gives no lower
bound for the `Classical.choose` agreement radius.  Therefore neither the
selected branch source nor a large-`D` scalar inequality can prove the
smallness required by `inv_eq_normal_lt` uniformly over stages.

The same defect reappears in the center first-variation path:
`HalfSqDistGrad.exists_expMapIntrinsic_normalChart`,
`exists_central_geodesic`, `exists_halfSqDist_md`, and the chosen
`centerOfMass.eqnRadius` ultimately use the qualitative
intrinsic/realized-exp agreement radius.  Thus merely bypassing
`DiagInvBranch.inv_eq_normal_lt` does not yet give a uniform root equation.

## Three routes already audited

1. **Bound the selected branch inverse from its model source.**  The phase ball
   controls the model initial data and should control the tangent norm, but the
   final comparison is still against the unbounded qualitative component of
   `expDiffeoRadius`.  This route cannot close with the current statement.
2. **Prove global `expMapIntrinsic = expMap`.**  Mathematically plausible on a
   complete Riemannian manifold, but the current `expMap` is built from a
   chart-fixed maximal geodesic with a junk value outside its maximal interval.
   The cross-chart endpoint-continuation/chained-flow layer is a substantially
   larger unfinished project and contains unrelated `sorry` frontiers.
3. **State the center equation directly using `B.inv`.**  This avoids literal
   `normalChartAt`, but the present minimizing-geodesic and first-variation
   proofs still use the same qualitative agreement radius.  Closing this route
   requires a new quantitative local minimizing/first-variation theorem for the
   selected intrinsic phase branch.

These are architecture-level alternatives, not three tactic failures.

## Questions

1. Which route is smallest and mathematically faithful under the current H6
   data?
   - a quantitative theorem identifying `expMapIntrinsic` and `expMap` on the
     existing H6 phase tube;
   - making the selected intrinsic exponential branch the canonical normal
     coordinate API used by Step C;
   - proving the half-squared-distance gradient and center equation directly in
     terms of the selected intrinsic branch;
   - or a fourth route?
2. State the **lowest reusable theorem** that should be added first, with a Lean
   signature close enough to implement.  Specify its natural file/layer.
3. Are `NormalCoordMetricBoundInput` (all metric derivatives),
   `NormalRadiusProfile`, phase-orbit fencing, completeness, and the existing
   selected branch sufficient?  If not, identify the smallest genuinely
   missing geometric theorem, not a repackaged desired conclusion.
4. Give a proof dependency chain and identify which current qualitative
   theorems should be replaced or bypassed.
5. Explain how the chosen result yields both:
   - the branch equality needed by `centerReadoutB_zero`; and
   - a uniform finite-hat half-squared-distance differentiability/gradient
     radius, so `centerOfMass.eqnRadius` is no longer an independent arbitrary
     choice.
6. Does the route require changing `MetricCompactnessInputs.D` to record an
   explicit large-`D` inequality, or can that choice be produced later from the
   existing `normalBrScale` coefficients without strengthening the endpoint
   input bundle?

## Constraints

- Preserve the checked quantitative selected branch and `B.readDom` work.
- Do not return to the qualitative `exists_readoutEBall` architecture.
- Do not add a uniform `expDiffeoRadius` lower bound as a consumer-side or
  endpoint hypothesis.
- Do not introduce a second polished exponential/normal-chart hierarchy unless
  you explicitly justify migration of the canonical API.
- Keep `Function.invFun` behavior outside ranges irrelevant.
- Keep the independent Hessian/Neumann producer visible; do not claim branch
  existence alone proves Hessian coercivity.
- Prefer one reusable geometric frontier over several wrapper assumptions.

## Requested answer format

1. Verdict and chosen route.
2. Exact first theorem statement.
3. Proof skeleton with existing declarations to reuse.
4. Necessary follow-up theorems in order.
5. Rejected routes and why.
6. Any required change to the endpoint/input architecture.
