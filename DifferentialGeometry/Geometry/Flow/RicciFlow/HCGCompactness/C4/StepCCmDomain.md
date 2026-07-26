# StepCCmDomain

## 2026-07-18 canonical framed-coordinate migration

- All fixed-base configuration coordinates in `centerCfgOn`, `chartCenterOn`,
  both center readout producers, the ambient extension interfaces, and
  `centerReadoutB_min` now use `framedChartAt`.  The raw `normalChartAt` calls
  whose base is the selected moving center are intentionally retained: they
  are the true tangent readout used by the inverse-exponential equation.
- `chartCenterOn_cont` now uses the framed partial diffeomorphism's exported
  `contMDiffOn_toFun`, and the minimizing readout's base/decode seam uses the
  framed chart source together with `framedExp_target`.
- The model-space instance block now matches the canonical no-diamond Step-C
  API: `InnerProductSpace`, `FiniteDimensional`, and `CompleteSpace` supply the
  required normed and finite-module structure without parallel explicit
  instances.  This mirrors the deterministic-timeout repair in
  `StepB1Producers`; no heartbeat was raised.
- Focused verification is green with zero diagnostics, the exact module refresh
  is green, and the scoped diff is clean.  The module's canonical framed API is
  now available to downstream consumers.  Current rounded infrastructure
  accounting remains about
  95% for B1, 87% for C4, and 60% for the whole HCG compactness project; the
  `MetricCompactBase.exists_b1_raw` source proof body is complete but awaits
  this framed-chain validation.  The separately named textbook B1 theorem and
  unconditional endpoints remain theorem-level 0%.

## 2026-07-13 minimizing-branch center readout

`centerReadoutB_min` is implemented, focused-green, and sorry-free. For a
finite configuration in the explicit half-cage of the selected quantitative
branch it derives, rather than assumes:

- differentiability of every summand from `IsNormalDiag.halfSq_inf`;
- the branch-native gradient identities from `IsNormalDiag.grad_half_inv`;
- branch-domain and fixed-trivialization base membership;
- the weighted inverse-tangent equation from `centerOfMass.invB_eqn`.

The fixed-trivialization linear equivalence then transports the tangent sum to
`chartCmEqnB = 0`. This route does not use the moving-center normal-chart
inverse, `centerOfMass.eqnRadius`, `expDiffeoRadius`, an external `hread`, or a
new endpoint radius assumption. Gate 5 is therefore theorem-complete (100%).

This closes the selected-branch root equation, not the whole B1 producer.
Gate 6 uniform scale is now completed in `NormalBranchScale.lean` and consumed
on the live cage in `NormalBranchCage.lean`; the generic large-`D`/packing order
is checked in `MetricCompactnessInputs.lean`. `StepB1RawInput`, textbook B1,
and the conditional compactness endpoint remain 0%. The post-packing
finite-cage/Item-3, Hessian/Neumann, and convergence frontiers remain.
Consequently the rounded machinery estimates are about 79% for Step-B/B1, 75%
for Chapter 4, and 52% for the whole HCG compactness project.

## 2026-07-11 selected-branch migration

- `centerReadoutB_zero` proves the actual center equation for an explicit
  `DiagInvBranch`.  It now consumes finite-pair membership in `B.readDom` and
  smallness of the branch inverse below `expDiffeoRadius`; internally it derives
  fixed-trivialization base membership from a positive weight and derives
  `B.inv = normalChartAt` from `DiagInvBranch.inv_eq_normal_lt`.  Callers no
  longer supply either conclusion as a separate hypothesis.  The legacy
  `centerReadout_zero` remains unchanged because its hypotheses do not include
  membership in the standard branch domain.
- `existsCmExtensionB` specializes compact pinned-root gluing to
  `chartCmEqnB`; `cmExtB_contDiffOn` globalizes the branch-parametric implicit
  solution on an open parameter domain.  The old `diagExpInv` entrypoints remain
  compatibility APIs.
- Focused verification passed without warnings or local `sorry`s.  The abstract
  branch-parametric domain/extension consumer layer is complete.  The concrete
  quantitative HCG branch and finite-configuration `readDom` containment are
  now produced in `NormalDiagBranch` / `NormalBranchCage`.  The remaining
  producer work is the quantitative intrinsic/realized-exp compatibility,
  reverse-chart/half-squared-distance radius control, and Hessian/Neumann bound.
- This migration does not complete `StepB1RawInput` or textbook B1; both remain
  0%.  The rounded machinery estimates below are unchanged.

## 2026-07-10 current verified state

This section supersedes the 2026-07-09 in-progress paragraph below.

- `existsRootExtension` glues local pinned inverses along a compact root graph.
  It obtains one common open injectivity neighborhood with
  `Set.InjOn.exists_isOpen_superset`, then defines the inverse root on an
  ambient open parameter set. Agreement with the original root is proved by
  pinned-map injectivity, not assumed from two root equations.
- `existsCmExtension` specializes the construction to `chartCmEqn'`.
  `chartCenterOn_cont` supplies the subtype continuity adapter for the selected
  center and removes the outside-domain filler with `centerCfgOn_eq`.
- `centerReadout_zero` is a generic conditional producer for the selected
  center's `chartCmEqn' = 0` equation.  It consumes the named center radius,
  `halfSqDist` differentiability, moving normal-source membership, fixed-chart
  membership, branch projection/intrinsic-exp identities, and smallness below
  `expDiffeoRadius`; it derives genuine inverse-branch identification through
  `diagInv_eq_normal_lt`.  It therefore does not rename `hzero`, but its
  finite-hat instantiation is not yet complete.
- Focused verification and targeted builds passed. Branch gluing/agreement is
  no longer a frontier.
- The common off-diagonal branch and finite-family `readDom` containment are no
  longer frontiers.  The remaining genuine inputs are containment in
  `eqnRadius`, reverse-chart/named-radius smallness needed to instantiate the
  checked differentiability and branch-identification producers, and the
  book-scale Hessian/Neumann producer.

## 2026-07-11 quantitative compatibility stop

- The selected branch does not by itself discharge the remaining
  `expDiffeoRadius` inequality.  That radius is the minimum of
  `expRadiusGp` and a pointwise `Classical.choose` radius for
  `expMapIntrinsic = expMap`; `NormalRadiusProfile` controls the former but has
  no lower bound for the latter.
- Replacing `hreal` by a direct branch-source estimate therefore cannot work
  with the present API.  Globally identifying the two exponentials enters the
  unfinished cross-chart maximal-geodesic continuation layer.  Reproving the
  center equation directly for the selected intrinsic branch also requires a
  new quantitative minimizing/first-variation theorem: the current
  `HalfSqDistGrad` route uses the same qualitative agreement radius.
- This is a three-route design/API stop, not a coercion failure.  Do not add a
  consumer-side uniform agreement-radius assumption.  The next decision is
  whether to prove a quantitative intrinsic/realized-exp compatibility theorem
  from the H6 phase tube, make the intrinsic branch canonical for normal
  coordinates, or formulate and prove the first-variation/root equation
  directly for the selected branch.

## 2026-07-09 restricted configuration interface

- The old `chartCm_contDiffOn` wrapper requires `CenterInput` on the entire
  configuration space.  That is not instantiable because the space contains
  negative and all-zero weight vectors.
- `centerCfgOn` uses `centerAverageOn` on an admissible set and the chart base
  as its harmless outside-domain filler; `centerCfgOn_eq` recovers the actual
  center of mass on that set.
- An ambient-open subset containing a sparse or delta weight cannot itself
  carry `CenterInput`: perturbing a zero weight negatively contradicts
  `CenterInput.mu_nonneg`.  Therefore an open-domain theorem for the literal
  selected center would still be unusable at the finite-hat boundary.
- `cmExt_contDiffOn` instead globalizes the local implicit readout solution for
  an ambient `E`-valued extension.  It derives the neighborhood solution
  equation from the pointwise equation and openness, and derives pointwise
  `Tendsto` from `ContinuousOn`.  It deliberately makes no signed-weight center
  claim and avoids a chart/symm round trip.
- The real next producer must construct an ambient open extension and prove
  agreement with `centerCfgOn` along the admissible finite-hat configuration
  image.  The gluing route is now pinned: apply
  `Set.InjOn.exists_isOpen_superset` to the pinned map
  `(z, params) ↦ (chartCmEqn' z params, params)` on the compact graph of the
  actual admissible center.  Local IFT partial homeomorphs give local
  injectivity; the resulting open graph neighborhood gives one common
  uniqueness region and a continuous inverse root.  This leaves a routine
  extraction of the pinned local `OpenPartialHomeomorph` plus a small subtype
  center-continuity adapter, rather than a new branch-gluing theorem from
  scratch.  Its genuine mathematical inputs remain
  off-diagonal `C^infty` control of the moving inverse-exponential readout and
  Hessian/Neumann invertibility plus the readout equation.
- Verification is pending because the missing upstream
  `DifferentialGeometry.Tensor.RSTensor.NablaOnTensors.Regularity.Derivation`
  object currently exposes a committed-source elaboration/heartbeat wall when
  rebuilt.  Its file owner is repairing that shared dependency separately.

## Progress accounting

- Admissible-center, ambient-extension, root-equation, and agreement interface:
  implemented and verified.
- `StepB1RawInput` producer theorem: 0%.
- Textbook B1 theorem: 0%.
- Dedicated Step-B1 machinery: about 77%.
- Chapter 4 machinery: about 74%.
- Whole HCG compactness machinery: about 51%.
- Conditional and final compactness endpoints: 0%.

## 2026-07-10 — lower-level root-equation inputs

- `centerReadout_zero` no longer consumes the already-packaged equality
  `diagExpInv = moving normalChartAt`.  It now takes the branch projection,
  intrinsic exponential identity, and smallness below `expDiffeoRadius`, then
  derives that equality through `diagInv_eq_normal_lt`.
- Focused verification and the targeted module build passed.
- This is a completed generic consumer simplification, not the finite-hat root
  theorem.  Concrete production of the three hypotheses on the common
  configuration domain remains open; the finite-hat instantiation is still
  0% complete.  The running machinery percentages above therefore remain
  unchanged.
