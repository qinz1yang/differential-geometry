# NormalPhaseEndpoint

## Role

This is the merge layer between the quantitative normal-coordinate phase flow
and the project's intrinsic moving exponential.  It consumes the checked
geodesic naturality and interval-uniqueness producers; it does not define a
second intrinsic inverse.

## Verified state

- `normal_enorm` supplies the Riemannian tangent-enorm formula under the
  endpoint layer's explicit suppression of the model tangent norm instances.
- `normalTangent` sends `(u,v)` to
  `⟨exp_x u, d(exp_x)_u v⟩`; `normalPair` sends a pair of normal coordinates to
  the corresponding ambient pair.
- `normal_launch_mfd` identifies the launch derivative of a pushed phase curve
  with `d(exp_x)_u v`.
- `normal_end_eq_intr` transports the bilateral phase trajectory through the
  quarter-ball normal diffeomorphism and identifies its time-one value with
  `expMapIntrinsic`.
- `normal_end_eq_diag` is the exact commutative-square statement with
  `diagExp`.
- `exists_normal_diag` packages one positive bilateral flow ball, the
  quantitative `OpenPartialHomeomorph`, its explicit positive target-ball
  radius, forward and inverse `C^infinity` regularity, and the commutative
  square with `diagExp`.
- `IsNormalDiag` is the minimal consumer specification for that exact branch:
  explicit source ball, `e 0 = 0`, fixed-origin target ball, smooth
  forward/inverse maps, and the intrinsic endpoint square.
- `NormalRadiusProfile.exists_uniform_diag` has the required quantifier order.
  For each fixed basepoint-distance sublevel it chooses one `q` and one explicit
  positive `delta` before quantifying over all stages and admissible centers.
  It consumes the existing profile and adds no branch-radius assumption.
- `NormalRadiusProfile.exists_flow_at` exposes the same checked construction at
  a prescribed positive `q`, provided the phase-radius, acceleration, and
  inverse-error budgets are supplied.  `exists_uniform_flow` keeps its original
  public statement and is now the compatibility wrapper that selects such a
  `q` with `exists_smooth_q` before calling `exists_flow_at`.
- The prescribed-radius path is consumed downstream by
  `NormalRadiusProfile.exists_diagPair_at`, and the live source now contains
  `MetricCompactnessInputs.exists_slot_diag`, which applies it at each live
  slot with stage radius `q alpha` and limit radius `q alpha / 2` on one shared
  metric-limit subsequence.
- `normal_inv_eq` proves that this model branch agrees with the existing
  `diagExpInv` whenever the existing branch identities hold and both tangent
  vectors satisfy the concrete `expDiffeoRadius` smallness conditions.
- `DiagExpDerivative.diagExpInv_diagExp` supplies the complementary
  source-side germ identity, so the two branches are now formally compatible on
  every verified overlap.
- `PhaseFlow.inv_smooth_of_approx` closes the generic last step from forward
  `C^infinity` regularity to inverse regularity for the exact supplied
  quantitative partial homeomorphism.  It does not choose another branch.

Focused verification passed without local warnings, `sorry`, or `admit`.
The public declarations' axiom audit contains only `propext`,
`Classical.choice`, and `Quot.sound`.

## Review disposition

The external review recommended geodesic-spray naturality.  The live project
already had the equivalent lower-level producer
`CovariantDerivativeAlong.covAlong_natCrossAt`: it handles an arbitrary
along-curve field by a local extension plus a residual vanishing at the point.
`Geodesic.geoEq_mapCrossAt` and `geodesicOn_mapLocal` then provide the required
pointwise/open-set naturality.  This closes the review's arbitrary-velocity
objection without introducing a parallel spray API.

An attempted move of `normal_enorm` into `PointedEmetric.lean` was rejected and
fully reverted: importing the norm-reconciliation layer there reintroduced the
tangent norm instance diamond that `PointedEmetric` is designed to avoid.

## Frontier

The normal endpoint producer is closed: endpoint naturality, forward
smoothness, inverse smoothness, zero normalization, and a positive target
radius are checked on the same prescribed branch.  The prescribed radius now
also reaches a slotwise matched stage/limit branch producer.  The next
integration target is higher-level assembly: feed the radii and budgets chosen
by the live minimizing-branch scale into `exists_slot_diag`, then close the
same-branch seam before the support/readout capstone.  At present
`exists_slot_min` retains one `HasNormalBrFull` witness while
`exists_slot_diag` independently chooses the stage branch used in
`HasDiagPairConv`; equality cannot be inferred merely from their common `q`.
The next producer must reuse one witness or prove and transport an on-domain
branch identification.  Compatibility with `diagExpInv` remains an overlap
theorem, not a global equality of totalized functions.

The strict-convexity Hessian/Neumann continuation remains an independent
analytic frontier.

## Project position

- `StepB1RawInput` producer: unstated/unproved, 0%.
- Textbook B1 theorem: unstated/unproved, 0%.
- Quantitative normal-coordinate `diagExp` branch theorem
  (`exists_normal_diag`): proved, 100%.
- Uniform fixed-sublevel quantitative branch producer
  (`exists_uniform_diag`): proved, 100%.
- Uniform theorem identifying the whole branch with totalized `diagExpInv`:
  intentionally not pursued; global totalized equality is not the selected API.
- Smooth quantitative inverse implication (`inv_smooth_of_approx`): proved, 100%.
- Forward smooth endpoint theorem on the explicit source ball:
  proved, 100%.
- Dedicated normal-coordinate quantitative branch machinery: about 98%.
- Step B/B1 infrastructure: about 75%.
- Chapter 4 infrastructure: about 73%.
- Whole HCG compactness infrastructure: about 50%.

## 2026-07-16 canonical fence retention

`NormalDiagFence` now has its canonical home in this lower endpoint module,
next to the first construction that proves the whole-ball endpoint
containments.  `NormalRadiusProfile.exists_flow_at` retains the fence for the
same prescribed `q` and the same selected branch `e`; no second existential
branch or radius was introduced.  `exists_uniform_flow` preserves its public
compatibility statement and intentionally forgets the extra fence field.

Focused verification passed, and the endpoint refresh plus downstream checks
confirmed the moved declaration is visible to consumers.  The former
same-branch integration seam is now closed downstream by
`IsNormalDiag.eqOnSource` and `HasDiagPairConv.congr_stage`.  This remains
infrastructure: `StepB1RawInput` and textbook B1 are theorem-level **0%**;
dedicated Step-B/B1 machinery is about **95%**, Chapter 4 about **87%**, and
whole-HCG compactness machinery about **57%**.
