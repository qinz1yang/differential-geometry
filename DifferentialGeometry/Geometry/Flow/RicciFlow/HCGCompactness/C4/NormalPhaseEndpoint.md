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

The normal quantitative producer is now closed: endpoint naturality, forward
smoothness, inverse smoothness, zero normalization, and a uniform positive
target radius are all checked on the same branch.  The next target is a
consumer refactor: parameterize the HCG readout by the selected inverse branch
instead of hard-coding the privately chosen qualitative `diagExpInv` germ.
Compatibility with `diagExpInv` remains an overlap theorem, not a global
equality of totalized functions.

After that refactor, the next geometric obligations are concrete finite-hat
containment and the independent half-squared-distance Hessian/Neumann bound.

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
