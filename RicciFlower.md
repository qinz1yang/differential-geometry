# RicciFlower root notes

## 2026-05-16 export scalar finite-time endpoint

- Worked: exported `RicciFlower.RicciFlow.Evolution.ScalarFiniteTime` after the
  new Corollary 7.4 module checked independently.
- Verification passed for the focused new file.  The targeted module build did
  not finish because `Tensor0SRiemannian.lean` currently has an unsolved goal
  at line 1408, so the root import check was not run.
- Remaining risk: the new endpoint theorem is conditional on the 7.3 regularity
  and scalar-continuity producers, not on maximal-time or extension theory.

## 2026-05-15 export Perelman statement interfaces

- Worked: added `RicciFlower.RicciFlow.Perelman` to the root import path as the
  index for MSM135 Chapter 6 entropy and no-local-collapsing interfaces.
- Failed: direct root verification did not reach the new import because the
  current workspace is missing `RicciFlower.Curvature.Components.olean`.
- Remaining risk: the new Perelman layer is a statement vocabulary, not an
  analytic proof of entropy monotonicity or no local collapsing.

## 2026-05-15 export scalar/Ricci producer bridge

- Worked: exported `RicciFlower.RicciFlow.Evolution.ScalarRicci` after the new
  bridge file checked, the targeted bridge and scalar-lower-bound modules
  built, and the root import check passed.
- Failed: no root-import proof obstruction appeared.
- Remaining risk: Corollary 7.3 still needs the regular-time to closed-slab
  endpoint bridge if one wants to consume interval-regular evolution directly.

## 2026-05-15 export scalar lower-bound comparison

- Worked: exported `RicciFlower.RicciFlow.Evolution.ScalarLowerBound` from the
  root import after the focused file check and targeted module build passed.
- Failed: no root-import proof obstruction appeared.
- Remaining risk: the module closes the ODE comparison layer, while the full
  Ricci-flow Corollary 7.3 still depends on the heat-operator realization,
  trace/norm Cauchy-Schwarz, and compact initial-infimum producer lemmas.

## 2026-05-13 export curvature-operator evolution scaffold

- Worked: exported `RicciFlower.RicciFlow.Evolution.CurvatureOperator` from the
  root import file after the focused file check and targeted module build
  passed.
- Failed: no proof obstruction appeared in the new module beyond the five
  intentional scaffold `sorry`s.  The root import itself was not checked because
  a downstream Chapter 6 aggregate build is currently blocked by an unrelated
  failure in `RicciFlower/Curvature/Components.lean` near lines 1220 and 1227.
- Remaining risk: the module intentionally carries Section 6.3 frontiers for
  self-adjointness, Lie-square positivity, the `Rm^2 + Rm#` rewrite, and the
  tensor maximum-principle preservation corollaries.

## 2026-05-13 export Uhlenbeck evolution scaffold

- Worked: exported `RicciFlower.RicciFlow.Evolution.Uhlenbeck` from the root
  import file after the focused file check and targeted module build passed.
- Failed: no root-import proof obstruction appeared for the new module.  The
  root import itself was not checked because a targeted downstream BK build is
  currently blocked by an unrelated failure in
  `RicciFlower/Tensor/RicciIdentity.lean` near line 837.
- Remaining risk: the module intentionally carries three `sorry` statement
  frontiers for MSM110 Section 6.2.

## 2026-05-12 export Riemann norm evolution

- Worked: exported `RicciFlower.RicciFlow.Evolution.RiemannNorm` from the root
  import file after the focused module check passed.
- Failed: no root-import proof obstruction appeared.
- Remaining risk: root verification can still be affected by unrelated dirty
  files in the shared workspace; the new module itself checked independently.

## 2026-05-12 export scalar evolution

- Worked: exported `RicciFlower.RicciFlow.Evolution.Scalar` from the root
  import file after the scalar module check and targeted build passed.
- Failed: no root-import proof obstruction appeared.
- Remaining risk: the new scalar theorem assumes the pre-Bianchi scalar
  evolution and contracted-Bianchi reduction as explicit inputs.
