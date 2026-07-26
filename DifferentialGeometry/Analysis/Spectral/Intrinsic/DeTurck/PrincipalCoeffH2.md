# PrincipalCoeffH2

## Goal

Produce the pointwise order-zero and order-zero-through-two `L2` jet bounds for
the DeTurck principal-cometric coefficient from a small three-dimensional
spectral `H2` metric perturbation.  These are exactly the coefficient inputs of
`appCc_h2_h3_h1`.

## Current route

The order-two inverse-metric product grid is integrated by the antidiagonal
Gagliardo--Nirenberg engine.  Small `H2` controls the zeroth metric jet
pointwise, the first metric jet in `L4`, and the second metric jet in `L2`.
The inverse coefficient is then handled separately at orders zero, one, and
two; `principal_coeff_h2` projects those bounds to the DeTurck coefficient.

`principal_arm_h2` then composes that coefficient envelope with the
three-dimensional `H2 x H3 -> H1` `appCc` estimate.  Its conclusion is the
actual DeTurck principal-cometric arm bound, with operator size linear in the
metric perturbation's spectral `H2` norm.

`inv_coeff_h2`, `principal_coeff_h2`, and `principal_arm_h2` passed focused
verification and the target module build.  They contain no new assumptions or
local sorries and are theorem-level complete.

The direct two-endpoint add-subtract route leaves a genuine coefficient
difference multiplying the single-endpoint second jet.  The better existing
route is the Ricci path linearization: its highest-order arm uses the single
intermediate metric on the convex path and acts directly on the second jet of
`T - T'`.  `principal_path_h2` now packages the uniform pointwise/two-jet
coefficient bound on the totalized `realizedFam` used by the path-integral
algebra; `delta < 1`, `delta' < 1`, and `s in [0,1]` select its genuine path
branch.  Writing the proof-dependent `realizedMetricPath` twice in the theorem
conclusion hit an 800k-heartbeat `whnf` performance wall, so the equivalent
totalized form is intentional.  The totalized theorem passed focused
verification without local warnings or `sorry`.  The lower path arms still
require separate low-regularity H1 coefficient bounds.

## Project accounting

Uniform low-regularity Ricci--DeTurck existence and
`ricci_flow_unif_existence` remain unstated or unproved at theorem level (0%).
This file addresses only the nonlinear principal-coefficient producer.  Even
after it verifies, the lower-order remainder split, the low-regularity solver,
and same-interval smoothing remain separate frontiers.
