# `Geodesic.lean`

## Result

`HasLEquationAt` records exactly the local regularity that makes the covariant
acceleration genuine, together with vanishing of `lEulerPair` against every
tangent vector.  In particular it does not rely on the default value of
`deriv` at a nondifferentiable point.

`IsLGeodesic S T gamma s` is deliberately indexed by a time set.  It requires
every `tau` in `s` to be positive, to correspond to a regular forward flow
time `T - tau`, and to satisfy `HasLEquationAt`.  This supports local segments
such as `Ioc 0 tau0` without pretending that a raw `Real -> M` curve solves the
singular equation globally.

`lFirst_var_zero` proves the completed direction from the intrinsic equation
to stationarity: an L-geodesic is stationary under every smooth variation
whose first-order endpoint variation fields vanish.

`IsLCritical` is the canonical fixed-endpoint criticality predicate.  It
packages `C⁸` regularity of the central curve and quantifies over genuine
endpoint-fixed smooth variations, so it is neither vacuous on nonsmooth curves
nor stronger than standard variational criticality.  `IsLGeodesic.critical`
proves the forward implication.

`IsLCritical.isLGeo` proves the converse on `Ioo a b` when `0 < a < b` and the
backward interval lies in the regular flow-time set.  A chart-local compactly
supported transverse field is realized by `exists_chartVar`; multiplying it by
arbitrary scalar test functions turns stationarity into the scalar fundamental
lemma.  Continuity upgrades the resulting almost-everywhere Euler identity to
a pointwise identity, and tangent-trivialization cancellation recovers an
arbitrary test vector.

`lEuler_sq` proves the nonsingular square-root-time form of the intrinsic
Euler pairing.  For `alpha(s) = gamma(s^2)` and `A = alpha'`, it establishes

```text
4*s^2*lEulerPair
  = <Y,D_s A> - 2*s^2*<grad R,Y> + 4*s*Ric(Y,A)
```

at every `s > 0` under only the pointwise curve and velocity-chart
differentiability needed by `covDerivAlong`.  The proof uses the generic
reparameterization chain rule and the positive-time velocity germ identity;
it does not assume the Ricci-flow equation, regular-time membership, or a
global smooth curve.

`lRegAccel` is the direct tangent-vector right-hand side

```text
2*s^2*grad R - 4*s*Ric-sharp(A).
```

`lRegAccel_inner` identifies it after pairing with any tangent vector, and
`HasLEquationAt.accel_sq` upgrades the all-test-vector Euler equation to the
intrinsic vector equation `D_s A = lRegAccel`.  This is the form consumed by
the ODE layer; no vector residual is postulated as extra data.

`lPhaseField` is the fixed-chart first-order phase field `(q',v')` obtained by
adding the coordinate Christoffel term to `lRegAccel`.  It is nonsingular at
`s = 0`; `lPhaseField_zero` proves that its zero-time value is exactly the
ordinary geodesic phase field of `g(T)`.  The correct textbook normalization
is `A(0) = 2*Z`, because `A(s) = 2*s*X(s^2)` and the prescribed limit is
`s*X(s^2) -> Z`.

`lPhaseField_smoothAt` proves joint `C^infinity` regularity at every regular
chart phase point.  It reuses the public smooth-family Christoffel theorem,
joint scalar and Ricci component regularity, inverse-Gram smoothness, and the
fixed-chart metric-sharp formula.  No private DeTurck helper or moving sharp
bundle is imported.

`exists_lPhaseSol` gives local phase solutions.  `lPhaseSol_unique_at` proves
germ uniqueness at any regular square-root time, and `lPhaseSol_unique` is its
zero-time specialization.  `lPhaseCurve`, `lPhaseVel`, `lPhase_velocity`, and
`lPhase_accel` reconstruct their intrinsic curve and acceleration.  The
reverse theorem `lRegCurve_phase` turns any intrinsic regularized solution back
into the fixed-chart phase ODE.

`exists_lRegCurve` therefore proves honest local intrinsic existence from
`(T,x,Z)` with `T` regular, including `A(0)=2*Z`, regular backward times,
manifold differentiability, velocity-field differentiability, and the full
regularized acceleration equation on one interval.  `lRegCurve_unique_at`
proves that any two intrinsic solutions with the same position and velocity
agree as germs at any regular square-root time; `lRegCurve_unique` is its
zero-time specialization.

## Resolved third route failure

The converse cannot be obtained by reusing the existing exponential-map
variation realizers without strengthening consumers.  The available
double-endpoint theorem requires, among other structures, `ConnectedSpace M`,
`CompleteSpace M`, a continuous Riemannian-bundle package, and explicit norm
comparison data.  Those assumptions are absent from the current L-geometry
context and are not consequences of it.

Reparameterization variations test only the velocity direction, while the
scalar fundamental lemma alone does not realize arbitrary tangent test fields.
This was a genuine missing-groundwork/API boundary rather than an elaboration
problem.  It is now resolved at the correct generic layer by
`Comparison/Variation/ChartVariation.lean`: a fixed chart, compact thickening,
bounded smooth parameter, and support gluing avoid every disallowed global
assumption.

## Verification and progress

Focused verification of `Geodesic.lean` passed without local warnings.  The
generic chart/covariant bridges, metric-family pairing, metric-sharp formula,
chart variation, and joint scalar/Ricci producers also pass focused
verification, with targeted export refreshes where downstream imports require
them.  The files contain no `sorry`, `admit`, or new axiom.

The first `lExp` domain/totalization brick is now implemented in `Exp.lean`,
following the native ordinary `maximalGeodesic` architecture.  The exact next
stage is to propagate `lRegCurve_unique_at` across common connected witness
domains, prove the pointwise choices coherent, and only then export local
smooth dependence in `(Z,tau)`.

`redVolume_anti` remains **0%**.  Dedicated L-geometry machinery is about
**18--20%**; reusable generic prerequisites are about **60--70%**.  P2 remains
below **1%**, and the whole Poincare program remains about **3--5%**.
