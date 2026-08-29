# `RegCurveAt.lean`

## Result

`exists_lRegCurve_at` constructs an intrinsic regularized L-acceleration
solution through arbitrary data at an arbitrary regular square-root time.  For
`x : M`, `A0 : TangentSpace I x`, and regular `T - s0^2`, it returns a positive
radius and a curve `alpha` satisfying

```text
alpha s0 = x,
lVelocity alpha s0 = A0,
```

together with manifold differentiability, differentiability of the actual
velocity chart representative, and the intrinsic acceleration equation at
every time in `Ioo (s0 - epsilon) (s0 + epsilon)`.

## Construction

The phase seed is

```text
(extChartAt I x x, trivToE x x A0).
```

The proof applies `exists_lPhaseSol_at` at the original base time `s0`, then
shrinks its interval so the position component remains in the chart interior.
`lPhase_velocity` identifies the reconstructed phase velocity with the actual
`lVelocity` as germs; `lPhaseCurve_mdiff` and `lPhaseVel_diff` supply the two
regularity statements, and `lPhase_accel` plus covariant-derivative germ
congruence supplies the intrinsic equation.

Unlike the zero-time constructor, the prescribed velocity is used directly;
there is no `2 * Z` normalization.  No regularized solution, Euler equation,
extra consumer assumption, reference import, new class, or frontier wrapper is
assumed.

## Verification and progress

Focused verification passed without warnings or placeholders.  Arbitrary-base-
time intrinsic regularized L-curve existence is 100% complete.  The terminal
`exists_lMinimizer` and `redVolume_anti` remain 0%; dedicated L-geometry
machinery is approximately 98%, reused generic infrastructure is 100%, P2
remains below 1%, and the whole Poincare program remains approximately 3--5%.
