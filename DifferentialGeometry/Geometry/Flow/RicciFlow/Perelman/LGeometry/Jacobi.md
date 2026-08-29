# Regularized L-Jacobi fields

## Current definition layer

`Jacobi.lean` starts L4 in square-root time.  It defines the fully paired
scalar residual `lRegJacobiPair`, rather than introducing a bundle-valued sharp
field or beginning with the singular backward-time equation.

At square-root time `s`, both along-curve covariant derivatives use the metric
frozen at `T - s^2`.  With `A = alpha'` and `DY = D_s Y`, the residual is

```text
<W,D_s^2 Y> + <W,R(Y,A)A>
  - 2 s^2 Hess(R)(Y,W)
  + 4 s (nabla_Y Ric)(A,W)
  + 4 s Ric(DY,W).
```

The derivative slot of `totalNabla0SFun` is first, hence the native slot order
for the Ricci-derivative term is `(Y,A,W)`.  `HasLRegJacobiAt` keeps pointwise
regularity separate from the equation, and `IsLRegJacobi` quantifies it over a
set.  No Ricci-flow equation, interval, positivity, or completeness assumption
is built into these definitions.

## Status

The full regularized variation-to-Jacobi chain is focused-green and
warning-free.  `lRegVar_reg`, `lRegEuler_deriv`, `lRegVar_jacobiAt`, and
`lRegVar_jacobi` prove the transverse linearization without unfolding tensor or
Hom representations.  `lRegJacobiField` is the initial-tangent differential of
the maximal regularized L-curve; `lRegCurve_jacobi` proves its Jacobi equation,
`lExpJacobi_eq` identifies it with the differential of `lExp`, and
`lRegJacobi_d0` proves the normalized initial derivative `D_s J(0) = 2 V`.
The zero-time residual and pointwise equation projections are also checked.

The connection-calculus part of the nonsingular dynamic equation is now
exposed once as `lRegJacobi_dyn_eq`.  It assumes only differentiability of the
field and of its frozen-metric covariant derivative, and keeps the paired
Jacobi residual on the right-hand side.  The older `lRegJacobi_dyn` public
theorem retains its signature and is a short corollary obtained by setting
that residual to zero.  Focused verification passed without warnings.

The next exact theorem is `lRegJacobi_unique`: uniqueness on a connected
regularized-time interval for a regularized Jacobi field with prescribed value
and covariant derivative at one time.  This is the missing initial-value bridge
needed before defining L-conjugate points and proving index positivity.  It
should be derived from the existing regularized phase-flow uniqueness rather
than exposed as a new assumption.

`redVolume_anti` remains **0%**.  The regularized Jacobi producer chain above is
complete; the broader L4 phase is about **70--75%**, with Jacobi initial-value
uniqueness, conjugacy, and index positivity still outstanding.  Dedicated
L-geometry machinery overall is about **48--52%**; generic reused
infrastructure is about **88--92%**.
