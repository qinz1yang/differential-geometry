# Regularized L-index form

## Definition and normalization

`lRegIndexInt` is the square-root-time density for `alpha(s) = gamma(s^2)`.
Writing `A = alpha'`, `DY = D_s Y`, `DW = D_s W`, and letting `N` denote the
covariant derivative of Ricci with its derivative slot first, it is

```text
1/2 * (<DY,DW> - Rm(Y,A,A,W))
  + s^2 * Hess(R)(Y,W)
  + s * (N(A,Y,W) - N(Y,A,W) - N(W,A,Y)).
```

The coefficients are normalized so that the checked pointwise balance is

```text
d/ds <D_s Y,W> = 2 * lRegIndexInt(Y,W) + lRegJacobiPair(Y,W).
```

`lRegIndex` is the oriented interval integral of this density.  Pointwise and
integrated symmetry are proved intrinsically from metric, curvature-pair,
Hessian, and covariant-Ricci symmetries.

## Green identity and the initial endpoint

`lRegIndex_green` integrates the balance without any positive lower-endpoint
assumption, so its interval may start at `s = 0`.  The theorem keeps honest
interval-integrability hypotheses for the index density and residual.
`lRegIndex_zero_ends` removes both boundary pairings, while
`lRegIndex_jacobi` removes the residual along a regularized Jacobi field.

At positive `s`, `lRegIndexInt_sq` proves the exact Jacobian identity

```text
lIndexInt(s^2) * (2*s) = lRegIndexInt(s).
```

The pointwise identity is deliberately not asserted at `s = 0`.  The integral
bridge `lIndex_sq` uses monotone substitution and an almost-everywhere
congruence that excludes the singleton `{0}` before invoking the positive-time
formula.  Both orientations of the interval are supported.

## Interval congruence

`lRegIndex_congr` proves that the index form depends only on the two fields on
the unordered open interval between its endpoints.  The proof uses
neighborhood equality to transport both covariant derivatives, then removes
the remaining endpoint by an almost-everywhere interval-integral congruence.
It deliberately does not assert equality of endpoint derivatives from equality
on a closed interval.

## Status and next frontier

Focused verification and the targeted module export pass without warnings.
The regularized index/Green/square-time/congruence brick is complete and is now
used by the arbitrary-field minimizing index theorem.

`redVolume_anti` remains **0%**.  The L4 index infrastructure is complete;
dedicated L-geometry machinery overall is approximately **62--66%**, while
generic reused infrastructure is approximately **94--96%**.
