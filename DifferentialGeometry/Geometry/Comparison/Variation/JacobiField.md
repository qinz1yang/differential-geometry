# JacobiField notes

## 2026-07-08

- Added `ode_bound_of_isJacobiAt`: a generic projection from a pointwise
  Jacobi equation plus a curvature-term norm bound to the
  second-covariant-derivative norm bound consumed by covariant Gronwall
  estimates.
- The lemma is intentionally only a projection/adapter.  It does not prove a
  curvature operator bound, Jacobi-field differentiability, or any radial
  smallness theorem.
- Verification passed for the focused file check and targeted module build.
