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

## 2026-07-17 Wronskian conservation

- Added `jacobiWronskian`, `wronskian_deriv_at`, and `wronskian_zero_on`.
  The derivative theorem needs only pointwise curve regularity and pointwise
  Jacobi equations; the interval theorem integrates this zero derivative when
  both fields vanish at the centre.
- Kept `hasDerivAt_wronsk` and `wronskian_eq_zero` as smooth-curve compatibility
  wrappers over the weaker pointwise API.
- Focused verification and the explicitly named module build passed.  The
  radial specialization is supplied separately by `RadialGram.lean`.
