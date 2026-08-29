# Integral-curve transport

## API correction

The integral-curve transport and uniqueness theorems are universe-polymorphic
and now use `IsManifold I ∞ M`. Their inputs are smooth maps and `C^1` vector
fields, so no analytic-manifold assumption is needed. The `ContDiff` scope is
opened explicitly for the smoothness-order notation.

## Verification

Focused verification and the targeted module export pass without warnings.
In particular, `integralCurve_eq_of_agree_zero` now applies directly to the
smooth tangent-bundle flow used in field realization.
