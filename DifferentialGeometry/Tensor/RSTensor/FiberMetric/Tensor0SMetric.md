# Covariant tensor metric

## 2026-07-16 squared-norm sign

Added `normSq0S_nonneg`, the canonical nonnegativity projection from the
metric-induced fiber inner product.  This avoids reopening coordinate sums in
downstream square-sign arguments.  Focused verification passed without a new
`sorry`.

This is a reusable tensor-layer producer; its use in the `W` derivative sign
does not count as completion of the no-local-collapsing endpoint.

## 2026-07-22 fibre Cauchy--Schwarz

Added `inner0S_sq_le_mul`, the invariant Cauchy--Schwarz inequality for the
metric-induced inner product on arbitrary covariant tensor fibres.  The proof
uses the existing `MetricFiberData` inner-product core and does not introduce
coordinates or curvature assumptions.  Focused and exported verification
passed.

This helper is complete.  It is infrastructure for the curvature-tower Kato
estimate; the complete noncompact Bernstein theorem remains theorem-level 0%.
