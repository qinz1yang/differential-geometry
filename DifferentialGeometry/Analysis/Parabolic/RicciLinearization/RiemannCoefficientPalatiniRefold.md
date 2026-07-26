# RiemannCoefficientPalatiniRefold additions

## Low-regularity exports

Two small public aliases were added without changing their underlying proofs:

- `endo_eq_dlb` exposes the equality between the geometric endomorphism arm
  and the concrete `DLb` coefficient field.
- `dlbDiff_grid` exposes the existing pointwise product-grid estimate for the
  change `DLb(g_bg) - DLb(g0)`.

The second estimate has grid window `i + 2`; for `i < 2` it is integrable from
the metric jet through order three in dimension three.

## Verification

Focused verification is pending the shared sequential artifact refresh.  The
underlying producer proofs pre-existed; only their public aliases are new.
