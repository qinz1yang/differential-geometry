# LowRegCoeffJets

## Route

This file follows the three-dimensional low-regularity route required by the
uniform short-time construction.  It keeps the frozen spectral metric `g0`
separate from the fixed DeTurck gauge background `g_bg`.

The source currently contains:

- `convex_h3_jet`, transferring endpoint spectral `H3` bounds to the whole
  convex path without shrinking time;
- `ricci0_h1` and `dla_h1`, direct range-two jet bounds for the order-zero
  Ricci and `DLa` coefficients;
- `dlbDiff_h1`, a range-two jet bound for
  `DLb(g_bg) - DLb(g0)` obtained from the pointwise grid-window theorem and
  `h3_grid_int`;
- the rank-generic `grid_h1_le` and `h1_of_grid` integration bridge;
- `riem_h1`, the complete range-two jet bound for the fixed-curvature
  `lieCorr0` piece.  Its proof keeps the exact moving double trace applied to
  the fixed curvature passenger, places the trace in `H1`, the passenger in
  `H2`, and uses the mixed `appCcRS` product estimate;
- `tail0_decomp`, the exact cancellation-preserving decomposition of the
  remaining order-zero tail;
- `rhs0_h1_of_aux` and `rhs1_h2_of_aux`, consumer-shaped synthesis theorems
  whose remaining auxiliary inputs are explicit.

The order-zero source frontier after `dlbDiff_h1` and `riem_h1` is the `H1`
control of the insertion difference, vector--bilinear, and mixed fields in
`tail0_decomp`.  The order-one frontier is the `H2` control of the Ricci
`appCcRS` arm and `deTurckLieArm1Coeff`.

## Verification and accounting

The source has not yet been focused-checked because the shared build is under
an exclusive sequential artifact refresh.  None of the new declarations in
this file is counted as verified until that check completes.

`ricci_flow_unif_existence` remains 0%.  This machinery is currently a
three-dimensional route and therefore does not by itself close the existing
dimension-generic public endpoint statement.
