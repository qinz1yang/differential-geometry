# LowRegRhs0Tame

## Mathematical route

The source follows the dimension-three low-regularity route.  The integrated
antidiagonal grids of total order at most two depend only on the lower `H2`
metric radius.  The total-order-three grid is supplied by
`h3_top_grid_int`, where it is linear in the norm of the third covariant
derivative.  `h1_grid_tame` packages this split as
`B0 R + B1 R * A` for an `H1` coefficient jet.

The concrete exports are:

- `ricci0_h1_tame`, `dla_h1_tame`, and `dlbDiff_h1_tame` from their canonical
  pointwise grid estimates;
- `riem_h1_tame`, using the lower-only moving trace and fixed-curvature
  passenger;
- `vb_h1_tame` and `amix_h1_tame`, preserving the existing exact refolds and
  assigning the unique top derivative to the self-background Koszul factor;
- `tail_h1_tame`, assembled only after the `DLb + lieCorr0` cancellation;
- `rhs0_h1_tame`, which transfers independent endpoint spectral `H2` and `H3`
  bounds to the same convex path and returns the complete
  `rhsLow0Coeff` estimate in affine form.

No auxiliary analytic hypothesis, replacement producer, axiom, `sorry`, or
`admit` was introduced.  The complete metric jet needed by the Koszul factor
is bounded by `(R + A)^2`; the proof then expands the resulting constant back
into an exact affine function of `A`.

## Verification and project accounting

This file was intentionally written source-only while the root agent owns the
sequential Lean slot.  Focused verification has not yet been run, so none of
these declarations is counted as checked until that verification succeeds.

The exact theorem `ricci_flow_unif_existence` remains 0% until its unchanged
public statement is proved and verified.  This file advances only the
dimension-three order-zero coefficient machinery; the order-one coefficient,
maximal-regularity realization, uniform-family constants, and same-horizon
smoothing still remain before the endpoint can close.  The smooth forward
uniqueness theorem and the Hamilton positive-Ricci endpoint are unaffected by
this source-only step.
