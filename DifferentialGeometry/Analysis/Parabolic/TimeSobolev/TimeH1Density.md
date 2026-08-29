# Time H1 density

## Result

`exists_flat_dense` proves fixed-endpoint strong density for vector-valued time
`H1` curves on a positive interval in a finite-dimensional real normed space.
It returns global `C1` functions and their exact `timeH1` realizations.  The
functions agree with the original continuous representative at both endpoints,
are constant on neighborhoods of both endpoints, converge strongly in
`timeH1`, and their realized derivatives converge strongly in `timeL2`.

## Construction

The proof uses `exists_flat_deriv` from `TimeH1Flat` for smooth derivative
approximation.  Its support inclusion in `Ioo 0 T` alone does not imply a zero
germ at either endpoint, so a shrinking interior bump is applied.  The added
boundary-layer error is controlled by `MemLp.eLpNorm_indicator_le`.

A fixed normalized interior bump corrects the total derivative integral.  The
correction tends to zero because the native `timeIntegral` is continuous.  The
corrected derivative is integrated globally, producing a global `C1` primitive
with exact endpoint values and constant endpoint germs.  Native
`timeH1.ofContDiffOn` realizes each primitive and supplies exact representative
agreement on `Icc 0 T`.

All interval-integral and `timeMeasure` identifications are proved explicitly;
the endpoint correction uses `ContDiffBump.integral_normed`.

## Verification

Focused verification passed without placeholders or diagnostics.

## Project status

- Generic `exists_flat_dense` producer: 100%.
- Downstream `lAction_c1_dense`: 100%, now checked in `ActionDensity.lean`.
- `exists_lMinimizer`: 0% until the minimizer theorem is proved.

This module is analytic infrastructure for the L-geometry density lane.  It
supplies the terminal missing density input but does not itself prove minimizer
existence or reduced-volume monotonicity.
