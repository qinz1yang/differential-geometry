# ShiBallCalabi

## Status

`exists_ballCalabi` is source-written. It is the fixed-time bridge from an
Rm-controlled flow metric ball to a Calabi distance upper support on the inner
half-radius ball. The selected comparison tail is shortened so its whole
Jacobi interval remains in the controlled outer ball.

The coefficient is `q = finrank E / radius`. When the transverse dimension is
positive, this dominates the pointwise Ricci loss obtained from
`ricci_ge_of_rm`; the zero-transverse-dimension branch needs no Ricci input.

Focused verification is warning-free GREEN.

## Next theorem

Use this fixed-time support inside the time-dependent radial cutoff to produce
`ShiCutoffLowerSupportAt` with error of order `radius⁻²`, then apply the finite
compact-support maximum-principle estimate for the `m = 1` Bernstein quantity.
