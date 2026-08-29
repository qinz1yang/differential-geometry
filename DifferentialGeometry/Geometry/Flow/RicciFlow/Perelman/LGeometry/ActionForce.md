# ActionForce

## Result

`lChartPosDeriv` is the fixed-chart position covector of the nonlinear
regularized Lagrangian.  Its kinetic coordinates use the actual spatial
Fréchet derivative of `chartGramOp`, and its scalar coordinates use the native
jointly smooth scalar-curvature derivative `chartScalarDeriv`. `lChartForce`
is its canonical Riesz vector, and `lChartForce_inner` identifies pairing with
that vector with application of the position covector.

`lChartForce_int` proves that this force is integrable on a positive compact
time interval for every `timeH1` chart curve whose continuous representative
stays in the interior chart target and whose backward times are regular.  It
does not assume a supplied force, Euler identity, velocity regularity, or an
`L2` force bound.

The proof bounds each spatial Gram derivative on the compact time-position
image and applies the existing time-quadratic integrability theorem to the weak
velocity.  Scalar coordinates are continuous, and finite-dimensional chart
covector reconstruction preserves integrability.  The scoped higher heartbeat
limit is needed for this compact-bound and finite-coordinate assembly; the
focused check takes roughly 15--20 seconds on the current checkout.

## Verification

Focused verification and the targeted module refresh passed without warnings
or placeholders.  The only upstream artifact initially needed by the check
was the explicitly refreshed `MetricFamilyGramSmooth` module.

## Project position

This L1 position-force producer is complete (100%).  The full nonlinear
chart-H1 weak Euler theorem is still unstated and unproved (0%): it additionally
needs differentiation of the nonlinear integral action at an H1 base curve and
derivation of the weak Euler identity from a genuine local minimum.  Its
dedicated checked machinery is now about 80--88%.  Dedicated L-geometry
machinery remains about 78--82%; `exists_lMinimizer` and `redVolume_anti`
remain 0%, P2 remains below 1%, and the whole Poincaré program remains 3--5%.
