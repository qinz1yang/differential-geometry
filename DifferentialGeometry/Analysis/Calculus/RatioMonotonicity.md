# RatioMonotonicity.lean

## 2026-07-17 cross derivative to quotient monotonicity

Added `ratio_anti_of_cross`: on an open interval, positivity of `g` and the
cross inequality `f' * g <= f * g'` imply that `f / g` is antitone.

This is the scalar V2b endgame for a radial Jacobian divided by the model
density.  It contains no Riccati or curvature input; those remain the geometric
frontier.

Focused verification passed.

Added `integralRatio_anti`: an antitone positive-denominator density ratio
induces an antitone ratio of the cumulative interval integrals from zero.  This
is the scalar area-to-ball-volume step in Bishop--Gromov.

Focused verification and the explicitly named module build passed.  The two
theorems finish the scalar quotient-and-integration kernel; they do not supply
the geometric radial Jacobian inequality.
