# Continuous chart-force representatives

## Result

`lChartPosRep` and `lChartForceRep` evaluate the existing nonlinear chart
position derivative at a supplied coordinate-velocity representative.  The
kinetic term uses the actual spatial derivative of `chartGramOp`; the scalar
term uses the canonical whole covector `chartScalCov`, not a new scalar-force
interface.

`lChartForceRep_cont` proves that this force is continuous on a regular compact
chart interval whenever the supplied velocity representative is continuous.
`lChartForceRep_ae` proves that it agrees almost everywhere with the original
`lChartForce` when the supplied velocity represents `u.deriv` for
`timeMeasure`.

The scalar compatibility proof uses `chartScalCov_apply` once to identify the
whole covector on each chart basis vector.  It does not repeat the expensive
coordinatewise scalar smoothness proof which previously blocked the nonlinear
weak-Euler module.

## Verification and project position

Focused verification and the explicitly named module refresh both passed.  The
source has no `sorry`, `admit`, or axiom declarations, and all public names are
within the twenty-character project limit.

This module is complete (100%) as a dedicated bootstrap producer.  The exact
next consumer is the C2 upgrade: combine `chartVel_rep_c1` with
`lChartForceRep_cont` and `lChartForceRep_ae`, feed that continuous force into
the actual weak momentum identity, and identify the derivative of the continuous
chart-velocity representative with the chart Euler right-hand side.  Dedicated
L-geometry machinery is roughly 84% complete, while the terminal
`exists_lMinimizer` and `redVolume_anti` theorems remain 0% until each is stated
and proved.  The broader P2 endpoint is below 1%, and the whole Poincare program
remains roughly 3--5% complete.
