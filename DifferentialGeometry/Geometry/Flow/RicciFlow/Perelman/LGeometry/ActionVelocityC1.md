# C1 coordinate velocity

## Result

`chartVel_c1_of_mom` inverts the genuine chart Gram operator along a `C¹`
time-position curve.  A `C¹` momentum representative therefore gives a `C¹`
coordinate-velocity representative with the honest almost-everywhere equality
to the weak derivative.

`chartVel_rep_c1` starts from the actual fixed-chart weak Euler identity with a
continuous force.  It first uses `mom_rep_c1`, then the existing continuous
momentum-to-velocity theorem to obtain the `C¹` chart position, and finally the
smooth Gram inverse to upgrade the velocity.  The resulting representative is
also the pointwise `derivWithin` of `u.toFun` on the closed interval.

No inverse, velocity regularity, primitive representation, or Euler equation
is supplied as a conclusion-shaped hypothesis.

## Native inverse API

`MetricFamilyGramInv` now provides `chartGramInv_smooth`.  It combines the
existing joint smoothness of `chartGramOp`, the coercivity-derived
`chartGramOp_unit`, and Mathlib's smoothness of ring inversion at a unit.  No
new operator or inverse data was introduced.

## Status and project position

Focused verification and the targeted module refresh passed without warnings.
Both public velocity theorems and this module's dedicated C1 assembly are
complete (100%).  This closes the generic continuous-force momentum-to-C1-
velocity bootstrap, but does not yet identify the velocity derivative with the
full geometric regularized L-acceleration or bootstrap the chart equation to
smoothness.  Dedicated L-geometry remains roughly 81--85%.  The terminal
`exists_lMinimizer` and `redVolume_anti` endpoints remain 0% until stated and
proved; the whole Poincare program remains roughly 3--5%.

The source contains no `sorry`, `admit`, or new axiom.
