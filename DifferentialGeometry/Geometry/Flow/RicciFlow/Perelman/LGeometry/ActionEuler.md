# ActionEuler

`lRegAction_stat` is checked.  It applies the existing full nonlinear
regularized-action first-variation theorem to an actual local minimum along a
smooth variation whose endpoints are fixed for every variation parameter.
Thus the moving metric and scalar-curvature terms are differentiated by the
already checked geometric calculation, rather than being frozen.

`lChartLag` and `lChartAct` name the corresponding nonlinear fixed-chart
integrand and action.  Their Gram coefficient is evaluated at `u.toFun r`;
they are a definition for the next nonlinear H1 calculus step, not a frozen
time-quadratic surrogate.

The intended chart-H1 theorem `lChart_weak_euler` is not yet stated.  Its
position derivative contains the chart-Gram derivative paired with two weak
velocities, hence is naturally an `L¹` force, not an `L²` force.  The present
`timeQuad_weak_euler` API accepts only a fixed coefficient and an `L²`
position force, so it cannot express this nonlinear variation without a new
generic `L¹` nonlinear Nemytskii/first-variation and momentum-primitive API.
No supplied Euler identity, inverse, or regularity hypothesis was added.

Focused verification and the targeted module refresh passed without warnings.
This is a small first Tonelli brick; the nonlinear Tonelli regularity endpoint
and `isLRegCurve_of_min` remain unproved.
