# `JointRegularity.lean`

## Result

`chartRicci_joint` proves joint `C^infinity` regularity of fixed-chart Ricci
components on regular spacetime chart domains.  The proof uses the Ricci-flow
identity `Ric = -1/2 * partial_t g` together with the native smooth
metric-component and first-time-derivative APIs.

`chartNablaRicci` upgrades this to fixed-chart components of the covariant
derivative of Ricci.  It differentiates the checked chart Ricci components in
the spatial direction and uses the native `nablaRicChartComp` coordinate
identity for the two Christoffel correction terms.  `nablaRicci_cont` then
packages these components as a continuous rank-three covariant tensor family
on regular time, using the existing chart-basis component reconstruction API.

## Verification and use

Focused verification and the targeted export refresh passed without warnings.
The new family theorem supplies the covariant-Ricci coefficient continuity
needed by the fixed-chart Jacobi ODE.  This is generic regularity
infrastructure; it does not itself prove any L-geodesic uniqueness or reduced
volume monotonicity endpoint.
