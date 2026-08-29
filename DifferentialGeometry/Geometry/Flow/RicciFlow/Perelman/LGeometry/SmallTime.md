# SmallTime

This module begins the zero-backward-time normalization needed for the
L-geometric reduced-volume argument.

## Checked producer

`lRayAct_zero_lim` proves that the regularized action of the maximal L-ray
with initial tangent `Z`, divided by `2 * s`, converges from the right to
`g(T)(Z,Z)`.  The proof uses joint smoothness of the ray Lagrangian, the
fundamental theorem of calculus at zero, and the normalization
`lVelocity (lRegCurve ...) 0 = 2 • Z`.  It fully evaluates the moving metric
on the velocity before taking the limit.  Focused verification passed without
warnings.

`lRedLen_sq_lim` is the checked thin minimizing-ray bridge.  A
single later strict-minimizing-domain witness supplies minimizing membership
for all sufficiently small positive squared times through `lMinDomain_down`;
on that filter, reduced length is the normalized ray action.  This avoids
assuming a separate global short-time minimizing theorem for the pointwise
Jacobian asymptotic.  Focused verification passed without warnings.

## Remaining zero-time chain

The next local producer is the normalized L-exponential density limit.  It
requires the first-order regularized Jacobi limit, then finite-dimensional
Gram determinant continuity.  The separate global reduced-volume limit still
needs eventual exhaustion of `lInjDomain`; that is a genuine short-time
strict-minimizing result, not a measure-theory wrapper.
