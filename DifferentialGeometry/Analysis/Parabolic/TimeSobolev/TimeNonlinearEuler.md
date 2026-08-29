# Nonlinear time Euler identity

## Scope and status

The generic minimizer-to-Euler theorem in this file is complete and focused
verification passed without warnings.  The exported module was also refreshed
for downstream consumers.  It does not complete a geometric L-minimizer
theorem or reduced-volume monotonicity; those endpoints remain outside this
module.

`timeCoeff_euler` combines the genuine curve-dependent coefficient derivative
from `timeCoeff_line_on` with the nonlinear potential derivative from
`timeNlinPot_line`.  Its combined position force is the sum of the Riesz
coefficient force and the potential gradient.  Quadratic growth of
`coeffForce` and the time-`L²` velocity prove that this force is `L¹`; the
Euler identity is derived from an actual fixed-endpoint local minimizer.

`timeCoeff_line_on` requires differentiability and self-adjointness only at the
affine-tube points
`u.toFun t + c • v.toFun t`, for `c ∈ [-1,1]` and almost every interior time.
It proves the line-integrand derivative from `HasFDerivAt`; it does not assume
the derivative formula.

For the Euler theorem, a geometric consumer may choose a separate positive
scale for every variation.  All tube, measurability, and domination hypotheses
are imposed only on the scaled variation.  The proof applies
`timeCoeff_line_on` there and divides the resulting identity by the positive
scale.  Thus no global extension or cutoff of a chart-local coefficient is
required.

The remaining geometric obligations are explicit: produce the positive tube
scale, prove chart-coefficient differentiability and self-adjointness on that
tube, establish strong measurability of the line integrand and its derivative,
and give a common integrable majorant.  The base-curve coefficient and its
spatial derivative also need measurable uniform bounds.  The nonlinear
potential keeps the separate joint-continuity/gradient interface from
`timeNlinPot_line`; this file does not pretend that measurable coefficient
velocity supplies potential regularity.

## Progress boundary

- `timeCoeff_line_on`: theorem 100%; dedicated local-tube derivative machinery
  100%.
- `timeCoeff_euler`: theorem 100%; its generic analytic assembly 100%.
- Geometric `ActionWeakEuler` consumption of these APIs: 0% in this file; its
  chart tube, domination, and coefficient-identification proofs are separate.
- The broader Perelman L-geometry program is roughly 80--84% complete after
  this generic result.  The terminal `exists_lMinimizer` and `redVolume_anti`
  theorems remain unstated/unproved endpoints (0% each).

No `sorry`, `admit`, or new axiom is used.
