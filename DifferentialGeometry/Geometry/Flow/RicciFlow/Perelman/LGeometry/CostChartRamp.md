# Fixed-chart terminal ramps

## Scope

`CostChartRamp.lean` supplies the local analytic replacement used near the
terminal point of a minimizing regularized L-ray.  The ramp is an affine line
in one fixed extended chart and has an arbitrary prescribed positive duration;
its duration is deliberately not tied to its endpoint displacement.

## Proved interface

- `lChartRamp` realizes the affine coordinate segment as a `timeH1` curve.
- `lRamp_apply`, `lRamp_deriv`, `lRamp_start`, and `lRamp_end` identify its
  representative, weak derivative, and endpoints.
- `lRamp_mapsTo` keeps the whole ramp inside any convex coordinate set
  containing both endpoints.
- `lRampAct_bound` bounds its chart action by
  `Cg / 2 * ‖z - y‖ ^ 2 / L + Cs * L` under honest pointwise Gram and scalar
  bounds on the positive ramp interval.
- `lRampAct_linear` converts this into a bound linear in `L` when
  `‖z - y‖ ≤ V * L`.
- `lRampAct_slab` obtains one nonnegative pair of Gram and scalar constants
  for every positive affine ramp whose time lies in a fixed compact regular
  slab and whose image lies in a fixed compact chart set.

The arbitrary-duration form is essential.  In the terminal replacement, the
old ray endpoint at time `b - L` also moves.  Taking
`L = kappa * endpointDistance`, with `kappa` larger than a uniform chart-speed
constant, controls the total replacement displacement without solving an
implicit fixed-point equation.

## Verification and next theorem

Focused verification of the complete file passed without warnings, and the
explicitly named module refresh passed.

The exact next producer is a compact-slab theorem that obtains `Cg`, `Cs`, and
the chart-speed constant uniformly for a bounded family of minimizing initial
tangents.  It should then choose `L` proportional to endpoint chart distance,
splice the affine ramp onto the shortened ray, and yield the fixed-chart
two-sided local Lipschitz estimate for `lCost`.

## Project accounting

- Fixed-chart affine ramp, explicit action estimate, and compact-slab
  uniformization: 100%.
- Uniform bounded-family terminal replacement: 0% until its compact-slab
  theorem is stated and proved.
- Fixed-chart local Lipschitz theorem for `lCost`: 0% until stated and proved.
- `lCutMulti_null` and `redVolume_anti`: each 0%; this file is dedicated
  infrastructure and does not complete either theorem.
