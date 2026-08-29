# `Exp.lean`

## Result

`IsLRegCurveOn` records the nonsingular square-root-time equation with the
Perelman normalization `A(0) = 2 • Z`.  `LRegCurveWitness` requires a solution
on an open preconnected interval containing zero and the queried time.

The maximal witnessed domain `lRegDomain` is open and preconnected;
`lRegDomain_seg` records its nonnegative initial-segment closure, while
`lRegDomain_reg` recovers regular Ricci-flow time at every member.  The
totalized `lRegCurve` returns the base point outside this domain, and
`lRegWitness_eq` proves that any two witnesses with the same initial data agree
on the intersection of their domains.  Consequently `lRegCurve_eqOn` identifies
the totalized curve with every witness on its witness interval.
`lRegData_congr` exports the corresponding germ-invariance theorem for the
full pointwise regularized data, and `lRegCurve_eqIcc` restricts an open
solution witness to a nonnegative closed interval.

The local-flow layer now exports the full maximal-domain smooth-dependence
chain without adding a new solution class or a stronger consumer assumption:

* `exists_lPhaseFlow` gives a jointly smooth phase flow near a regular phase
  seed and keeps it inside the regular chart domain;
* `exists_lPhaseAt` restarts that flow at an arbitrary absolute square-root
  time, while `exists_lPhaseComp` supplies one common restart time on a compact
  phase trajectory lying in a fixed chart;
* `exists_lRegFamily` reconstructs a jointly smooth family of intrinsic
  regularized L-curves for nearby initial tangent vectors on one common
  square-root-time interval;
* `lRegSol_eqOn` propagates arbitrary-time phase-state uniqueness, and
  `lRegFamily_step` glues one restarted family to an existing family;
* `lPhaseSeed_vel` exposes the intrinsic-to-chart velocity seed identity, and
  `lRegFamily_step_of` exposes the supplied-flow family splice used by compact
  phase-cage continuation arguments;
* `lRegFamily_extend` uses an open/closure-stable good-time argument and the
  compact uniform phase-flow radius to continue a common parameter family
  across any compact segment of a witness;
* `lRegCurve_smooth` identifies the continued family with the maximal
  totalized curve at every point of its domain.  Consequently
  `lRegJointDom_open` and `lRegCurve_smoothOn` give the joint open-domain API;
* `lRegCurve_c1On` fixes the initial tangent and restricts that joint
  smoothness to every nonnegative closed segment of the maximal domain.

`lExpDomain` is the nonnegative pullback of `lRegDomain` by `sqrt`, and `lExp`
evaluates `lRegCurve` at square-root time.  `lExpPosDom` is its joint positive
part; it is open, and `lExp_smoothOn` proves joint smoothness throughout it.
At every positive backward time, `lExp_vel_sqrt` identifies the terminal
regularized velocity with `2 * sqrt tau` times the velocity of the ordinary
backward-time `lExp` ray.  This is a pure reparameterization identity and needs
no regular-domain or solution hypothesis.
`lExpPosDom_down` transfers positive-domain membership to every smaller
positive backward time, and `lExpPosDom_reg` supplies regular Ricci-flow times
on the full associated nonnegative square-root-time segment.
`exists_lExpFamily` remains the useful uniform short-time box theorem, while
the regularized `s`-family supplies the smooth extension through `s = 0`.
The normalization remains `A(0) = 2 Z`; no ordinary exponential map is used
to define `lExp`.

## Verification and boundary

Focused verification passed without warnings after the endpoint-facing,
domain-restriction, restart-facing, and velocity-reparameterization exports.
Axiom audits of `lRegCurve_c1On` and
`lExpPosDom_reg` report only `propext`, classical choice, and quotient
soundness.  The file contains no `sorry`, `admit`, or new axiom.

The full positive maximal-domain smoothness claim is now complete.  Smoothness
at `tau = 0` is intentionally expressed through the regularized `s` variable:
`sqrt` itself is not smooth at zero.  Pullback and parabolic-scaling naturality
are now complete in `Naturality.lean` and `Scaling.lean`, so L3 is closed.  L4
Jacobi work may use `lExp_smoothOn`, but must still keep zero-time arguments in
the regularized formulation.

`redVolume_anti` remains **0%**.  The compact global-regularized-C1 minimizer
and its identification with `lExp` are complete; the global cut-domain stage
has only its local-diffeomorphism and endpoint-identification producers.
P2 remains below **1%**, and the whole Poincare program remains about
**3--5%**.
