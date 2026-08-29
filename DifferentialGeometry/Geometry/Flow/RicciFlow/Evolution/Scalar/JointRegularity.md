# `JointRegularity.lean`

## Result

The existing joint scalar-curvature theorem remains canonical.
`chartScalFun_smooth` is now public and exposes the whole chart scalar value as
a jointly smooth function on regular time times the chart-target interior; the
weak-Euler consumer reuses it instead of rebuilding chart inversion and scalar
composition.  The added
`chartScalarDeriv` result exposes joint `C^infinity` regularity of the spatial
scalar differential in a fixed chart on regular spacetime chart domains.
The new `chartScalCov` packages the whole spatial differential canonically as
the full joint chart-scalar `fderiv` postcomposed with the spatial inclusion
`E -> Real x E`.  `chartScalCov_smooth` proves joint `C^infinity` regularity
without finite basis reconstruction; `chartScalCov_eq` and
`chartScalCov_apply` identify it with the ordinary fixed-time derivative of
`scalarOnE`.

`chartScalarHess` differentiates each checked first coordinate component once
more in the spatial variable and adds the smooth Christoffel correction.
`scalarHess_cont` reconstructs these components as a continuous rank-two
covariant tensor family of scalar Hessians on regular time.  All three results
stay in fixed-chart scalar coordinates rather than creating a moving
gradient-bundle API.

An earlier route first converted `scalar_joint` after chart composition to a
model-space `ContDiffOn` theorem and then differentiated twice.  That conversion
hit a deterministic `whnf` performance wall even after being isolated.  The
checked route instead reuses `chartScalarDeriv`, identifies it with the native
`partialDeriv` component, and differentiates only once.

## Verification and use

Focused verification and the targeted export refresh passed without warnings.
The axiom audit for the three covector theorems reports only the standard
`propext`, `Classical.choice`, and `Quot.sound` dependencies.  The canonical
covector removes the scalar finite-coordinate elaboration wall encountered by
the fixed-chart weak Euler producer.

The scalar Hessian family supplies a coefficient-continuity producer for the
fixed-chart Jacobi ODE.  This is generic regularity infrastructure; it does not
itself prove L-geodesic uniqueness or reduced-volume monotonicity.

The covector producer itself is complete (100%).  It is one lower-layer input
to the still-unverified fixed-chart weak Euler theorem, not completion of that
endpoint.  Dedicated L-geometry remains about 78--82%; reduced-volume
monotonicity remains 0%, P2 remains below 1%, and the whole Poincare program
remains about 3--5%.
