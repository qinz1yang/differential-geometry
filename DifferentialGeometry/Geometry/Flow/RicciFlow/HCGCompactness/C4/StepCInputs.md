# StepCInputs.lean

## 2026-06-30

Added the C4-layer strict distance-squared convexity input for MSM135
`lbl413`/`lbl416`.

The input is intentionally shaped exactly like
`CenterOfMass.exists_unique_curve*`: it packages the midpoint containment,
endpoint laws, and per-summand `StrictConvexOn` statement along the selected
joining curves in the Hopf--Rinow metric world. It does not claim to prove the
Hessian comparison.

Verification passed for the focused file check and the targeted module refresh.

Implementation trap: this file must live in the same RiemannianBundle instance
world as `CenterOfMass.lean`. The local `Tensor0SBundle` tangent norm instances
are removed so `g.toRiemannianMetric` controls tangent fibers.

The index type is currently restricted to `Type`, matching the finite-gradient
equation endpoint in `CenterOfMass.lean`.

## 2026-07-14 producer audit

`StrictDistInput` remains the correct consumer shape, but it is not itself a
proved producer.  The two-point join portion is now discharged by the
focused-green `Geometry/Comparison/GeodesicConvexity.minJoin` API.  A future
C4 adapter should use that join rather than quantify over a new selector.

The precise unresolved mathematics is the `lbl412` Hessian identity and the
`lbl413` uniform positive Hessian lower bound on the controlled, cut-locus-free
bootstrap ball.  The target `p` instance gives midpoint confinement, while the
active point instances give the `strict` field.  Existing second variation only
proves index-form nonnegativity.  Therefore the concrete `StrictDistInput`
producer remains 0%, and no additional input structure was added here.
