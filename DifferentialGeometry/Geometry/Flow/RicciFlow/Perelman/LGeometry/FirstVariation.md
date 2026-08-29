# `FirstVariation.lean`

## Result

The file proves the complete first-variation stage for Perelman's oriented
L-length.  `lLength_first_var` gives

```text
delta L = 2 sqrt(b) <Y,X>_b - 2 sqrt(a) <Y,X>_a
  + integral_a^b [
      sqrt(tau) <grad R,Y>
      - 1/sqrt(tau) <Y,X>
      - 2 sqrt(tau) <Y,D_tau X>
      - 4 sqrt(tau) Ric(Y,X)] d tau.
```

There is no ordering assumption on `a,b`; the statement respects oriented
interval integrals.  The only time assumptions are positivity on the compact
interval and regularity of the corresponding forward times.

`lEulerPair` packages the scalar pairing of the intrinsic Euler residual with
one tangent vector.  It remains fully applied and pointwise, so no moving
Ricci-sharp bundle object is introduced.  `lLength_euler` rewrites the interior
term as `-2 sqrt(tau) * lEulerPair`.  The auxiliary results
`lGrad_contOn`, `lCross_contOn`, and `lEuler_contOn` expose exactly the
continuity later needed by the scalar fundamental lemma, while
`lEulerPair_smul` records linearity in the test vector.

The differentiation-under-the-integral proof produces its compact domination
internally.  It uses the current `scalar_joint`, `metricCLMSmoothAt`, and native smooth
variation velocity fields to obtain joint `C^1` control.  No Lipschitz,
domination, or integrability hypothesis is passed to the consumer theorem.

The later second-variation layer also consumes `lEuler_var_c1`.  This theorem
proves joint `C^1` regularity of the weighted Euler residual in the variation
parameter and backward time.  Its proof differentiates three fully paired
jointly `C^2` scalar functions (scalar curvature, speed square, and the mixed
metric pairing); it never compares a moving tangent bundle or connection-valued
object.  Consequently the transverse Jacobi-pair integrability needed by the
fixed-endpoint second variation is generated internally on every positive
compact regular interval.

## Routes rejected

1. Fixed-time scalar smoothness plus joint scalar-value continuity does not
   control the spatial derivative uniformly on a compact spacetime slab.
2. A pointwise difference-quotient or FTC argument has the same missing
   uniform bound and cannot replace dominated differentiation.

Both failures were resolved at the producer layer by proving genuine joint
spacetime regularity, not by strengthening the first-variation consumer.

## Verification and next API

Focused verification and the targeted module refresh passed without local
warnings.  The file contains no `sorry`, `admit`, or new axiom.

The fixed-endpoint converse consumes these continuity results together with the
generic `exists_chartVar` producer and is proved in `Geodesic.lean`.  The
square-root regularized Euler identity is proved by `lEuler_sq`, which identifies
`4*s^2*lEulerPair` with the nonsingular pairing

```text
<Y,D_s A> - 2*s^2*<grad R,Y> + 4*s*Ric(Y,A).
```

`SecondVariation.lean` now uses `lEuler_var_c1` to prove the natural-input
fixed-endpoint theorem `lLength_second_var`; no regularity or integrability
hypothesis is added to that consumer.

## Progress

`redVolume_anti` remains **0%**.  Dedicated L-geometry machinery is about
**48--52%**; reusable generic prerequisites are about **88--92%**.  P2 as a
whole remains below **1%**, and the whole Poincare program remains about
**3--5%**.
