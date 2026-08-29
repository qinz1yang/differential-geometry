# L-Jacobi and second variation

## Implemented surface

`SecondVariation.lean` contains the ordinary backward-time L-Jacobi predicate
and the fixed-endpoint second-variation layer.  The public declarations include:

- `HasLJacobiAt` and `IsLJacobi` for the dynamic L-Jacobi equation;
- `lJacobiPair_sq`, the paired scalar square-root-time identity relating the
  dynamic and regularized Jacobi residuals;
- `lJacobiVel_sq_diff`, `lJacobi_of_sq`, and `lExp_jacobi`, which reconstruct
  the moving-metric derivative, descend the regularized equation, and identify
  the differential of the L-exponential map with a dynamic L-Jacobi field;
- `lEuler_var_deriv`, `lEuler_var_geo`, and `lEulerInt_deriv`, which linearize
  the Euler residual and its weighted integral;
- `lVarJacobiVel_diff` and `lVarInner_c1`, the positive-time regularity
  producers used to discharge the Green-identity hypotheses;
- `lVarMetric_c2`, the joint `C²` producer with independent metric and curve
  times used by endpoint-zero regularized variation arguments;
- `lIndexInt`, `lIndex`, symmetry, diagonal, zero, adjacent-additivity,
  the pointwise `lIndex_balance`, `lIndex_green`, `lIndex_zero_ends`, and
  `lIndex_jacobi`;
- `lLength_second_jac` and the natural-input capstone
  `lLength_second_var`.

The square-root bridge deliberately works after fully pairing every moving
tangent vector with an arbitrary test vector.  It combines the fixed-metric
square-reparameterization product rule, `covAlong_diff`, and the Ricci-flow
connection-backward pairing formula.  This avoids equality of whole moving
bundle or Hom-valued objects.  The signs and factors are the genuine ones:
the velocity contributes `2 s`, the second-order term contributes `4 s^2`,
and the connection correction combines with the explicit Ricci derivative
terms in the dynamic residual.

The reusable Green identity keeps honest interval-integrability hypotheses
explicit.  The concrete smooth fixed-endpoint consumer does not inherit them:
`lLength_second_var` derives positivity of time, regularity, variation-field
regularity, and all three required integrability facts internally.  Its result
is the exact scalar identity

```text
d/du|_0 (d/dv L(f(v,-))|_u) = 2 I(Y,Y),
```

where `Y` is the central variation field.  No sign claim for the index form is
made without a minimizing or no-conjugate-point hypothesis.

## Verification and frontier

Focused verification passes without warnings, and the module's exported
artifact refresh also passes.  The file contains no `sorry`, `admit`, new
axiom, or reference-tree dependency.

The next exact theorem is `lRegJacobi_unique` in `Jacobi.lean`.  Once
regularized Jacobi initial data are unique, the next L4 declarations can define
L-conjugacy through singularity of the initial-tangent differential of `lExp`
and prove index positivity before the first conjugate point.  That is a new L4
substage, not an unverified part of `lLength_second_var`.

Honest progress at this point: `redVolume_anti` remains unstated and unproved
(0%); `lLength_second_var` is proved (100%); the broader L4 phase is about
70--75%; dedicated L-geometry machinery is about 48--52%; reusable generic
prerequisites are about 88--92%.  P2 as a whole remains below 1%, and the whole
Poincare program remains about 3--5%.
