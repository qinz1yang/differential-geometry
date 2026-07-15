# Operators.lean - scalar operator algebra

## 2026-06-23

Step C needed the finite-sum algebra behind the center-of-mass gradient
characterization. The reusable result belongs here, below the pointwise
`gradientFun` API, not in the HCG file.

What landed:

- `gradientFun_sum`: the gradient of a finite function sum is the finite sum of
  the gradients.
- `gradientFun_sum_smul`: the gradient of a finite weighted function sum is the
  weighted sum of the gradients.

The proof uses the native function-sum form `sum i in s, f i`, because
Mathlib's `MDifferentiableAt.sum` is stated in that form. Callers with
pointwise lambdas can bridge using `Finset.sum_apply`.

Verification status: focused Lean check and targeted module build passed. Axiom
print for `gradientFun_sum` and `gradientFun_sum_smul` is
`[propext, Classical.choice, Quot.sound]`; no `sorryAx` is introduced by these
declarations. The targeted build replayed existing upstream warnings outside
this file.

## 2026-06-24

Added `gradientFun_eq_zero_of_isLocalMin`: at a local minimum of a differentiable
scalar function on a boundaryless manifold, the realized gradient vanishes.

This theorem belongs in the lower scalar-operator API because
`Comparison/CenterOfMass.lean` needs the first-order gradient fact but should
not import the Laplacian minimum-principle file. The proof is the chart-level
first-order part of the existing Laplacian minimum route, packaged directly for
`gradientFun`.

Verification status: focused Lean check and targeted module build passed.
Axiom print for `gradientFun_eq_zero_of_isLocalMin` is
`[propext, Classical.choice, Quot.sound]`; no `sorryAx` is introduced by this
declaration.

Added `gradientFun_eq_of_flat`: if `(mfderiv f x).toLinearMap` is the
metric-flat covector of a tangent vector `v`, then the realized gradient is
`v`. This is the pure musical-map bridge needed by Step C so the remaining
distance-squared first-variation theorem can be stated as a covector identity,
not as a gradient identity.

Verification status: focused Lean check and targeted module build passed.
Axiom print for `gradientFun_eq_of_flat` is
`[propext, Classical.choice, Quot.sound]`; no `sorryAx` is introduced by this
declaration.
