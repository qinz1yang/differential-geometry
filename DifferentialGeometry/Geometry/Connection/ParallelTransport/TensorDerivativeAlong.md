# Tensor derivative along a curve

## Purpose

This module supplies the generic product rule for evaluating a smooth
covariant tensor on moving tangent fields along a differentiable curve.  It is
the reusable connection-layer input needed by the Perelman L-Jacobi
calculation.

## Status

`tensor_eval_deriv` is implemented and focused verification passes without
warnings.  For a smooth covariant tensor `A`, a curve `γ` differentiable at
`t`, and moving tangent slots whose fixed-chart representatives are
differentiable at `t`, it proves

```text
d/dt A(V₁, ..., Vₛ)
  = (∇_{γ'} A)(V₁, ..., Vₛ)
    + Σᵢ A(V₁, ..., DₜVᵢ, ..., Vₛ).
```

The theorem uses `totalNabla0SFun` for the tensor derivative and
`covDerivAlong` for each moving slot.  The proof fully evaluates the tensor in
a fixed chart; it does not unfold bundle or Hom representations.

## Placement and reuse

A native-source search found model-space product rules and the special metric
compatibility formula, but no generic along-curve tensor-evaluation theorem.
The new theorem therefore lives in the connection/parallel-transport layer,
which already owns `covDerivAlong` and may import the tensor derivative API
without reversing the Tensor-to-Geometry dependency direction.

The immediate consumer is the Perelman L-Jacobi calculation: rank one gives
the derivative of `du(W)`, while rank two gives the three-term derivative of
`Ric(A, W)`.

## Project progress

This generic producer is complete.  It is reused infrastructure rather than
the Perelman endpoint itself: `redVolume_anti` remains unproved (0%), and the
dedicated L-geometry/Jacobi lane must still specialize and combine this rule
with its variation and curvature identities.
