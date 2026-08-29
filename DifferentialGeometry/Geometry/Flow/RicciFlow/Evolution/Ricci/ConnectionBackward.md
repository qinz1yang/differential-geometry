# Backward-time connection variation

## Implemented producer

`ConnectionBackward.lean` now exports `connBack_vec_sq`.  For the Ricci-flow
metric family `g(T-r^2)`, it proves differentiability at `s` of the chart
representation of

```text
(nabla^{g(T-r^2)} - nabla^{g(T-s^2)})_{A(r)} Y(r).
```

The theorem assumes only regularity of `T-s^2`, manifold differentiability of
the curve, and chart differentiability of the two moving tangent fields.  It
does not introduce a test vector or a stronger downstream regularity
assumption.

The proof first reconstructs the lowered connection-difference as a
continuous-multilinear model from a finite chart basis.  It then raises the
remaining lower slot with the smooth inverse chart Gram matrix.  All moving
tangent fields are fully evaluated before the reconstruction, so no equality
or differentiability assertion is made about a whole moving bundle or Hom
object.

## Verification and use

Focused verification and the exported-module refresh both pass without
warnings.  The source contains no `sorry`, `admit`, new axiom, or reference-tree
dependency.

`lJacobiVel_sq_diff` now consumes this producer to transfer frozen-metric
covariant-derivative regularity to the moving-metric L-Jacobi velocity after
square-root reparameterization.  That consumer and the resulting
`lExp_jacobi` endpoint are verified in `LGeometry/SecondVariation.lean`.
