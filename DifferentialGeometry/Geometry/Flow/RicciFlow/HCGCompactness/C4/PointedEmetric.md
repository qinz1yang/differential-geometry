# PointedEmetric.lean

`PointedRiemannianManifold.emetricSpace` remains the canonical packaged
Riemannian emetric for a stored smooth metric.

This pass added reusable projections for the same stored-metric instance
package:

- `PointedRiemannianManifold.riemBundle`;
- `PointedRiemannianManifold.riemInner`;
- `PointedRiemannianManifold.riemBundle_cont`.

These projections are intentionally built in the pointed-emetric layer, where
the model-space inner product is not active as a competing tangent-fiber
instance. Downstream Hopf--Rinow consumers should bind them with unannotated
`letI` declarations so Lean preserves their exact instance types.

Verification passed after marking the class-valued projections reducible.
