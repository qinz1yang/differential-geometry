# CurvatureAction notes

## 2026-05-14: Slotwise curvature action layer

Worked:

- Added the invariant slot-map action `curvatureAction0SAtSlots`.
- Added the operator specialization `curvatureAction0SOperatorAt`, matching
  the formula `-Σ_i T(..., R(X,Y)V_i, ...)` when a pointwise curvature
  operator is available.
- Moved the `(0,s)` action-facing API out of `Tensor/RicciIdentity.lean`:
  `oneFormAtSlot0S`, `freezeSlot0SAt`, `curvatureAction0SAt`,
  `torsionCorrection0SAt`, and the pointwise Ricci-identity predicates.
- Added bridges from the existing `Rm13` pairing convention to the slot-map
  action and to the connection-curvature field replacement sum.

Verification passed.

Lesson:

- The slot-map action is the proof-safe intermediate for connection curvature,
  because `connectionRiemannCurvatureField` is field-level until a separate
  tensoriality theorem packages it as a pointwise operator.
