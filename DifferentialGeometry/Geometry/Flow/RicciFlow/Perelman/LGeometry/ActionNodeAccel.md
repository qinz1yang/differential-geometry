# ActionNodeAccel

## Status

`lFinNode_reg` is complete and focused verification passes without warnings.
It has no `sorry` or auxiliary frontier assumption.

## Result

For a strict finite chart-`H¹` realization of a global regularized L-action
minimizer, every internal subdivision node has all three pointwise properties
required by `IsLRegCurveOn`: the curve is manifold differentiable, its actual
velocity has a differentiable curve-point chart representation, and the
intrinsic regularized L-acceleration equation holds.

## Proof route

The proof first uses `lFinCurve_c1` to obtain one global `C¹` curve across all
nodes.  In the chart centered at a selected node it forms the actual phase from
the curve coordinate and the coordinate representation of `lVelocity`.  On
the two adjacent punctured pieces, `lStrict_piece_c2_at`,
`MFDerivAlongCurve.velocity_coord_diff`, and `lStrict_piece_accel` allow
`lRegCurve_phase` to identify the derivative of this phase with
`lPhaseField`.  Global `C¹` regularity makes the phase continuous at the node,
while `lPhaseField_smoothAt` makes the phase-field value continuous there.
`DifferentialGeometry.hasDerivAt_of_punct` then fills the missing node
derivative.  Finally `lPhase_accel` and germ congruence transfer the phase
equation back to the original curve and its actual velocity.

The shared interior-`C²` reconstruction now lives canonically in
`ActionStrictC2` as `lStrict_piece_c2_at`; the former private duplicate was
removed.  The refactored node module was rechecked and refreshed successfully.

The focused noncompact recheck also passed without warnings. `lFinNode_reg`
now exports without an ambient `CompactSpace M` instance; its downstream
refresh completed successfully, replaying only the unrelated pre-existing
`ActionNodeLocal` linter warning.

## Progress

- `lFinNode_reg`: 100%.
- Internal-node regularized-curve gate: 100%.
- Terminal `exists_lMinimizer`: 0%; this theorem is dedicated machinery only.
- `redVolume_anti`: 0%.
- Dedicated L-geometry machinery: approximately 98%.
- Generic reused infrastructure: 100% for this step.
- P2 remains below 1%; the whole Poincaré program remains approximately 3--5%.
