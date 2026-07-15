# GeometricInputs

## Source

This file records the MSM135 Chapter 4 black-box boundary for the compactness
proof: Cheeger--Gromov--Taylor injectivity-radius decay (`lbl384`), the
Bishop--Gromov bounded-overlap volume comparison remark after `lbl384`, and
Jacobi/Rauch derivative bounds for normal-coordinate transition maps
(`lbl-2103`).

## Definitions

- `PointedSeqDistance` records the per-term distance function used by the
  Chapter 4 estimates.  It is theorem-facing input because
  `PointedRiemannianManifold` does not currently store the emetric/vector-bundle
  instances needed to use `dist` globally.
- `NormalChartFor` and `normalTransitionMap` give the HCG-local vocabulary for
  the model-coordinate map `exp_y^{-1} o exp_x` built from `NormalChartData`.
  `NormalChartFor` explicitly carries the tangent vector-bundle instance needed
  by the normal-coordinate backend.
- `InjRadiusDecayInput` packages the CGT decay constants and the decay estimate,
  using the existing `BaseInjBound` field for the basepoint injectivity input.
- `VolumeComparisonInput` packages the bounded-overlap conclusion Step A needs.
- `ExpInverseDerivBoundInput` packages uniform derivative bounds for normal
  transition maps, consumed later by Steps B/C.

## Frontier

The hard geometry is intentionally still producer-side: none of these records
prove CGT, Bishop--Gromov, or Jacobi/Rauch comparison.  Later Chapter 4 phases
should consume these fields rather than re-deriving the deep theorems.

## Verification

Verification passed for the new module.  The local audit found no `sorry`,
`admit`, or `axiom` in this file.
