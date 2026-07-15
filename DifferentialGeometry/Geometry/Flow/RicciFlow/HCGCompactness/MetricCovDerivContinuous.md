# MetricCovDerivContinuous.lean — spatial continuity of `metricCovDerivNorm`

## Goal / role

Deliverable 1 of the P4 Brick-4 unblock: the MISSING analytic API that
`ConvFieldAssembly.lean`'s `hgLip`/`hbdd` head/mid indices need — continuity of
`z ↦ metricCovDerivNorm q h gRef z` and its compact-set boundedness corollary.

## Delivered (sorry-free, axiom-clean `[propext, Classical.choice, Quot.sound]`)

- `metricCovDerivNorm_continuousAt q h gRef z₀` — `ContinuousAt` at a base point.
- `metricCovDerivNorm_continuous q h gRef` — `Continuous` (from the local form).
- `metricCovDerivNorm_bddAbove_of_isCompact q h gRef hK` — `BddAbove (… '' K)`.
- `metricCovDerivNorm_le_of_isCompact q h gRef hK` — `∃ C, ∀ z ∈ K, … ≤ C`
  (the shape `hbdd` consumes directly).

## Route (worked first try, only fix = `rfl` for the finrank card)

Continuity is LOCAL. Near `z₀`, use the smooth `gRef`-orthonormal frame
`smoothOrthoFrame gRef z₀` (from
`Geometry/Curvature/CurvatureOperator/RicciIdentitySmoothFrame.lean`). On the
open nbhd `smoothOrthoFrameNbhd z₀` (in `𝓝 z₀`, contains `z₀`) the frame is
`gRef`-orthonormal, so `normSq0S` (frame-independent) equals the finite sum of
squared frame components via `normSq0S_identity_eq_sum_sq`
(`Tensor0SRiemannian/Comparison.lean`). The `MetricInverseInBasis_gen` hypothesis
comes from `metricInverseInBasis_of_orthonormal` (`Curvature/Components/RicciTrace.lean`)
+ `identityInvMetric`/`diagonalInvMetric` simp, exactly as in
`MetricDerivNormRestrict.normSq0S_restrictOpen_apply`.

Each component `z ↦ (∇^q h z)(fun a => frame (slots a) z)` is smooth (hence
continuous) via `tensor0SField_eval_smooth_slots_contMDiffAt`
(`NablaOnTensors/Regularity/Tensor0S.lean`): `metricCovDeriv h gRef q` is a
`Tensor0SField (q+2)` (`PointedConvergence.lean`), and the frame vectors are
smooth `ContMDiffSection`s (`orthoFrameSection` = `ContMDiffSection.mk` of
`smoothOrthoFrame` + `smoothOrthoFrame_smooth`). `component0S basis A slots =
A (fun a => basis (slots a))` (`Coordinates/CoordinateBasis.lean`) closes the
rewrite. Finite `∑` of `·²` is continuous (`continuous_finset_sum` + `.pow`);
`Real.continuous_sqrt` finishes. `ContinuousAt→Continuous` via
`continuous_iff_continuousAt`, gluing the local nbhd forms with `.congr`.

## Reused infra (no new frontier)

- `smoothOrthoFrame` / `_smooth` / `_orthonormal` / `smoothOrthoFrameNbhd` /
  `_mem_nhds` / `mem_..._self` — `RicciIdentitySmoothFrame.lean`.
- `normSq0S_identity_eq_sum_sq`, `component0S_apply`,
  `metricInverseInBasis_of_orthonormal` — as in `normSq0S_restrictOpen_apply`.
- Private `orthoFrameBasis` / `orthoFrameSection` reproduce the `smoothOrthoBasis`
  packaging pattern from `Connection/MetricCompatibility/TensorMetricCompatible.lean`
  (those are `private` there, so the small `basisOfLinearIndependentOfCardEqFinrank`
  + inline `linearIndependent_of_orthonormal` are copied here).

## Typeclasses

Needs `[InnerProductSpace ℝ E]` + `[NeZero (Module.finrank ℝ E)]` +
`[BoundarylessManifold I M]` (all held by `smoothOrthoFrame`).
`BoundarylessManifold I M` is a global instance from `[I.Boundaryless]`
(Mathlib `InteriorBoundary.lean:174`), so downstream `[I.Boundaryless]` files
(e.g. `ConvFieldAssembly.lean`) synthesize it automatically.

## Gotcha

`basisOfLinearIndependentOfCardEqFinrank` card goal is
`Fintype.card (Fin n) = Module.finrank ℝ (TangentSpace I y)`; after
`rw [Fintype.card_fin]` the residue `finrank ℝ E = finrank ℝ (TangentSpace I y)`
does NOT close by `rw` alone — needs a trailing `rfl` (`TangentSpace I y` is
defeq `E`). Same as `smoothOrthoBasis`.

Targeted build green (`+…MetricCovDerivContinuous`, 3803 jobs).
