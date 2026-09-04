import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurck.LieCorrection.TameBounds
import DifferentialGeometry.Analysis.Spectral.Intrinsic.DeTurckCoefficients.LieCorrection.Zero.Splitting
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Geometry.Curvature

noncomputable section


open Bundle Manifold DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open LieCorrectionZeroCore
open DifferentialGeometry.Integral.L2

variable
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
      [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

omit [NeZero (Module.finrank ℝ E)] [I.Boundaryless] in
omit [SigmaCompactSpace M] in
theorem lieCorrectionZeroInsertion_eq_lieCorrectionZeroInsertionField
    (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    lieCorrectionZeroInsertion (I := I) (M := M) g₀ g₁ g_bg =
      lieCorrectionZeroInsertionField (I := I) (M := M) g₀ g₁ g_bg := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  apply Tensor0SSpace.toModel_injective
  apply ContinuousMultilinearMap.ext
  intro m
  exact (lieCorrectionZero_insert_fiber (I := I) (M := M) g₀ g₁ g_bg x D m).symm

omit [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem lieCorrectionZeroVectorBundle_eq_field (g₀ g₁ : SmoothRiemannianMetric I M) :
    lieCorrectionZeroVectorBundle (I := I) (M := M) g₀ g₁ =
      lieCorrectionZeroVectorBundleField (I := I) (M := M) g₀ g₁ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  change lieCorrectionZeroVBFib (I := I) g₀ g₁ x D = _
  exact (lieCorrectionZero_vb_fiber (I := I) (M := M) g₀ g₁ x D).symm

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem lieCorrectionZeroMixedConnection_eq_lieCorrectionZeroMixedConnectionField (g₀ g₁ g_bg : SmoothRiemannianMetric I M) :
    lieCorrectionZeroMixedConnection (I := I) (M := M) g₀ g₁ g_bg =
      lieCorrectionZeroMixedConnectionField (I := I) (M := M) g₀ g₁ g_bg := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  change lieCorrectionZeroMixedConnectionFib (I := I) g₀ g₁ g_bg x D = _
  exact (lieCorrectionZero_amix_fiber (I := I) (M := M) g₀ g₁ g_bg x D).symm

omit [NeZero (Module.finrank ℝ E)] [SigmaCompactSpace M] in
omit [I.Boundaryless] in
theorem lieCorrectionZeroRiemann_eq_field (g₀ g₁ : SmoothRiemannianMetric I M) :
    lieCorrectionZeroRiemann (I := I) (M := M) g₀ g₁ =
      lieCorrectionZeroRiemannField (I := I) (M := M) g₀ g₁ := by
  apply SmoothCcTensor.ext
  apply ContMDiffSection.ext
  intro x
  apply ContinuousLinearMap.ext
  intro D
  change TensorRSSpace.ofCLM (lieCorrectionZeroRiemFib (I := I) g₀ g₁ x) D = _
  exact (lieCorrectionZero_riem_fiber (I := I) (M := M) g₀ g₁ x D).symm

end DifferentialGeometry.Analysis.Spectral

end
