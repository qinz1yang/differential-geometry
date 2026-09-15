import DifferentialGeometry.Analysis.Spectral.Intrinsic.Garding.Scalar.RankZeroRealization
import DifferentialGeometry.Analysis.Sobolev.TensorHilbert.OperatorField.Parametric.ScalarSmulJet
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.SmoothInclusion

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Analysis.Parabolic.MaximalRegularity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
theorem rawTensorConnLapSmooth_scalarCc_const (g : SmoothRiemannianMetric I M) (c : ℝ) :
    rawTensorConnLapSmooth g 0 0 (scalarCc g ⟨fun _ => c, contMDiff_const⟩) = 0 := by
  let zeta : C^∞⟮I, M; ℝ⟯ := ⟨fun _ => c, contMDiff_const⟩
  let S := scalarCc g zeta
  change rawTensorConnLapSmooth g 0 0 S = 0
  apply SmoothCcTensor.ext
  rw [← TensorRSField.lift_scalar0 (rawTensorConnLapSmooth g 0 0 S).toSection,
    ← TensorRSField.lift_scalar0 (0 : SmoothCcTensor g 0 0).toSection]
  congr 2
  funext x
  rw [rawLap_cc_scalar,
    ← laplacian_levi_eq g (TensorRSField.scalar0_smooth S.toSection)]
  rw [show TensorRSField.scalar0 S.toSection = (fun _ => c) from scalar0_scalarCc g zeta]
  rw [laplacian_const, SmoothCcTensor.toSection_zero, TensorRSField.scalar0_zero]
  rfl

theorem tensorScaleLaplacian_ccTensorToHs_scalarCc_const
    (g : SmoothRiemannianMetric I M) (m c : ℝ) :
    tensorScaleLaplacian (g := g) (r := 0) (s := 0) m
      (ccTensorToHs g 0 (m + 2) (scalarCc g ⟨fun _ => c, contMDiff_const⟩)) = 0 := by
  rw [tensorScaleLaplacian_apply_ccTensorToHs, rawTensorConnLapSmooth_scalarCc_const,
    ← ccToHsLin_apply]
  exact map_zero _

end DifferentialGeometry.Analysis.Spectral
end
