import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Scalar.ContinuousMultiplier
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.SmoothInclusion
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Parametric.Application

open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [I.Boundaryless] [T2Space M] [SigmaCompactSpace M] [CompactSpace M]

theorem tensorHsInclusion_appHs_scalarCc_zero
    (g : SmoothRiemannianMetric I M) (a : C^∞⟮I, M; ℝ⟯)
    (u : TensorHs g 0 0 ((0 : ℕ) : ℝ)) :
    let J := tensorHsInclusion (g := g) (r := 0) (s := 0)
      (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))
    J (appHs g 0 0 0 (scalarCc g a) u) =
      scalarH0ContinuousMul g ⟨a, a.2.continuous⟩ (J u) := by
  intro J
  refine (ccToHsLin_dense g 0 (by norm_num : (0 : ℝ) ≤ ((0 : ℕ) : ℝ))).induction_on u ?_ ?_
  · exact isClosed_eq (J.continuous.comp (appHs g 0 0 0 (scalarCc g a)).continuous)
      ((scalarH0ContinuousMul g ⟨a, a.2.continuous⟩).continuous.comp J.continuous)
  intro S
  simp only [ccToHsLin_apply, J, appHs_apply_ccTensorToHs, app_scalarCc,
    tensorHsInclusion_ccTensorToHs, scalarH0ContinuousMul_ccTensorToHs]

end DifferentialGeometry.Analysis.Spectral
