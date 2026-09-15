import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Embedding.SmoothCompactSupportDense

section

open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [T2Space M] [SigmaCompactSpace M]

theorem tensorHsInclusion_ccTensorToHs (g : SmoothRiemannianMetric I M)
    (s : ℕ) {τ σ : ℝ} (h : τ ≤ σ) (S : SmoothCcTensor g 0 s) :
    tensorHsInclusion h (ccTensorToHs (I := I) (M := M) g s σ S) =
      ccTensorToHs (I := I) (M := M) g s τ S := by
  ext i
  rw [tensorHsInclusion_coeff_apply, ccTensorToHs_coeff, ccTensorToHs_coeff]

end DifferentialGeometry.Analysis.Spectral

end
