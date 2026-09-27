import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Jet.Bounds.IteratedCovariantDerivative

noncomputable section
open scoped Manifold ContDiff

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [BoundarylessManifold I M]
  [T2Space M]

theorem ccTensorToHs_add_two_norm_eq_oneMinusConnLap (g : SmoothRiemannianMetric I M)
    (s : ℕ) (σ : ℝ) (S : SmoothCcTensor g 0 s) :
    ‖ccTensorToHs g s (σ + 2) S‖ =
      ‖ccTensorToHs g s σ (oneMinusConnLapSmooth g 0 s S)‖ := by
  have hsq : ‖ccTensorToHs g s (σ + 2) S‖ ^ 2 =
      ‖ccTensorToHs g s σ (oneMinusConnLapSmooth g 0 s S)‖ ^ 2 := by
    rw [ccToHs_norm_sq, ccToHs_norm_sq]
    apply tsum_congr
    intro i
    rw [oneMinus_coeff]
    unfold tensorSobolevWeight
    rw [Real.rpow_add (lt_of_lt_of_le zero_lt_one (one_le_one_add_lambda i)), Real.rpow_two]
    ring
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

end DifferentialGeometry.Analysis.Spectral
