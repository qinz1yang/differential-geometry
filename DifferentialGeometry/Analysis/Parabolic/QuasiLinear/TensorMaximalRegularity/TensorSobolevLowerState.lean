import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.TensorMaximalRegularity.DenseLowerState
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Inclusion

noncomputable section

open Bundle Manifold Set
open scoped Manifold Topology ContDiff ENNReal NNReal InnerProductSpace

namespace DifferentialGeometry.Analysis.Parabolic

open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.QuasiLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M]

def lowerStateRS (g₀ : SmoothRiemannianMetric I M) (r s a : ℕ) (R : ℝ) :
    Set (TensorHs (I := I) (M := M) g₀ r s ((a : ℝ) + 2)) :=
  lowerBall (tensorHsInclusion (I := I) (M := M) (g := g₀) (r := r) (s := s)
    (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith)) R

theorem zero_mem_lowerRS (g₀ : SmoothRiemannianMetric I M) (r s a : ℕ)
    {R : ℝ} (hR : 0 ≤ R) :
    (0 : TensorHs (I := I) (M := M) g₀ r s ((a : ℝ) + 2)) ∈
      lowerStateRS (I := I) (M := M) g₀ r s a R := by
  change
    ‖tensorHsInclusion (I := I) (M := M) (g := g₀) (r := r) (s := s)
        (show (a : ℝ) + 1 ≤ (a : ℝ) + 2 by linarith)
        (0 : TensorHs (I := I) (M := M) g₀ r s ((a : ℝ) + 2))‖ ≤ R
  simpa only [map_zero, norm_zero] using hR

end DifferentialGeometry.Analysis.Parabolic

end
