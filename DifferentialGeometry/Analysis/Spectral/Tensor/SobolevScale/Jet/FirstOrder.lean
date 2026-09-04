import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Jet.IteratedCovariantDerivativeBound
import DifferentialGeometry.Analysis.Spectral.Tensor.SobolevScale.Jet.LaplacianIterateLadder

set_option autoImplicit false

noncomputable section

open DifferentialGeometry.Analysis.Sobolev
open DifferentialGeometry.Analysis.Spectral
open DifferentialGeometry.Analysis.Elliptic
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open Bundle Manifold MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal BigOperators

namespace DifferentialGeometry.Analysis.Spectral

open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Parabolic.TensorHeatEquation
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [CompactSpace M] [I.Boundaryless]
  [BoundarylessManifold I M] [T2Space M] [SigmaCompactSpace M]

private theorem cc_toHs_eq_smooth
    (g : SmoothRiemannianMetric I M) (σ : ℝ)
    (T : SmoothCcTensor g 0 2) :
    ccTensorToHs (I := I) (M := M) g 2 σ T =
      smoothCcToTensorHs (I := I) (M := M) g σ T := by
  refine TensorHs.ext ?_
  funext i
  simp only [ccTensorToHs_coeff, smoothCcToTensorHs_coeff]

theorem cc_h1_jet_sq
    (g : SmoothRiemannianMetric I M) (T : SmoothCcTensor g 0 2) :
    ‖ccTensorToHs (I := I) (M := M) g 2 (1 : ℝ) T‖ ^ 2 =
      ‖T‖ ^ 2 + ‖covGrad (I := I) (M := M) g 0 2 T‖ ^ 2 := by
  rw [cc_toHs_eq_smooth (I := I) (M := M) g (1 : ℝ) T]
  have h := smoothCcToTensorHs_odd_norm_sq_eq_toL2_iter_add_covGrad
    (I := I) (M := M) g 0 T
  simp only [oneMinusConnLapSmoothIter_zero, SmoothCcTensor.norm_toL2] at h
  have horder : (((2 * 0 + 1 : ℕ) : ℝ)) = (1 : ℝ) := by norm_num
  rw [horder] at h
  exact h

end DifferentialGeometry.Analysis.Spectral

end
