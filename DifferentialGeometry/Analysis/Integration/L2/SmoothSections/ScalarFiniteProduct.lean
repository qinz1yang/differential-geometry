import DifferentialGeometry.Analysis.Integration.L2.SmoothSections.ScalarNorm
import Mathlib.Analysis.Normed.Lp.PiLp

noncomputable section

open MeasureTheory
open scoped Manifold ContDiff

namespace DifferentialGeometry.Integral.L2.SmoothCcTensor

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {ι : Type*} [Fintype ι]

private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

theorem integral_norm_sq_scalar0_piLp
    (g : SmoothRiemannianMetric I M) (S : ι → SmoothCcTensor g 0 0) :
    (∫ x, ‖WithLp.toLp 2 (fun i => TensorRSField.scalar0 (S i).toSection x)‖ ^ 2
      ∂riemannianVolumeMeasure (I := I) (M := M) g) =
      ‖WithLp.toLp 2 S‖ ^ 2 := by
  simp_rw [PiLp.norm_sq_eq_of_L2, Real.norm_eq_abs, sq_abs]
  rw [integral_finsetSum _ (fun i _ => (memLp_scalar0 g (S i) 2).integrable_sq)]
  apply Finset.sum_congr rfl
  intro i _
  rw [← real_inner_self_eq_norm_sq, inner_eq_integral_scalar0_mul]
  simp only [pow_two]

end DifferentialGeometry.Integral.L2.SmoothCcTensor
