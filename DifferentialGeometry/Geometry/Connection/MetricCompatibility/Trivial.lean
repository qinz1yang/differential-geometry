import DifferentialGeometry.Geometry.Connection.Trivial
import Mathlib.Geometry.Manifold.VectorBundle.CovariantDerivative.Metric

open Bundle
open scoped Manifold ContDiff

namespace CovariantDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  (M : Type*) [TopologicalSpace M] [ChartedSpace H M]
  (F : Type*) [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

theorem trivial_isMetricCompatible : (trivial I M F).IsMetricCompatible := by
  unfold IsMetricCompatible
  funext x
  ext v w X
  rw [derivMetricTensor_apply_eq_extend]
  have hext (a : F) : FiberBundle.extend (E := Bundle.Trivial M F) F (x := x) a = fun _ => a := by
    funext y
    simp [FiberBundle.extend]
  simp only [trivial_apply, hext, mvfderiv_const, Pi.zero_apply, zero_apply,
    inner_zero_left, inner_zero_right, sub_zero]
  change mvfderiv I (fun _ : M => inner ℝ v w) x X = 0
  rw [mvfderiv_const, zero_apply]

end CovariantDerivative
