import DifferentialGeometry.Geometry.Geodesic.Equation.Basic

open scoped Manifold BigOperators ContDiff

namespace DifferentialGeometry.Geometry.Connection

open Riemannian.Geodesic
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Tensor.Coordinates

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem norm_chartChristoffelContraction_le
    (g : SmoothRiemannianMetric I M) (p : M) (x u v : E) {C : ℝ}
    (hC : 0 ≤ C) (hΓ : ∀ i j k, ‖chartChristoffel g p i j k x‖ ≤ C) :
    ‖chartChristoffelContraction g p u v x‖ ≤
      (C * (∑ i, ‖((chartModelBasis E).coord i).toContinuousLinearMap‖) ^ 2 *
        (∑ k, ‖chartModelBasis E k‖)) * ‖u‖ * ‖v‖ := by
  classical
  let b := chartModelBasis E
  let c := fun i => ‖(b.coord i).toContinuousLinearMap‖
  have hc (i) (w : E) : ‖chartCoord (E := E) i w‖ ≤ c i * ‖w‖ :=
    ((b.coord i).toContinuousLinearMap).le_opNorm w
  have hterm (i j k) : ‖chartChristoffel g p i j k x * chartCoord i u * chartCoord j v‖ ≤
      C * (c i * ‖u‖) * (c j * ‖v‖) := by
    rw [norm_mul, norm_mul]
    exact mul_le_mul (mul_le_mul (hΓ i j k) (hc i u) (norm_nonneg _) hC)
      (hc j v) (norm_nonneg _) (mul_nonneg hC (mul_nonneg (norm_nonneg _) (norm_nonneg _)))
  calc
    ‖chartChristoffelContraction g p u v x‖ ≤
        ∑ k, (∑ i, ∑ j, C * (c i * ‖u‖) * (c j * ‖v‖)) * ‖b k‖ := by
      unfold chartChristoffelContraction
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro k _
      rw [norm_smul]
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      apply (norm_sum_le _ _).trans
      apply Finset.sum_le_sum
      intro i _
      exact (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => hterm i j k)
    _ = _ := by
      simp only [Finset.mul_sum, Finset.sum_mul, pow_two]
      simp only [← Finset.sum_mul, ← Finset.mul_sum]
      dsimp only [c, b]
      ring

end DifferentialGeometry.Geometry.Connection
