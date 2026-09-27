import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Norm
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Algebra

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem curvStep_eq_covStep
    (g : SmoothRiemannianMetric I M) (a : Nat)
    (A : Tensor0SField (𝕜 := Real) (E := E) (H := H)
      (I := I) (M := M) (n := (∞ : WithTop ℕ∞)) (a + 4)) :
    curvCovDerivStep (I := I) g a A =
      covStep (I := I) g (a + 4) A := by
  refine DFunLike.ext _ _ (fun x => ?_)
  rw [covStep_apply]
  rfl

end DifferentialGeometry.CheegerGromovCompactness
