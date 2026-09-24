import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Covariant
import DifferentialGeometry.Geometry.Curvature.DimensionOne.Flat
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Algebra

noncomputable section

universe u uE uH

namespace DifferentialGeometry
namespace CheegerGromovCompactness

open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type u} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

omit [SigmaCompactSpace M] in
private theorem metricRm04_eq_zero_of_finrank_le_one (g : SmoothRiemannianMetric I M)
    (hE : Module.finrank ℝ E ≤ 1) :
    metricRm04 (I := I) (M := M) g = 0 := by
  refine DFunLike.ext _ _ (fun x => ?_)
  rw [metricRm04_apply]
  exact metricRm04At_eq_zero_of_finrank_le_one (I := I) g hE x

omit [SigmaCompactSpace M] in
theorem curvCovDeriv_eq_zero_of_finrank_le_one (g : SmoothRiemannianMetric I M)
    (hE : Module.finrank ℝ E ≤ 1) (k : ℕ) :
    curvCovDeriv (I := I) (M := M) g k = 0 := by
  induction k with
  | zero => exact metricRm04_eq_zero_of_finrank_le_one (I := I) g hE
  | succ k ih => rw [curvCovDeriv_succ, ih, curvStep_eq_covStep, covStep_zero]

omit [SigmaCompactSpace M] in
theorem curvDerivNorm_eq_zero_of_finrank_le_one (g : SmoothRiemannianMetric I M)
    (hE : Module.finrank ℝ E ≤ 1) (k : ℕ) (x : M) :
    curvDerivNorm (I := I) k g x = 0 := by
  rw [curvDerivNorm, curvDerivNormSq]
  have hcomp : curvCovDeriv (I := I) (M := M) g k x = 0 := by
    rw [curvCovDeriv_eq_zero_of_finrank_le_one (I := I) g hE k]
    rfl
  rw [hcomp, (Tensor0SBundle.normSq0S_eq_zero_iff (I := I) g x (k + 4) 0).mpr rfl,
    Real.sqrt_zero]

end CheegerGromovCompactness

end DifferentialGeometry
