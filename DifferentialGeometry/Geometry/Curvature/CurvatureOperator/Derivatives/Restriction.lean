import DifferentialGeometry.Geometry.Connection.TensorNabla.Naturality.MetricRestriction
import DifferentialGeometry.Geometry.Curvature.Naturality.OpenRestriction
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Derivatives.Norm
import DifferentialGeometry.Geometry.Metric.TensorInner.Tensor0S.Restriction

set_option autoImplicit false
noncomputable section
open Bundle Set Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

open Geometry.Curvature DifferentialGeometry.Tensor0SBundle

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

local instance : CompleteSpace E := FiniteDimensional.complete ℝ E
local instance : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)
local instance : IsManifold I 2 M := IsManifold.of_le (n := ∞) (by decide)

theorem curvCovDeriv_restrictOpen (g : SmoothRiemannianMetric I M)
    (U : TopologicalSpace.Opens M) (k : ℕ) (x : U)
    (slots : Fin (k + 4) → TangentSpace I x) :
    curvCovDeriv (g.restrictOpen U) k x slots = curvCovDeriv g k (x : M) slots := by
  induction k generalizing x with
  | zero =>
    change metricRm04 (g.restrictOpen U) x slots = metricRm04 g (x : M) slots
    rw [metricRm04_apply, metricRm04_apply]
    have hvec : vec4 (slots 0) (slots 1) (slots 2) (slots 3) = slots := by
      ext i
      fin_cases i <;> rfl
    have h := metricRm04StandardAt_restrictOpen g U x (slots 0) (slots 1) (slots 2) (slots 3)
    simp only [metricRm04StandardAt_apply, mfderiv_subtype_val_apply] at h
    rw [hvec] at h
    exact h
  | succ k ih =>
    change totalNabla0SFun (k + 4) (metricCov (g.restrictOpen U))
        (curvCovDeriv (g.restrictOpen U) k) x slots =
      totalNabla0SFun (k + 4) (metricCov g) (curvCovDeriv g k) (x : M) slots
    have hA : curvCovDeriv (g.restrictOpen U) k =
        restrictOpen0S (k + 4) (curvCovDeriv g k) := by
      ext y v
      exact ih y v
    rw [hA, totalNabla0SFun_metricCov_restrictOpen]
    rfl

theorem curvDerivNorm_restrictOpen (g : SmoothRiemannianMetric I M)
    (U : TopologicalSpace.Opens M) (k : ℕ) (x : U) :
    curvDerivNorm k (g.restrictOpen U) x = curvDerivNorm k g (x : M) := by
  have h : curvCovDeriv (g.restrictOpen U) k x = curvCovDeriv g k (x : M) := by
    ext slots
    exact curvCovDeriv_restrictOpen g U k x slots
  unfold curvDerivNorm curvDerivNormSq
  rw [normSq0S_restrictOpen_apply, h]

end DifferentialGeometry.CheegerGromovCompactness
