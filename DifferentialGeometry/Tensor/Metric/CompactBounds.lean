import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Algebra
import DifferentialGeometry.Geometry.Connection.MetricTrace.Connection

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Tensor.RSTensor DifferentialGeometry.CheegerGromovCompactness
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Tensor

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

theorem exists_pos_bound_norm_on_compact (g : SmoothRiemannianMetric I M) {r : ℕ}
    (A : Tensor0SField (I := I) (M := M) ∞ r) {K : Set M} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K, Real.sqrt (normSq0S g x r (A x)) ≤ C := by
  have hc : Continuous (fun x : M => Real.sqrt (normSq0S g x r (A x))) :=
    Real.continuous_sqrt.comp (normSq0S_smooth g A).continuous
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max 1 C, zero_lt_one.trans_le (le_max_left _ _), fun x hx => ?_⟩
  have hxC := hC x hx
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)] at hxC
  exact hxC.trans (le_max_right _ _)

theorem exists_pos_bound_iterCov_on_compact [CompleteSpace E] [T2Space M]
    (g : SmoothRiemannianMetric I M) {r : ℕ}
    (A : Tensor0SField (I := I) (M := M) ∞ r) (k : ℕ) {K : Set M} (hK : IsCompact K) :
    ∃ C : ℝ, 0 < C ∧ ∀ x ∈ K,
      Real.sqrt (normSq0S g x (r + k) (iterCov g r A k x)) ≤ C :=
  exists_pos_bound_norm_on_compact g (iterCov g r A k) hK

end DifferentialGeometry.Geometry.Tensor
