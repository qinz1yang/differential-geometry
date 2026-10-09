import DifferentialGeometry.Geometry.Curvature.Bounds.MetricDerivatives
import DifferentialGeometry.Geometry.Metric.BilinearPerturbation
import DifferentialGeometry.Geometry.Metric.DerivativeScaleENorm

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [T2Space M]

private local instance : CompleteSpace E := FiniteDimensional.complete ℝ E

theorem exists_pos_bound_intrinsic_curvature_derivative_of_metric_error
    (j : ℕ) (eps A : ℝ) (heps : eps < 1) :
    ∃ C > 0, ∀ (G g : SmoothRiemannianMetric I M) (x : M),
      (∀ s ≤ j + 2, metricDerivNorm s g G G x ≤ eps) →
      (∀ s ≤ j, Real.sqrt (normSq0S G x (4 + s)
        (iterCov G 4 (metricRm04 G) s x)) ≤ A) →
      Real.sqrt (normSq0S g x (4 + j)
        (iterCov g 4 (metricRm04 g) j x)) ≤ C := by
  let rho := max 0 eps
  have hrho : 0 ≤ rho := le_max_left _ _
  have hrho1 : rho < 1 := max_lt zero_lt_one heps
  have hden : 0 < 1 - rho := sub_pos.mpr hrho1
  let L := (1 - rho)⁻¹
  have hL : 1 ≤ L := by
    dsimp only [L]
    apply (le_inv_comm₀ zero_lt_one hden).mpr
    simpa only [inv_one] using sub_le_self (1 : ℝ) hrho
  have hupper : 1 + rho ≤ L := by
    dsimp only [L]
    rw [← one_div, le_div_iff₀ hden]
    nlinarith [sq_nonneg rho]
  let B := Real.sqrt (Module.finrank ℝ E : ℝ) + rho
  have hB : 0 ≤ B := add_nonneg (Real.sqrt_nonneg _) hrho
  obtain ⟨C, hC, hbound⟩ :=
    exists_pos_bound_intrinsic_curvature_derivative_of_metric_jets
      (I := I) (M := M) j L B (max 0 A) hL hB (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro G g x herror hreference
  have herr (s : ℕ) (hs : s ≤ j + 2) : metricDerivNorm s g G G x ≤ rho :=
    (herror s hs).trans (le_max_right _ _)
  have hequiv (v : TangentSpace I x) :
      L⁻¹ * G.inner x v v ≤ g.inner x v v ∧
        g.inner x v v ≤ L * G.inner x v v := by
    obtain ⟨hl, hu⟩ := inner_bounds_of_metricDerivNorm_le G g x (herr 0 (by omega)) v
    constructor
    · simpa only [L, inv_inv] using hl
    · exact hu.trans (mul_le_mul_of_nonneg_right hupper (metric_inner_self_nonneg G x v))
  have hjets (s : ℕ) (hs : s ≤ j + 2) : metricCovDerivNorm s g G x ≤ B := by
    have hself : metricCovDerivNorm s G G x ≤ Real.sqrt (Module.finrank ℝ E : ℝ) := by
      cases s with
      | zero => exact (metricCovDerivNorm_self_zero G x).le
      | succ s => rw [covNorm_self_succ]; exact Real.sqrt_nonneg _
    exact (covNorm_le_add s g G G x).trans (add_le_add hself (herr s hs))
  exact hbound G g x hequiv hjets
    (fun s hs => (hreference s hs).trans (le_max_right _ _))

end DifferentialGeometry.Geometry.Curvature
