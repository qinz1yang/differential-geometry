import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardScalarComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardActionComparison
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardScalarLower
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardLifetime
set_option autoImplicit false
noncomputable section
open Set Manifold TopologicalSpace DifferentialGeometry
open DifferentialGeometry.Tensor0SBundle DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff
namespace DifferentialGeometry.PDE.RicciFlow.StandardCap
open private E3 from DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.StandardSolution.StandardScalarComparison
theorem exists_uniform_scalar_lower_bound_of_standard_metric_close_on_opens
    (θ : ℝ) (hθ : 0 ≤ θ) (hθ1 : θ < 1) :
    ∃ ε : ℝ, 0 < ε ∧
      ∀ (U : Opens E3) (g : SmoothRiemannianMetric (𝓡 3) U)
        (S : StandardSolution) (t : ℝ), t ∈ Icc 0 θ → ∀ x : U,
        (∀ j ≤ 2, metricDerivNorm j g ((S.val.metric t).restrictOpen U)
          (metric.restrictOpen U) x ≤ ε) →
        1 / 2 ≤ metricScalarAt g x := by
  obtain ⟨ε,hε,hcomparison⟩ := exists_uniform_standard_metric_scalar_lower_comparison θ hθ hθ1
  refine ⟨ε,hε,?_⟩
  intro U g S t ht x hclose
  have hcompare := (hcomparison S U g t ht x hclose).2
  have hdom : t ∈ S.val.domain := by
    apply (mem_lifetimeInterval_carrier S.val.lifetime S.val.lifetime_pos t).mpr
    refine ⟨ht.1,?_⟩
    rw [S.lifetime_eq_one]
    exact ENNReal.ofReal_lt_one.mpr (ht.2.trans_lt hθ1)
  have hlower := S.val.one_le_scalar t hdom x.val
  rw [metricScalarAt_restrictOpen] at hcompare
  linarith

end DifferentialGeometry.PDE.RicciFlow.StandardCap
