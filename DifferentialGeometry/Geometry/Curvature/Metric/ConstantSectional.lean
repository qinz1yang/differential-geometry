import DifferentialGeometry.Geometry.Curvature.Metric.Conditions
import DifferentialGeometry.Geometry.Curvature.Algebraic.TensorMetric
import DifferentialGeometry.Geometry.Curvature.Riemann.SectionalCurvature

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [T2Space M]

omit [FiniteDimensional ℝ E] [T2Space M] in
private theorem sectionalCurvatureDenominator_eq_zero_of_not_linearIndependent
    (g : SmoothRiemannianMetric I M) (x : M)
    (v w : TangentSpace I x) (hdep : ¬ LinearIndependent ℝ ![v, w]) :
    g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2 = 0 := by
  have hnonneg : 0 ≤ g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2 := by
    simpa only [Riemannian.sectionalCurvatureDenominator_def]
      using Riemannian.sectionalCurvatureDenominator_nonneg g x v w
  have hnotpos : ¬ 0 < g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2 := by
    intro hpos
    exact hdep (Riemannian.linearIndependent_pair_of_sectionalCurvatureDenominator_pos
      g x v w (by
        simpa only [Riemannian.sectionalCurvatureDenominator_def] using hpos))
  exact le_antisymm (le_of_not_gt hnotpos) hnonneg

theorem constantPositiveSectionalCurvatureMetric_iff [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) :
    constantPositiveSectionalCurvatureMetric g ↔
      ∃ c : ℝ, 0 < c ∧ ∀ x (v w : TangentSpace I x),
        LinearIndependent ℝ ![v, w] → Riemannian.sectionalCurvature g x v w = c := by
  constructor
  · rintro ⟨c, hc, hsec⟩
    refine ⟨c, hc, fun x v w hLI => ?_⟩
    have hden : 0 < g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2 := by
      simpa only [Riemannian.sectionalCurvatureDenominator_def]
        using Riemannian.sectionalCurvatureDenominator_pos_of_linearIndependent g x v w hLI
    rw [Riemannian.sectionalCurvature_eq_metricRm04StandardAt_div, hsec x v w]
    field_simp [ne_of_gt hden]
  · rintro ⟨c, hc, hsec⟩
    refine ⟨c, hc, fun x v w => ?_⟩
    by_cases hLI : LinearIndependent ℝ ![v, w]
    · have hden : 0 < g.inner x v v * g.inner x w w - (g.inner x v w) ^ 2 := by
        simpa only [Riemannian.sectionalCurvatureDenominator_def]
          using Riemannian.sectionalCurvatureDenominator_pos_of_linearIndependent g x v w hLI
      have hcurv := hsec x v w hLI
      rw [Riemannian.sectionalCurvature_eq_metricRm04StandardAt_div] at hcurv
      field_simp [ne_of_gt hden] at hcurv
      linarith
    · rw [Geometry.metricRm04StandardAt_eq_zero_of_not_linearIndependent g x v w hLI]
      have hden := sectionalCurvatureDenominator_eq_zero_of_not_linearIndependent g x v w hLI
      have hden' : g.inner x v v * g.inner x w w -
          g.inner x v w * g.inner x v w = 0 := by
        simpa only [pow_two] using hden
      rw [hden', mul_zero]

end DifferentialGeometry.Geometry.Curvature
