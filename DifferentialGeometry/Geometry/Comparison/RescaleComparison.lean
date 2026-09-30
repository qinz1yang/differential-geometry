import DifferentialGeometry.Geometry.Comparison.AngleShortening
import DifferentialGeometry.Geometry.Metric.Scaling.RescaleGeometry

set_option autoImplicit false

open Set Metric Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem fourPointComparison_rescale_sqrt_iff
    {X : Type*} [m : MetricSpace X] {κ : ℝ} (hκ : 0 < κ) (Ω : Set X) :
    @fourPointComparison X (m.rescale (sqrt κ) (sqrt_pos.mpr hκ)) 1 Ω ↔
      fourPointComparison κ Ω := by
  constructor <;> intro h x hx a ha b hb c hc hax hbx hcx
  · have ht := h x hx a ha b hb c hc hax hbx hcx
    simpa only [MetricSpace.rescale_dist,
      ← comparisonAngleNegCurvature_eq_one_sqrt_mul hκ.ne'] using ht
  · have ht := h x hx a ha b hb c hc hax hbx hcx
    simpa only [MetricSpace.rescale_dist,
      ← comparisonAngleNegCurvature_eq_one_sqrt_mul hκ.ne'] using ht

theorem local_fourPointComparison_rescale_sqrt_iff
    {X : Type*} [m : MetricSpace X] {κ : ℝ} (hκ : 0 < κ) (p : X) :
    (∃ Ω : Set X,
      @IsOpen X (m.rescale (sqrt κ) (sqrt_pos.mpr hκ)).toUniformSpace.toTopologicalSpace Ω ∧
      @fourPointComparison X (m.rescale (sqrt κ) (sqrt_pos.mpr hκ)) 1 Ω ∧ p ∈ Ω) ↔
      ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison κ Ω ∧ p ∈ Ω := by
  constructor
  · rintro ⟨Ω, hΩ, hcomp, hp⟩
    exact ⟨Ω, hΩ, (fourPointComparison_rescale_sqrt_iff hκ Ω).mp hcomp, hp⟩
  · rintro ⟨Ω, hΩ, hcomp, hp⟩
    exact ⟨Ω, hΩ, (fourPointComparison_rescale_sqrt_iff hκ Ω).mpr hcomp, hp⟩

end DifferentialGeometry.Geometry.Comparison.Toponogov
