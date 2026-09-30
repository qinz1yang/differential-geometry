import DifferentialGeometry.Geometry.Metric.Approximation.BoundedFactorRestriction
import DifferentialGeometry.Geometry.Metric.Approximation.NonslimEndpointRecognition
import DifferentialGeometry.Topology.MetricSpace.SegmentCurves

set_option autoImplicit false
open Set Metric
open DifferentialGeometry.Geometry.Comparison.Toponogov
namespace GC.MetricGeometry

universe u v w

theorem exists_nearby_endpoint_of_no_bounded_factor
    {X : Type u} {Z : Type v} {Y : Type w}
    [MetricSpace X] [MetricSpace Z] [MetricSpace Y] [CompleteSpace Y]
    {p : X} {z : Z} {y : Y} {β η e β₂ Δ : ℝ}
    (F : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), z)) β)
    (G : KleinerLottApprox z y η)
    (H : KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), y)) e)
    (hsegments : ∀ a b : X, ∃ γ : Icc (0 : ℝ) 1 → X,
      γ ⟨0, by norm_num⟩ = a ∧ γ ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (γ s) (γ t) = dist a b * dist s t)
    (hYsegments : ∀ a b : Y, ∃ γ : Icc (0 : ℝ) 1 → Y, Continuous γ ∧
      γ ⟨0, by norm_num⟩ = a ∧ γ ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (γ s) (γ t) = dist a b * dist s t)
    (hcomp : fourPointComparison 0 (univ : Set Y)) (hdim : dimH (univ : Set Y) ≤ 1)
    (hβ₂ : 0 < β₂) (hβ₂small : β₂ < 1 / 100) (hΔ : 100 / β₂ < Δ)
    (he : e < β₂ / 100) (hη : 900 * Δ < η⁻¹)
    (hnoplane : ¬ Nonempty (KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), (0 : ℝ))) β₂))
    (hnobounded : ∀ (A : Type v) [MetricSpace A] (a : A),
      Bornology.IsBounded (univ : Set A) → diam (univ : Set A) < 1000 * Δ →
        ¬ Nonempty (KleinerLottApprox p (WithLp.toLp 2 ((0 : ℝ), a)) β)) :
    (∃ C : ℝ, 500 * Δ < C ∧ ∃ f : Y ≃ᵢ Icc (0 : ℝ) C, (f y).val < Δ / 2) ∨
      (∃ f : Y ≃ᵢ Ici (0 : ℝ), (f y).val < Δ / 2) := by
  have hΔone : 1 ≤ Δ := by
    have hh : 100 < 100 / β₂ := (lt_div_iff₀ hβ₂).mpr (by linarith)
    linarith
  have hlarge : ∃ a b : Y, 500 * Δ < dist a b := by
    by_contra! hbound
    have hY : Bornology.IsBounded (univ : Set Y) :=
      Metric.isBounded_iff.mpr ⟨500 * Δ, fun a _ b _ => hbound a b⟩
    have hdiam : diam (univ : Set Y) ≤ 500 * Δ :=
      diam_le_of_forall_dist_le_of_nonempty ⟨y, mem_univ y⟩ (fun a _ b _ => hbound a b)
    obtain ⟨f, _, _, hb, hd⟩ :=
      exists_factor_approximation_of_bounded_target F G hsegments hY hdiam hΔone hη
    exact hnobounded (ball z (600 * Δ)) ⟨z, mem_ball_self (by linarith)⟩ hb hd ⟨f⟩
  exact exists_nearby_endpoint_of_no_plane_approximation H hβ₂ hβ₂small hΔ he hnoplane
    (arbitrarily_short_curves_of_metric_segments hYsegments) hcomp hdim hlarge

end GC.MetricGeometry
