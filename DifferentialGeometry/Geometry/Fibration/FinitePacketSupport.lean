import DifferentialGeometry.Geometry.Metric.Approximation.PaddedStripBoundary
import DifferentialGeometry.Geometry.Metric.WeakEdgeLocalization
import DifferentialGeometry.Analysis.Calculus.FixedJointCutoffNetwork
import DifferentialGeometry.Geometry.Metric.SupportScalePacking
import DifferentialGeometry.Geometry.Metric.SupportDomainBuffer
import DifferentialGeometry.Geometry.Metric.RadialSupportBuffer
import Mathlib.Data.Set.Card

set_option autoImplicit false

noncomputable section

open Set Metric
open scoped Topology

namespace DifferentialGeometry.Geometry.Fibration

variable {X : Type*} [PseudoMetricSpace X]

/-- Actual support scale, original-domain inclusion and its complement-distance margin. -/
theorem finite_packet_support_scale_buffer {ρ : X → ℝ} {Λ : NNReal}
    (hρ : LipschitzWith Λ ρ) {p z : X} (hp : 0 < ρ p) (hz : 0 < ρ z)
    {L C b : ℝ} (hL : 0 < L) (hC : 0 ≤ C)
    (hbudget : Λ * max L C ≤ 1 / 4) (hgap : 4 * L < b - C)
    {S U : Set X} (hS : S ⊆ closedBall z (C * ρ z))
    (hU : ball z (b * ρ z) ⊆ U) (hmeet : (S ∩ ball p (L * ρ p)).Nonempty) :
    ρ z / ρ p ∈ Icc (1 / 2) 2 ∧ dist z p ≤ (L + 2 * C) * ρ p ∧
      ball p (L * ρ p) ⊆ ball z ((C + 4 * L) * ρ z) ∧
      ball z ((C + 4 * L) * ρ z) ⊆ U ∧
      ∀ x ∈ ball p (L * ρ p), Uᶜ.Nonempty →
        (b - C - 4 * L) * ρ z ≤ infDist x Uᶜ := by
  obtain ⟨hratio, hdist⟩ := GC.MetricGeometry.scale_ratio_of_support_meeting hρ hp hz
    hC hbudget (hmeet.mono (inter_subset_inter_left _ hS))
  obtain ⟨hball, hdomain, hmargin⟩ := GC.MetricGeometry.support_meeting_ball_buffer hp hz hL
    hratio.1 hgap hS hU hmeet
  exact ⟨hratio, hdist, hball, hdomain, hmargin⟩

/-- The same radial supports have at most one active zero block and a genuine shell buffer. -/
theorem finite_packet_zero_shells {ι : Type*} {ρ : X → ℝ} {Λ : NNReal}
    (hρ : LipschitzWith Λ ρ) (hpos : ∀ x, 0 < ρ x)
    (z : ι → X) (R : ι → ℝ) (S : ι → Set X) (η : ι → X → ℝ)
    {p : X} {L T e : ℝ} (hL : 0 < L) (hΛ : L * Λ ≤ 1 / 4)
    (hT : 1600 * L ≤ T) (hR : ∀ j, T * ρ (z j) ≤ R j) (he : e < 1 / 40)
    (hlocal : ∀ j q, dist (z j) q ≤ 10 * R j → T / 20 ≤ R j / ρ q)
    (herror : ∀ j x, x ∈ S j → |η j x - dist (z j) x / R j| < e)
    (hvalue : ∀ j x, x ∈ S j → η j x ∈ Icc (1 / 5) (9 / 10))
    (hdisjoint : Pairwise fun j k => Disjoint (ball (z j) (R j)) (ball (z k) (R k))) :
    {j | (S j ∩ ball p (L * ρ p)).Nonempty}.Subsingleton ∧
      ∀ j, (S j ∩ ball p (L * ρ p)).Nonempty →
        T / 20 ≤ R j / ρ p ∧
        ∀ x ∈ ball p (L * ρ p), dist (z j) x / R j ∈ Icc (3 / 20) (19 / 20) := by
  have hT0 : 0 < T := by linarith
  have hR0 (j : ι) : 0 < R j := (mul_pos hT0 (hpos (z j))).trans_le (hR j)
  have hsupport (j : ι) : S j ⊆ closedBall (z j) ((37 / 40) * R j) := by
    intro x hx
    have ha := (abs_lt.mp (herror j x hx)).1
    have hb := (hvalue j x hx).2
    rw [mem_closedBall, dist_comm]
    apply ((div_lt_iff₀ (hR0 j)).mp (show dist (z j) x / R j < 37 / 40 by linarith)).le
  refine ⟨GC.MetricGeometry.subsingleton_zero_supports_meeting_ball hρ hpos z R S hL
    (θ := 37 / 40) (by norm_num) hΛ (by linarith) (by norm_num; linarith)
    hR hlocal hsupport hdisjoint, ?_⟩
  intro j hj
  exact GC.MetricGeometry.radial_support_test_ball_buffer hρ (hpos p) (hpos (z j)) hL
    hΛ hT (hR j) he (hlocal j p) (herror j) (hvalue j) hj

end DifferentialGeometry.Geometry.Fibration
open Set Metric
namespace DifferentialGeometry.Geometry.Fibration
variable {X : Type*} [PseudoMetricSpace X]
/-- One universal bottom-side constant applies to EVERY actual weak point. -/
theorem finite_packet_all_weak_bottom_points :
    ∃ τ : ℝ, τ ∈ Ioo 0 (1 / 100) ∧
    ∀ (p : X) (Δ δ C : ℝ), 0 < Δ → 0 < δ → δ ≤ τ * Δ → 200 * Δ < C →
    ∀ (Q : X → WithLp 2 (ℝ × ℝ)) (E : Set X)
      (W : X → X → WithLp 2 (ℝ × ℝ)), Q p = 0 →
    (∀ x ∈ ball p (200 * Δ), ∀ y ∈ ball p (200 * Δ),
      |dist (Q x) (Q y) - dist x y| ≤ δ) →
    (∀ y : WithLp 2 (ℝ × ℝ), y.snd ∈ Icc 0 C → ‖y‖ < 200 * Δ - δ →
      infDist y (Q '' ball p (200 * Δ)) ≤ δ) →
    (∀ z ∈ E ∩ ball p (120 * Δ), W z z = 0) →
    (∀ z ∈ E ∩ ball p (120 * Δ), ∀ x ∈ ball z Δ, 0 ≤ (W z x).snd) →
    (∀ z ∈ E ∩ ball p (120 * Δ), ∀ x ∈ ball z Δ, ∀ y ∈ ball z Δ,
      |dist (W z x) (W z y) - dist x y| ≤ δ) →
    ∀ z ∈ E ∩ ball p (120 * Δ), (Q z).snd < Δ / 10 := by
  refine ⟨1 / 1000000, by norm_num, ?_⟩
  intro p Δ δ C hΔ hδ hδsmall hC Q E W hQp hQdist hcover hWz hWheight hWdist z hz
  exact GC.MetricGeometry.padded_strip_height_lt_of_half_plane_model hΔ hδ
    (by linarith) hC Q (W z) hQp (hWz z hz) hQdist hcover (hWheight z hz)
    (hWdist z hz) hz.2

/-- SAME actual normalized height controls the physical alternative and fixed joint cutoffs. -/
theorem finite_packet_weak_edge_profile_alternative {E ι : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [Fintype ι]
    {P ρ : X → ℝ} {K Λ : NNReal}
    (hP : LipschitzWith K P) (hρ : LipschitzWith Λ ρ) (hK : (K : ℝ) ≤ 2)
    (hPnonneg : ∀ x, 0 ≤ P x) (hpos : ∀ x, 0 < ρ x)
    {p q : X} {L Δ : ℝ} (hL : 0 < L) (hΔ : 120 * L ≤ Δ)
    (hsmall : Δ * Λ ≤ 1 / 100) (hLsmall : L * Λ ≤ 1 / 4)
    (hq : q ∈ ball p (L * ρ p)) (hvq : P q / ρ q ≤ 9 * Δ)
    {A : Set X} (hnear : infDist p A ≤ 30 * Δ * ρ p)
    (s : ι → ℝ) (u : ι → E →L[ℝ] ℝ) (v : E →L[ℝ] ℝ) (η : X → E)
    (hheight : ∀ x ∈ ball p (L * ρ p), v (η x) = P x / ρ x) :
    (∀ x ∈ ball p (L * ρ p), P x / ρ x < 3 * Δ / 20 ∧
      DifferentialGeometry.Analysis.fixedJointCutoffNetwork Δ s u v (η x) none = 0 ∧
      ∀ j, DifferentialGeometry.Analysis.fixedJointCutoffNetwork Δ s u v (η x) (some j) =
        WithLp.toLp 2 (s j * (u j (η x) *
          DifferentialGeometry.Analysis.edgeCoordinateProfile (Δ⁻¹ * u j (η x))),
          s j * DifferentialGeometry.Analysis.edgeCoordinateProfile (Δ⁻¹ * u j (η x)))) ∨
    (∃ y ∈ ball p (L * ρ p), 3 * Δ / 20 ≤ P y / ρ y) ∧
      ∀ x ∈ ball p (L * ρ p),
        P x / ρ x ∈ Icc (Δ / 10) (181 * Δ / 20) ∧ infDist x A / ρ x < 50 * Δ := by
  rcases GC.MetricGeometry.weak_edge_quotient_alternative hP hρ hK hPnonneg hpos hL hΔ
    hsmall hLsmall hq hvq hnear with hlow | hhigh
  · left
    intro x hx
    refine ⟨hlow x hx, ?_⟩
    exact DifferentialGeometry.Analysis.fixedJointCutoffNetwork_low_height (by linarith)
      s u v (by rw [hheight x hx]; exact hlow x hx)
  · exact Or.inr hhigh

end DifferentialGeometry.Geometry.Fibration
