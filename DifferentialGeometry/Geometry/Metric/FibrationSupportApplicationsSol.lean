import DifferentialGeometry.Geometry.Metric.ZeroSupportIsolation
import DifferentialGeometry.Geometry.Metric.SupportDomainBuffer
import DifferentialGeometry.Geometry.Metric.RadialSupportBuffer
import DifferentialGeometry.Geometry.Metric.WeakEdgeLocalization
import DifferentialGeometry.Analysis.Calculus.Cutoff.EdgeNetworkProfiles

set_option autoImplicit false
open Set Metric DifferentialGeometry.Analysis

namespace GC.MetricGeometry.X81Sol
variable {X : Type*} [PseudoMetricSpace X]

theorem unique_zero_support_and_core {ι : Type*} {ρ : X → ℝ} {Λ : NNReal}
    (hρ : LipschitzWith Λ ρ) (hpos : ∀ x, 0 < ρ x)
    (z : ι → X) (R : ι → ℝ) (S : ι → Set X) {p : X} {L T θ : ℝ}
    (hL : 0 < L) (hθ : θ < 1) (hΛ : L * Λ ≤ 1 / 4)
    (hT : 40 * L < T) (hTθ : 40 * L / (1 - θ) < T)
    (hR : ∀ i, T * ρ (z i) ≤ R i)
    (hlocal : ∀ i q, dist (z i) q ≤ 10 * R i → T / 20 ≤ R i / ρ q)
    (hsupport : ∀ i, S i ⊆ closedBall (z i) (θ * R i))
    (hdisjoint : Pairwise fun i j => Disjoint (ball (z i) (R i)) (ball (z j) (R j))) :
    {i | (S i ∩ ball p (L * ρ p)).Nonempty}.Subsingleton ∧
      ∀ i, (S i ∩ ball p (L * ρ p)).Nonempty → ball p (L * ρ p) ⊆ ball (z i) (R i) := by
  refine ⟨subsingleton_zero_supports_meeting_ball hρ hpos z R S hL hθ hΛ hT hTθ
    hR hlocal hsupport hdisjoint, ?_⟩
  intro i hi
  exact (ball_subset_zero_core_of_support_meeting hρ (hpos p) (hpos (z i)) hL hθ hΛ
    hT hTθ (hR i) (hlocal i p) (hi.mono (inter_subset_inter_left _ (hsupport i)))).2

theorem support_meeting_ball_positive_margin {p q : X} {r rj L c b : ℝ} {S U : Set X}
    (hr : 0 < r) (hrj : 0 < rj) (hL : 0 < L)
    (hratio : (1 / 2 : ℝ) ≤ rj / r) (hgap : 4 * L < b - c)
    (hsupport : S ⊆ closedBall q (c * rj)) (hdomain : ball q (b * rj) ⊆ U)
    (hmeet : (S ∩ ball p (L * r)).Nonempty) :
    ball p (L * r) ⊆ U ∧ 0 < (b - c - 4 * L) * rj ∧
      ∀ x ∈ ball p (L * r), Uᶜ.Nonempty → (b - c - 4 * L) * rj ≤ infDist x Uᶜ := by
  have h := support_meeting_ball_buffer hr hrj hL hratio hgap hsupport hdomain hmeet
  exact ⟨h.1.trans h.2.1, mul_pos (by linarith) hrj, h.2.2⟩

theorem radial_support_open_annulus {ρ η : X → ℝ} {Λ : NNReal}
    (hρ : LipschitzWith Λ ρ) {p z : X} (hp : 0 < ρ p) (hz : 0 < ρ z)
    {L T R e : ℝ} (hL : 0 < L) (hΛ : L * Λ ≤ 1 / 4)
    (hT : 1600 * L ≤ T) (hR : T * ρ z ≤ R) (he : e < 1 / 40)
    (hlocal : dist z p ≤ 10 * R → T / 20 ≤ R / ρ p)
    {S : Set X} (herror : ∀ x ∈ S, |η x - dist z x / R| < e)
    (hsupport : ∀ x ∈ S, η x ∈ Icc (1 / 5) (9 / 10))
    (hmeet : (S ∩ ball p (L * ρ p)).Nonempty) :
    T / 20 ≤ R / ρ p ∧ IsOpen {x : X | dist z x / R ∈ Ioo (1 / 10) 10} ∧
      ball p (L * ρ p) ⊆ {x : X | dist z x / R ∈ Ioo (1 / 10) 10} := by
  have h := radial_support_test_ball_buffer hρ hp hz hL hΛ hT hR he hlocal herror hsupport hmeet
  refine ⟨h.1, isOpen_Ioo.preimage (continuous_const.dist continuous_id |>.div_const R), ?_⟩
  intro x hx
  have hh := h.2 x hx
  exact ⟨by linarith [hh.1], by linarith [hh.2]⟩

theorem weak_edge_actual_cutoff_alternative {P ρ : X → ℝ} {K Λ : NNReal}
    (hP : LipschitzWith K P) (hρ : LipschitzWith Λ ρ) (hK : (K : ℝ) ≤ 2)
    (hPnonneg : ∀ x, 0 ≤ P x) (hpos : ∀ x, 0 < ρ x)
    {p q : X} {L Δ : ℝ} (hL : 0 < L) (hΔ : 120 * L ≤ Δ)
    (hsmall : Δ * Λ ≤ 1 / 100) (hLsmall : L * Λ ≤ 1 / 4)
    (hq : q ∈ ball p (L * ρ p)) (hvq : P q / ρ q ≤ 9 * Δ)
    {E : Set X} (hnear : infDist p E ≤ 30 * Δ * ρ p) :
    (∀ x ∈ ball p (L * ρ p),
      P x / ρ x < 3 * Δ / 20 ∧ edgeHeightProfile (P x / ρ x / Δ) = 1 ∧
        jointHeightProfile (P x / ρ x / Δ) = 0) ∨
      (∃ y ∈ ball p (L * ρ p), 3 * Δ / 20 ≤ P y / ρ y) ∧
      ∀ x ∈ ball p (L * ρ p),
        P x / ρ x ∈ Icc (Δ / 10) (181 * Δ / 20) ∧ infDist x E / ρ x < 50 * Δ := by
  rcases weak_edge_quotient_alternative hP hρ hK hPnonneg hpos hL hΔ hsmall hLsmall hq hvq hnear with h | h
  · left
    intro x hx
    have hv := h x hx
    exact ⟨hv, edgeProfiles_low_height ((div_lt_iff₀ (by linarith : 0 < Δ)).mpr (by linarith))⟩
  · exact Or.inr h

end GC.MetricGeometry.X81Sol
