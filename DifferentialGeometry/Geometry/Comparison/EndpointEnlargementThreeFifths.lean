import DifferentialGeometry.Geometry.Comparison.HingeOfGerms
import DifferentialGeometry.Geometry.Comparison.CradleEnlargementThreeFifths

set_option autoImplicit false


open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem endpointHingeComparison_enlarge_three_fifths
    {X : Type*} [MetricSpace X] {κ ℓ : ℝ} (hκ : 0 ≤ κ) (hℓ : 0 < ℓ) {p : X}
    (hp : endpointHingeComparison κ p (3 * ℓ / 5))
    (hq : ∀ q ∈ ball p ℓ, endpointHingeComparison κ q (3 * ℓ / 5))
    (hjoins : ∀ q ∈ ball p ℓ, ∀ z : X, dist z p + dist z q < ℓ →
      ∃ J : MinimizingHinge p q, J.center = z)
    (hlocal : ∀ z ∈ ball p ℓ,
      ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison κ Ω ∧ z ∈ Ω) :
    endpointHingeComparison κ p ℓ := by
  intro x R S γ β hR hS hsum hγend hγrad hβrad hγmin hβmin
  let q := β S
  have ha : dist x p = R := by simpa only [hγend] using hγrad R ⟨hR, le_rfl⟩
  have hb : dist x q = S := hβrad S ⟨hS, le_rfl⟩
  have hqball : q ∈ ball p ℓ := by
    have ht := dist_triangle q x p
    rw [dist_comm q x, ha, hb] at ht
    exact ht.trans_lt (by linarith)
  obtain ⟨H, hcenter, hangle⟩ := MinimizingHinge.exists_hinge_of_germs
    (κ := κ) hR hS hγend (show β S = q from rfl) hγrad hβrad hγmin hβmin
  have ht := H.comparisonAngle_le_of_small_hinges_three_fifths hκ hℓ hp (hq q hqball)
    (hjoins q hqball)
    (fun z hz => hlocal z (show z ∈ ball p ℓ from
      (le_add_of_nonneg_right (dist_nonneg (x := z) (y := q))).trans_lt hz))
    (by rw [hcenter, ha]; exact hR) (by rw [hcenter, hb]; exact hS)
    (by rw [hcenter, ha, hb]; exact hsum)
  rwa [hcenter, ha, hb, hangle] at ht

end DifferentialGeometry.Geometry.Comparison.Toponogov
