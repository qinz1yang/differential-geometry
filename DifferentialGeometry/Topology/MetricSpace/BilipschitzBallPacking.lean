import DifferentialGeometry.Topology.MetricSpace.EuclideanPacking

set_option autoImplicit false

open Set Real

namespace Metric

variable {X : Type*} [MetricSpace X]

theorem finitePackingNumber_le_floor_of_centered_dist_bounds {q : X} {r : ℝ}
    (hr : 0 < r) {m : ℕ} (hm : 0 < m) {f : ball q r → PiLp 2 (fun _ : Fin m => ℝ)}
    {L ε : ℝ} (hL : 0 < L) (hε : 0 < ε) (hzero : f ⟨q, mem_ball_self hr⟩ = 0)
    (hlower : ∀ x y, L⁻¹ * dist x y ≤ dist (f x) (f y))
    (hupper : ∀ x y, dist (f x) (f y) ≤ L * dist x y) :
    finitePackingNumber ε (ball q r) ≤ (⌊(1 + 4 * L ^ 2 * r * sqrt m / ε) ^ m⌋₊ : ℕ∞) := by
  have hnorm (x : ball q r) : ‖f x‖ ≤ L * r := by
    calc
      ‖f x‖ = dist (f x) (f ⟨q, mem_ball_self hr⟩) := by rw [hzero, dist_zero_right]
      _ ≤ L * dist (x : X) q := hupper x ⟨q, mem_ball_self hr⟩
      _ ≤ L * r := mul_le_mul_of_nonneg_left (mem_ball.mp x.property).le hL.le
  have h := finitePackingNumber_le_floor_of_bounded_lower_dist_map hm (mul_pos hL hr).le
    (inv_pos.mpr hL) hε hnorm hlower
  have he : 4 * (L * r) * sqrt m / (L⁻¹ * ε) = 4 * L ^ 2 * r * sqrt m / ε := by
    field_simp
  simpa only [he] using h

end Metric
