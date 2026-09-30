import DifferentialGeometry.Geometry.Metric.ConeDistance
import Mathlib.Topology.MetricSpace.Cauchy

set_option autoImplicit false

open Set Filter Topology

namespace Metric

theorem two_mul_radius_mul_min_dist_le_pi_mul_coneDistance
    {Y : Type*} [PseudoMetricSpace Y] {x y : ℝ × Y} {ρ : ℝ}
    (hρ : 0 ≤ ρ) (hx : ρ ≤ x.1) (hy : ρ ≤ y.1) :
    2 * ρ * min Real.pi (dist x.2 y.2) ≤ Real.pi * coneDistance x y := by
  let θ := min Real.pi (dist x.2 y.2)
  have hθ : 0 ≤ θ := le_min Real.pi_pos.le dist_nonneg
  have hθpi : θ ≤ Real.pi := min_le_left _ _
  have hsin : 0 ≤ Real.sin (θ / 2) :=
    Real.sin_nonneg_of_nonneg_of_le_pi (by positivity) (by linarith)
  have hrad : ρ ^ 2 ≤ x.1 * y.1 := by
    simpa only [pow_two] using mul_le_mul hx hy hρ (hρ.trans hx)
  have hsq := coneDistance_sq (hρ.trans hx) (hρ.trans hy)
  have hid : Real.sin (θ / 2) ^ 2 = (1 - Real.cos θ) / 2 := by
    have h := Real.sin_sq_eq_half_sub (θ / 2)
    rw [mul_div_cancel₀ _ (by norm_num : (2 : ℝ) ≠ 0)] at h
    linarith
  have hlower : 2 * ρ * Real.sin (θ / 2) ≤ coneDistance x y := by
    apply (sq_le_sq₀ (by positivity) (coneDistance_nonneg _ _)).mp
    have hmul := mul_le_mul_of_nonneg_right hrad (sq_nonneg (Real.sin (θ / 2)))
    have hident : coneDistance x y ^ 2 =
        (x.1 - y.1) ^ 2 + 4 * (x.1 * y.1) * Real.sin (θ / 2) ^ 2 := by
      dsimp only [θ] at hid
      nlinarith [hsq]
    nlinarith [sq_nonneg (x.1 - y.1)]
  have hjordan : θ / Real.pi ≤ Real.sin (θ / 2) := by
    calc
      θ / Real.pi = 2 / Real.pi * (θ / 2) := by ring
      _ ≤ Real.sin (θ / 2) := Real.mul_le_sin (by positivity) (by linarith)
  have hj := mul_le_mul_of_nonneg_left hjordan (show 0 ≤ 2 * ρ by positivity)
  have h := hj.trans hlower
  have hp := mul_le_mul_of_nonneg_right h Real.pi_pos.le
  have heq : (2 * ρ * (θ / Real.pi)) * Real.pi = 2 * ρ * θ := by field_simp
  simpa only [heq, mul_comm (coneDistance x y) Real.pi] using hp

theorem dist_lt_of_coneDistance_lt
    {Y : Type*} [PseudoMetricSpace Y] {x y : ℝ × Y} {ρ ε : ℝ}
    (hρ : 0 < ρ) (hx : ρ ≤ x.1) (hy : ρ ≤ y.1)
    (hεπ : ε ≤ Real.pi)
    (hd : coneDistance x y < 2 * ρ * ε / Real.pi) :
    dist x.2 y.2 < ε := by
  have hbound := two_mul_radius_mul_min_dist_le_pi_mul_coneDistance hρ.le hx hy
  have hsmall : Real.pi * coneDistance x y < 2 * ρ * ε := by
    have h := (lt_div_iff₀ Real.pi_pos).mp hd
    simpa only [mul_comm (coneDistance x y) Real.pi] using h
  have hmin : min Real.pi (dist x.2 y.2) < ε := by
    nlinarith
  rcases min_lt_iff.mp hmin with hpi | hdist
  · exact False.elim (not_lt_of_ge hεπ hpi)
  · exact hdist

theorem cauchySeq_directions_of_coneDistance_cauchy
    {Y : Type*} [PseudoMetricSpace Y] {r : ℕ → ℝ} {u : ℕ → Y} {ρ : ℝ}
    (hρ : 0 < ρ) (hr : ∀ᶠ n in atTop, ρ ≤ r n)
    (hc : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ m ≥ N, ∀ n ≥ N,
      coneDistance (r m, u m) (r n, u n) < ε) :
    CauchySeq u := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp hr
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  let δ := min ε Real.pi
  have hδ : 0 < δ := lt_min hε Real.pi_pos
  obtain ⟨M, hM⟩ := hc (2 * ρ * δ / Real.pi) (by positivity)
  refine ⟨max N M, fun m hm n hn => ?_⟩
  have hd := dist_lt_of_coneDistance_lt hρ (hN m ((le_max_left _ _).trans hm))
    (hN n ((le_max_left _ _).trans hn)) (min_le_right ε Real.pi)
    (hM m ((le_max_right _ _).trans hm) n ((le_max_right _ _).trans hn))
  exact hd.trans_le (min_le_left _ _)

end Metric
