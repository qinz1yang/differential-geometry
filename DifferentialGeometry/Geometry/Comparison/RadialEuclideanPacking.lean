import DifferentialGeometry.Geometry.Comparison.PackingTransport
import DifferentialGeometry.Topology.MetricSpace.EuclideanPacking

set_option autoImplicit false

open Set Metric Real

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X]

theorem finitePackingNumber_le_of_radial_bounded_map
    (hcurves : ∀ x y : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + η))
    {Ω W : Set X} (hcomp : fourPointComparison 1 Ω) {q : X} (hq : q ∈ Ω)
    {a D t ρ ε : ℝ} (ha : 0 < a) (haD : a ≤ D) (ht : t ∈ Ioo 0 1)
    (htD : t * D < ρ) (hε : 0 < ε) (hB : ball q ρ ⊆ Ω) (hW : W ⊆ Ω)
    (hrad : ∀ x ∈ W, dist q x ∈ Icc a D)
    {m : ℕ} (hm : 0 < m) {f : ball q ρ → PiLp 2 (fun _ : Fin m => ℝ)}
    {B K : ℝ} (hBn : 0 ≤ B) (hK : 0 < K) (hnorm : ∀ x, ‖f x‖ ≤ B)
    (hlower : ∀ x y, K * dist x y ≤ dist (f x) (f y)) :
    finitePackingNumber ε W ≤
      (⌊(1 + 8 * B * sqrt m / (K * (t * D / sinh D) * ε)) ^ m⌋₊ : ℕ∞) := by
  have hLambda : 0 < t * D / sinh D :=
    div_pos (mul_pos ht.1 (ha.trans_le haD)) (sinh_pos_iff.mpr (ha.trans_le haD))
  have he : K * ((t * D / sinh D) / 2 * ε) = (K * (t * D / sinh D) * ε) / 2 := by ring
  have he' : 4 * B * sqrt m / (K * ((t * D / sinh D) / 2 * ε)) =
      8 * B * sqrt m / (K * (t * D / sinh D) * ε) := by
    rw [he, div_div_eq_mul_div]
    ring
  have h := finitePackingNumber_le_floor_of_bounded_lower_dist_map hm hBn hK
    (mul_pos (half_pos hLambda) hε) hnorm hlower
  rw [he'] at h
  exact (finitePackingNumber_le_radial_ball hcurves hcomp hq ha haD ht htD hε hB hW hrad).trans h

theorem finitePackingNumber_le_of_radial_centered_dist_bounds
    (hcurves : ∀ x y : X, ∀ η : ℝ, 0 < η →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = x ∧ c 1 = y ∧
        eVariationOn c univ < ENNReal.ofReal (dist x y + η))
    {Ω W : Set X} (hcomp : fourPointComparison 1 Ω) {q : X} (hq : q ∈ Ω)
    {a D t ρ ε : ℝ} (ha : 0 < a) (haD : a ≤ D) (ht : t ∈ Ioo 0 1)
    (htD : t * D < ρ) (hε : 0 < ε) (hB : ball q ρ ⊆ Ω) (hW : W ⊆ Ω)
    (hrad : ∀ x ∈ W, dist q x ∈ Icc a D)
    {m : ℕ} (hm : 0 < m) {f : ball q ρ → PiLp 2 (fun _ : Fin m => ℝ)}
    (hρ : 0 < ρ) {L : ℝ} (hL : 0 < L)
    (hzero : f ⟨q, mem_ball_self hρ⟩ = 0)
    (hlower : ∀ x y, L⁻¹ * dist x y ≤ dist (f x) (f y))
    (hupper : ∀ x y, dist (f x) (f y) ≤ L * dist x y) :
    finitePackingNumber ε W ≤
      (⌊(1 + 8 * L ^ 2 * ρ * sqrt m / ((t * D / sinh D) * ε)) ^ m⌋₊ : ℕ∞) := by
  have hnorm (x : ball q ρ) : ‖f x‖ ≤ L * ρ := by
    calc
      ‖f x‖ = dist (f x) (f ⟨q, mem_ball_self hρ⟩) := by rw [hzero, dist_zero_right]
      _ ≤ L * dist (x : X) q := hupper x ⟨q, mem_ball_self hρ⟩
      _ ≤ L * ρ := mul_le_mul_of_nonneg_left (mem_ball.mp x.property).le hL.le
  have h := finitePackingNumber_le_of_radial_bounded_map hcurves hcomp hq ha haD ht htD
    hε hB hW hrad hm (mul_pos hL hρ).le (inv_pos.mpr hL) hnorm hlower
  have he : 8 * (L * ρ) * sqrt m / (L⁻¹ * (t * D / sinh D) * ε) =
      8 * L ^ 2 * ρ * sqrt m / ((t * D / sinh D) * ε) := by
    field_simp
  simpa only [he] using h

end DifferentialGeometry.Geometry.Comparison.Toponogov
