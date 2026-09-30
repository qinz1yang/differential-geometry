import DifferentialGeometry.Geometry.Metric.RetainedMarkerRadii

set_option autoImplicit false

namespace GC.MetricGeometry

theorem nearby_scale_comparison_of_retained_markers {P X A : Type*} [PseudoMetricSpace X]
    (f : P → X) (ρ : P → ℝ) (marker : A → X → ℝ) (R : A → ℝ)
    (hR : ∀ i, 0 < R i) (hmarker : ∀ i, LipschitzWith 1 (marker i))
    (hfull : ∀ p, ∃ i, marker i (f p) = R i)
    (hsupport : ∀ i p, 0 < marker i (f p) → 3 * R i / 4 ≤ ρ p ∧ ρ p ≤ 5 * R i / 4)
    {σ L : ℝ} (hσ : 0 ≤ σ) (hL : 0 ≤ L) (hsmall : L * σ ≤ 1 / 5)
    (p q : P) (hdist : dist (f p) (f q) ≤ L * max (σ * ρ p) (σ * ρ q)) :
    (3 / 5 : ℝ) * ρ p ≤ ρ q ∧ ρ q ≤ (5 / 3 : ℝ) * ρ p := by
  obtain ⟨i, hi⟩ := hfull p
  obtain ⟨j, hj⟩ := hfull q
  have hp := hsupport i p (by rw [hi]; exact hR i)
  have hq := hsupport j q (by rw [hj]; exact hR j)
  have near (k : A) (hpR : ρ p ≤ 5 * R k / 4) (hqR : ρ q ≤ 5 * R k / 4) :
      dist (f p) (f q) ≤ R k / 4 := by
    have hm : max (σ * ρ p) (σ * ρ q) ≤ σ * (5 * R k / 4) :=
      max_le (mul_le_mul_of_nonneg_left hpR hσ) (mul_le_mul_of_nonneg_left hqR hσ)
    have hd := hdist.trans (mul_le_mul_of_nonneg_left hm hL)
    have hs := mul_le_mul_of_nonneg_right hsmall (show 0 ≤ 5 * R k / 4 by linarith [hR k])
    nlinarith
  rcases le_total (R i) (R j) with hij | hji
  · have hd := near j (by linarith [hp.2]) hq.2
    have hm := (hmarker j).dist_le_mul (f p) (f q)
    rw [Real.dist_eq, hj] at hm
    norm_num only [NNReal.coe_one, one_mul] at hm
    have hpos : 0 < marker j (f p) := by linarith [(abs_le.mp hm).1, hR j]
    have hpj := hsupport j p hpos
    exact ⟨by linarith [hpj.2, hq.1], by linarith [hpj.1, hq.2]⟩
  · have hd := near i hp.2 (by linarith [hq.2])
    have hm := (hmarker i).dist_le_mul (f p) (f q)
    rw [Real.dist_eq, hi] at hm
    norm_num only [NNReal.coe_one, one_mul] at hm
    have hpos : 0 < marker i (f q) := by linarith [(abs_le.mp hm).2, hR i]
    have hqi := hsupport i q hpos
    exact ⟨by linarith [hp.2, hqi.1], by linarith [hp.1, hqi.2]⟩

theorem small_radius_lt_half_reference_of_contributing_support
    {P X A : Type*} [PseudoMetricSpace X]
    (f : P → X) (ρ : P → ℝ) (marker : A → X → ℝ) (R : A → ℝ)
    (hR : ∀ i, 0 < R i) (hmarker : ∀ i, LipschitzWith 1 (marker i))
    (hfull : ∀ p, ∃ i, marker i (f p) = R i)
    (hsupport : ∀ i p, 0 < marker i (f p) → 3 * R i / 4 ≤ ρ p ∧ ρ p ≤ 5 * R i / 4)
    {b σ : ℝ} (hb : 0 ≤ b) (hσ : 0 ≤ σ) (hsmall : (128 * b) * σ ≤ 1 / 5)
    (p pₓ pᵤ qᵤ : P) (hpx : f pₓ = f p) (hpu : f pᵤ = f qᵤ)
    (hmeet : (Metric.closedBall (f pᵤ) (80 * b * (σ * ρ pᵤ)) ∩
      Metric.ball (f pₓ) (8 * b * (σ * ρ pₓ))).Nonempty)
    (a i : A) (ha : marker a (f qᵤ) = R a) (hi : R i < ρ p / 16) :
    R i < R a / 2 := by
  obtain ⟨j, hj⟩ := hfull p
  have hpxScale := scale_comparison_of_retained_marker f ρ marker R hR hsupport hpx.symm j hj
  have hpuScale := scale_comparison_of_retained_marker f ρ marker R hR hsupport hpu
    a (by rw [hpu]; exact ha)
  have hposx : 0 < ρ pₓ := lt_of_lt_of_le (by linarith [hpxScale.1]) hpxScale.2.1
  have hdist : dist (f pₓ) (f pᵤ) ≤ (128 * b) * max (σ * ρ pₓ) (σ * ρ pᵤ) := by
    obtain ⟨z, hzU, hzX⟩ := hmeet
    have htri := dist_triangle (f pₓ) z (f pᵤ)
    have hzu : dist z (f pᵤ) ≤ 80 * b * (σ * ρ pᵤ) := hzU
    have hzx : dist z (f pₓ) < 8 * b * (σ * ρ pₓ) := hzX
    rw [dist_comm (f pₓ) z] at htri
    have hmx := mul_le_mul_of_nonneg_left (le_max_left (σ * ρ pₓ) (σ * ρ pᵤ)) (by positivity : 0 ≤ 8 * b)
    have hmu := mul_le_mul_of_nonneg_left (le_max_right (σ * ρ pₓ) (σ * ρ pᵤ)) (by positivity : 0 ≤ 80 * b)
    have hm0 : 0 ≤ max (σ * ρ pₓ) (σ * ρ pᵤ) :=
      le_trans (mul_nonneg hσ hposx.le) (le_max_left _ _)
    have hbmax := mul_nonneg hb hm0
    nlinarith
  have hnear := nearby_scale_comparison_of_retained_markers f ρ marker R hR hmarker hfull
    hsupport hσ (by positivity : 0 ≤ 128 * b) hsmall pₓ pᵤ hdist
  have haScale := hsupport a qᵤ (by rw [ha]; exact hR a)
  linarith [hpxScale.2.1, hnear.1, hpuScale.2.1, haScale.2]

end GC.MetricGeometry
