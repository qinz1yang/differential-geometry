import DifferentialGeometry.Geometry.Comparison.ModelAngle

set_option autoImplicit false

open Set

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

def fourPointComparison {X : Type*} [MetricSpace X] (κ : ℝ) (s : Set X) : Prop :=
  ∀ x ∈ s, ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s, a ≠ x → b ≠ x → c ≠ x →
    comparisonAngleNegCurvature κ (dist x a) (dist x b) (dist a b) +
      comparisonAngleNegCurvature κ (dist x b) (dist x c) (dist b c) +
      comparisonAngleNegCurvature κ (dist x c) (dist x a) (dist c a) ≤ 2 * Real.pi

theorem fourPointComparison.mono {X : Type*} [MetricSpace X] {κ : ℝ} {s t : Set X}
    (h : fourPointComparison κ s) (hst : t ⊆ s) : fourPointComparison κ t := by
  intro x hx a ha b hb c hc hax hbx hcx
  exact h x (hst hx) a (hst ha) b (hst hb) c (hst hc) hax hbx hcx

theorem fourPointComparison_of_distinct {X : Type*} [MetricSpace X] {κ : ℝ}
    (hκ : 0 ≤ κ) {s : Set X}
    (h : ∀ x ∈ s, ∀ a ∈ s, ∀ b ∈ s, ∀ c ∈ s,
      a ≠ x → b ≠ x → c ≠ x → a ≠ b → b ≠ c → c ≠ a →
      comparisonAngleNegCurvature κ (dist x a) (dist x b) (dist a b) +
        comparisonAngleNegCurvature κ (dist x b) (dist x c) (dist b c) +
        comparisonAngleNegCurvature κ (dist x c) (dist x a) (dist c a) ≤ 2 * Real.pi) :
    fourPointComparison κ s := by
  intro x hx a ha b hb c hc hax hbx hcx
  have hbound (u w : X) :
      comparisonAngleNegCurvature κ (dist x u) (dist x w) (dist u w) ≤ Real.pi :=
    (comparisonAngleNegCurvature_mem_Icc _ _ _ _).2
  have hzero (u : X) (hu : u ≠ x) :
      comparisonAngleNegCurvature κ (dist x u) (dist x u) (dist u u) = 0 := by
    rw [dist_self]
    exact comparisonAngleNegCurvature_self hκ (dist_pos.mpr (Ne.symm hu))
  by_cases hab : a = b
  · subst b
    rw [hzero a hax]
    linarith [hbound a c, hbound c a]
  by_cases hbc : b = c
  · subst c
    rw [hzero b hbx]
    linarith [hbound a b, hbound b a]
  by_cases hca : c = a
  · subst c
    rw [hzero a hax]
    linarith [hbound a b, hbound b a]
  exact h x hx a ha b hb c hc hax hbx hcx hab hbc hca

private theorem cos_add_cos_nonneg_of_sum_le_pi {θ φ : ℝ}
    (hθ : θ ∈ Icc 0 Real.pi) (hφ : φ ∈ Icc 0 Real.pi)
    (hsum : θ + φ ≤ Real.pi) : 0 ≤ Real.cos θ + Real.cos φ := by
  have hcos := Real.cos_le_cos_of_nonneg_of_le_pi hφ.1
    (by linarith [hθ.1] : Real.pi - θ ≤ Real.pi) (by linarith : φ ≤ Real.pi - θ)
  rw [Real.cos_pi_sub] at hcos
  linarith

private theorem weighted_sq_le_of_cosine_sum {α β h A B : ℝ}
    (hα : 0 < α) (hβ : 0 < β) (hh : 0 < h)
    (hsum : 0 ≤ (β ^ 2 + h ^ 2 - B ^ 2) / (2 * β * h) +
      (h ^ 2 + α ^ 2 - A ^ 2) / (2 * h * α)) :
    β * A ^ 2 + α * B ^ 2 ≤ (α + β) * h ^ 2 + α * β * (α + β) := by
  have hm := mul_nonneg hsum
    (show 0 ≤ 2 * α * β * h by positivity)
  have heq : ((β ^ 2 + h ^ 2 - B ^ 2) / (2 * β * h) +
      (h ^ 2 + α ^ 2 - A ^ 2) / (2 * h * α)) * (2 * α * β * h) =
      α * (β ^ 2 + h ^ 2 - B ^ 2) + β * (h ^ 2 + α ^ 2 - A ^ 2) := by
    field_simp
  rw [heq] at hm
  nlinarith

theorem quadratic_side_comparison_of_fourPointComparison
    {X : Type*} [MetricSpace X] {s : Set X} (hs : fourPointComparison 0 s)
    {a b z v : X} (ha : a ∈ s) (hb : b ∈ s) (hz : z ∈ s) (hv : v ∈ s)
    {t : ℝ} (ht : t ∈ Icc 0 1)
    (haz : dist a z = t * dist a b) (hzb : dist z b = (1 - t) * dist a b) :
    (1 - t) * dist v a ^ 2 + t * dist v b ^ 2 -
      t * (1 - t) * dist a b ^ 2 ≤ dist v z ^ 2 := by
  by_cases hab : a = b
  · subst b
    have haz0 : dist a z = 0 := by simpa using haz
    have haz' : a = z := dist_eq_zero.mp haz0
    subst z
    simp only [dist_self, mul_zero, sub_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    nlinarith
  by_cases ht0 : t = 0
  · have haz' : a = z := dist_eq_zero.mp (by simpa [ht0] using haz)
    subst z
    simp [ht0]
  by_cases ht1 : t = 1
  · have hzb' : z = b := dist_eq_zero.mp (by simpa [ht1] using hzb)
    subst z
    simp [ht1]
  by_cases hvz : v = z
  · subst v
    rw [dist_self, dist_comm z a, haz, hzb]
    ring_nf
    exact le_refl _
  have hL : 0 < dist a b := dist_pos.mpr hab
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have htlt : t < 1 := lt_of_le_of_ne ht.2 ht1
  have hα : 0 < dist z a := by rw [dist_comm z a, haz]; exact mul_pos htpos hL
  have hβ : 0 < dist z b := by rw [hzb]; exact mul_pos (sub_pos.mpr htlt) hL
  have hh : 0 < dist z v := dist_pos.mpr (Ne.symm hvz)
  have hparts : dist z a + dist z b = dist a b := by
    rw [dist_comm z a, haz, hzb]
    ring
  have hstraight : comparisonAngle (dist z a) (dist z b) (dist a b) = Real.pi := by
    rw [← hparts]
    exact comparisonAngle_add hα hβ
  have hangles := hs z hz a ha b hb v hv (dist_pos.mp hα).symm
    (dist_pos.mp hβ).symm hvz
  simp only [comparisonAngleNegCurvature_zero] at hangles
  rw [hstraight] at hangles
  have hsum : 0 ≤ Real.cos (metricComparisonAngle b z v) +
      Real.cos (metricComparisonAngle v z a) := by
    apply cos_add_cos_nonneg_of_sum_le_pi (comparisonAngle_mem_Icc _ _ _)
      (comparisonAngle_mem_Icc _ _ _)
    linarith
  rw [cos_metricComparisonAngle (dist_pos.mp hβ).symm hvz,
    cos_metricComparisonAngle hvz (dist_pos.mp hα).symm] at hsum
  have hweighted := weighted_sq_le_of_cosine_sum hα hβ hh hsum
  apply (mul_le_mul_iff_left₀ hL).mp
  calc
    ((1 - t) * dist v a ^ 2 + t * dist v b ^ 2 -
        t * (1 - t) * dist a b ^ 2) * dist a b =
        dist z b * dist v a ^ 2 + dist z a * dist b v ^ 2 -
          dist z a * dist z b * (dist z a + dist z b) := by
      rw [dist_comm z a, haz, hzb, dist_comm b v]
      ring
    _ ≤ (dist z a + dist z b) * dist z v ^ 2 := by linarith
    _ = dist v z ^ 2 * dist a b := by rw [hparts, dist_comm z v]; ring

end DifferentialGeometry.Geometry.Comparison.Toponogov
