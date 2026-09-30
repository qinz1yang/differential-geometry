import DifferentialGeometry.Geometry.Metric.RadialConeRays
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

noncomputable section
open scoped NNReal

namespace GC.MetricGeometry

variable {X : Type*} [MetricSpace X]

namespace RadialConeData

variable {p : X} (H : RadialConeData p)

theorem two_apex_cross_dist {q : X} (K : RadialConeData q) (hpq : p ≠ q)
    (s t : ℝ≥0) :
    dist (H.unitRay q s) (K.unitRay p (nndist q p + t)) = (s : ℝ) + t := by
  let z := K.unitRay p (nndist q p + t)
  have hL : dist p q ≠ 0 := dist_ne_zero.mpr hpq
  have hpz : dist p z = (t : ℝ) := by
    rw [← K.unitRay_through hpq, (K.unitRay_isometry hpq).dist_eq]
    change |((nndist q p : ℝ≥0) : ℝ) - ((nndist q p + t : ℝ≥0) : ℝ)| = t
    simp only [NNReal.coe_add, sub_add_cancel_left, abs_neg, abs_of_nonneg t.coe_nonneg]
  have hqz : dist q z = dist p q + (t : ℝ) := by
    rw [K.unitRay_dist_apex hpq]
    simp only [NNReal.coe_add, coe_nndist, dist_comm q p]
  have hkernel : radialConeKernel p q z = -(dist p q * (t : ℝ)) := by
    unfold radialConeKernel
    rw [hpz, hqz]
    ring
  have hh := H.dist_sq (s / nndist p q) 1 q z
  rw [H.map_one, hpz, hkernel] at hh
  norm_num only [NNReal.coe_div, coe_nndist, NNReal.coe_one, one_pow, one_mul, mul_one] at hh
  apply (sq_eq_sq₀ dist_nonneg (add_nonneg s.coe_nonneg t.coe_nonneg)).mp
  change dist (H.map (s / nndist p q) q) z ^ 2 = ((s : ℝ) + t) ^ 2
  rw [hh]
  field_simp
  ring


def twoApexLine {q : X} (K : RadialConeData q) (r : ℝ) : X :=
  if 0 ≤ r then H.unitRay q r.toNNReal
  else K.unitRay p (nndist q p + (-r).toNNReal)

theorem twoApexLine_nonneg {q : X} (K : RadialConeData q) {r : ℝ} (hr : 0 ≤ r) :
    H.twoApexLine K r = H.unitRay q r.toNNReal := ite_eq_left hr

theorem twoApexLine_nonpos {q : X} (K : RadialConeData q) (hpq : p ≠ q)
    {r : ℝ} (hr : r ≤ 0) :
    H.twoApexLine K r = K.unitRay p (nndist q p + (-r).toNNReal) := by
  rcases eq_or_lt_of_le hr with hr | hr
  · subst r
    simp only [twoApexLine, le_refl, ite_true, Real.toNNReal_zero, H.unitRay_zero,
      neg_zero, add_zero, K.unitRay_through hpq]
  · exact ite_eq_right (not_le.mpr hr)

theorem twoApexLine_zero {q : X} (K : RadialConeData q) : H.twoApexLine K 0 = p := by
  simp only [twoApexLine, le_refl, ite_true, Real.toNNReal_zero, H.unitRay_zero]

theorem twoApexLine_through {q : X} (K : RadialConeData q) (hpq : p ≠ q) :
    H.twoApexLine K (dist p q) = q := by
  rw [H.twoApexLine_nonneg K dist_nonneg]
  change H.unitRay q (Real.toNNReal ((nndist p q : ℝ≥0) : ℝ)) = q
  rw [Real.toNNReal_coe]
  exact H.unitRay_through hpq.symm

theorem twoApexLine_isometry {q : X} (K : RadialConeData q) (hpq : p ≠ q) :
    Isometry (H.twoApexLine K) := by
  apply Isometry.of_dist_eq
  intro s t
  change dist (H.twoApexLine K s) (H.twoApexLine K t) = |s - t|
  by_cases hs : 0 ≤ s
  · rw [H.twoApexLine_nonneg K hs]
    by_cases ht : 0 ≤ t
    · rw [H.twoApexLine_nonneg K ht, (H.unitRay_isometry hpq.symm).dist_eq]
      change |(s.toNNReal : ℝ) - (t.toNNReal : ℝ)| = |s - t|
      rw [Real.coe_toNNReal _ hs, Real.coe_toNNReal _ ht]
    · have ht' : t ≤ 0 := le_of_not_ge ht
      rw [H.twoApexLine_nonpos K hpq ht', H.two_apex_cross_dist K hpq]
      rw [Real.coe_toNNReal _ hs, Real.coe_toNNReal _ (neg_nonneg.mpr ht')]
      rw [abs_of_nonneg (sub_nonneg.mpr (ht'.trans hs))]
      ring
  · have hs' : s ≤ 0 := le_of_not_ge hs
    rw [H.twoApexLine_nonpos K hpq hs']
    by_cases ht : 0 ≤ t
    · rw [H.twoApexLine_nonneg K ht, dist_comm, H.two_apex_cross_dist K hpq]
      rw [Real.coe_toNNReal _ ht, Real.coe_toNNReal _ (neg_nonneg.mpr hs')]
      rw [abs_of_nonpos (sub_nonpos.mpr (hs'.trans ht))]
      ring
    · have ht' : t ≤ 0 := le_of_not_ge ht
      rw [H.twoApexLine_nonpos K hpq ht', (K.unitRay_isometry hpq).dist_eq]
      change |((nndist q p + (-s).toNNReal : ℝ≥0) : ℝ) -
        ((nndist q p + (-t).toNNReal : ℝ≥0) : ℝ)| = |s - t|
      simp only [NNReal.coe_add, Real.coe_toNNReal _ (neg_nonneg.mpr hs'),
        Real.coe_toNNReal _ (neg_nonneg.mpr ht'), add_sub_add_left_eq_sub]
      rw [neg_sub_neg, abs_sub_comm]

theorem exists_line_through_two_apices (H : RadialConeData p) {q : X} (K : RadialConeData q) (hpq : p ≠ q) :
    ∃ γ : ℝ → X, Isometry γ ∧ γ 0 = p ∧ γ (dist p q) = q :=
  ⟨H.twoApexLine K, H.twoApexLine_isometry K hpq, H.twoApexLine_zero K,
    H.twoApexLine_through K hpq⟩

end RadialConeData
end GC.MetricGeometry
