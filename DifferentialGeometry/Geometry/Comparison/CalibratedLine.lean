import DifferentialGeometry.Geometry.Comparison.CalibratedRay

set_option autoImplicit false

open Set
open scoped NNReal

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X]

theorem lineCoordinate_reverse
    (hs : fourPointComparison 0 (univ : Set X)) {γ : ℝ → X}
    (hγ : Isometry γ) (x : X) :
    lineCoordinate (fun t => γ (-t)) x = -lineCoordinate γ x := by
  have h := sq_dist_isometry_line hs hγ x (-1)
  unfold lineCoordinate at *
  simp only [neg_zero]
  nlinarith

theorem exists_calibrated_line [ProperSpace X]
    (hs : fourPointComparison 0 (univ : Set X)) {γ : ℝ → X} (hγ : Isometry γ)
    (hsegments : ∀ a b : X, ∃ f : Icc (0 : ℝ) 1 → X,
      Continuous f ∧ f ⟨0, by norm_num⟩ = a ∧ f ⟨1, by norm_num⟩ = b ∧
      ∀ s t, dist (f s) (f t) = dist a b * dist s t)
    (x : X) : ∃ ℓ : ℝ → X, Isometry ℓ ∧ ℓ 0 = x ∧
      ∀ t, lineCoordinate γ (ℓ t) = lineCoordinate γ x + t := by
  obtain ⟨r, hr, hr0, hbr⟩ := exists_calibrated_ray hs hγ hsegments x
  have hrev : Isometry (fun t : ℝ => γ (-t)) := by
    apply Isometry.of_dist_eq
    intro s t
    rw [hγ.dist_eq, dist_neg_neg]
  obtain ⟨q, hq, hq0, hbq⟩ := exists_calibrated_ray hs hrev hsegments x
  have hbq' (t : ℝ≥0) : lineCoordinate γ (q t) = lineCoordinate γ x - t := by
    have h := hbq t
    rw [lineCoordinate_reverse hs hγ, lineCoordinate_reverse hs hγ] at h
    linarith
  let ℓ (t : ℝ) := if 0 ≤ t then r t.toNNReal else q (-t).toNNReal
  have hb (t : ℝ) : lineCoordinate γ (ℓ t) = lineCoordinate γ x + t := by
    dsimp only [ℓ]
    split_ifs with ht
    · rw [hbr, Real.coe_toNNReal _ ht]
    · rw [hbq', Real.coe_toNNReal _ (by linarith : 0 ≤ -t)]
      ring
  have hrad (t : ℝ) : dist (ℓ t) x = |t| := by
    dsimp only [ℓ]
    split_ifs with ht
    · rw [← hr0, hr.dist_eq]
      change |(t.toNNReal : ℝ) - 0| = |t|
      rw [Real.coe_toNNReal _ ht, sub_zero]
    · rw [← hq0, hq.dist_eq]
      change |((-t).toNNReal : ℝ) - 0| = |t|
      rw [Real.coe_toNNReal _ (by linarith : 0 ≤ -t), sub_zero, abs_neg]
  have hlower (s t : ℝ) : dist s t ≤ dist (ℓ s) (ℓ t) := by
    have h := (lipschitzWith_lineCoordinate hs hγ).dist_le_mul (ℓ s) (ℓ t)
    rw [hb s, hb t] at h
    simpa only [NNReal.coe_one, one_mul, dist_add_left] using h
  have hupper (s t : ℝ) (hs0 : 0 ≤ s) (ht0 : t < 0) :
      dist (ℓ s) (ℓ t) ≤ dist s t := by
    have h := dist_triangle (ℓ s) x (ℓ t)
    rw [dist_comm x (ℓ t), hrad s, hrad t, abs_of_nonneg hs0, abs_of_neg ht0] at h
    rw [Real.dist_eq, abs_of_nonneg (by linarith : 0 ≤ s - t)]
    linarith
  refine ⟨ℓ, ?_, ?_, hb⟩
  · apply Isometry.of_dist_eq
    intro s t
    by_cases hs0 : 0 ≤ s
    · by_cases ht0 : 0 ≤ t
      · simp only [ℓ, ite_eq_left hs0, ite_eq_left ht0]
        rw [hr.dist_eq]
        change |(s.toNNReal : ℝ) - (t.toNNReal : ℝ)| = |s - t|
        rw [Real.coe_toNNReal _ hs0, Real.coe_toNNReal _ ht0]
      · exact le_antisymm (hupper s t hs0 (lt_of_not_ge ht0)) (hlower s t)
    · by_cases ht0 : 0 ≤ t
      · rw [dist_comm (ℓ s) (ℓ t), dist_comm s t]
        exact le_antisymm (hupper t s ht0 (lt_of_not_ge hs0)) (hlower t s)
      · simp only [ℓ, ite_eq_right hs0, ite_eq_right ht0]
        rw [hq.dist_eq]
        change |((-s).toNNReal : ℝ) - ((-t).toNNReal : ℝ)| = |s - t|
        rw [Real.coe_toNNReal _ (by linarith : 0 ≤ -s),
          Real.coe_toNNReal _ (by linarith : 0 ≤ -t)]
        change dist (-s) (-t) = dist s t
        exact dist_neg_neg s t
  · simpa [ℓ] using hr0

end DifferentialGeometry.Geometry.Comparison.Toponogov
