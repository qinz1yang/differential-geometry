import DifferentialGeometry.Geometry.Metric.CloudCrossData

/-!
The horizontal truncated cloud has an explicit two-height error, while the small test at the
other centre is exactly vertical. These witnesses verify the actual affine-plane Hausdorff
conditions for the same compact cross and radius, without supplying planes at other points.
-/

set_option autoImplicit false

noncomputable section

open Set Metric

namespace GC.MetricGeometry.CloudCounterexample

theorem dist_realPart (z : ℂ) : dist z (z.re : ℂ) = |z.im| := by
  have heq : z - (z.re : ℂ) = (z.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  rw [dist_eq_norm, heq, norm_mul, Complex.norm_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs]

theorem cross_horizontal_test {δ : ℝ} (hδ : 0 < δ) :
    hausdorffEDist (crossSet δ ∩ ball (0 : ℂ) δ⁻¹)
      ((horizontalLine : Set ℂ) ∩ ball (0 : ℂ) δ⁻¹) ≤ ENNReal.ofReal (2 * crossHeight δ) := by
  obtain ⟨hh, hhδ, hh1, hs, hs1, hratio, hR, hha, hRa⟩ := cross_parameters hδ
  apply hausdorffEDist_le_of_mem_edist
  · intro z hz
    refine ⟨(z.re : ℂ), ⟨?_, ?_⟩, ?_⟩
    · exact (mem_horizontalLine).mpr (by simp)
    · rw [mem_ball, dist_zero_right]
      have hzn : ‖z‖ < δ⁻¹ := by simpa only [dist_zero_right] using mem_ball.mp hz.2
      have hre : ‖(z.re : ℂ)‖ ≤ ‖z‖ := by
        simpa only [Complex.norm_real, Real.norm_eq_abs] using Complex.abs_re_le_norm z
      exact hre.trans_lt hzn
    · apply (edist_le_ofReal (by positivity : 0 ≤ 2 * crossHeight δ)).mpr
      rw [dist_realPart]
      have him : |z.im| ≤ crossHeight δ := by
        rcases hz.1 with (hz | hz) | hz
        · rcases hz with ⟨t, ht, rfl⟩
          simp only [Complex.ofReal_im, abs_zero]
          exact hh.le
        · rcases hz with ⟨t, ht, rfl⟩
          simp only [Complex.ofReal_im, abs_zero]
          exact hh.le
        · rcases hz with ⟨t, ht, rfl⟩
          simpa only [crossPoint, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
            Complex.I_im, Complex.I_re, Complex.ofReal_re, mul_one, mul_zero, add_zero,
            zero_add] using abs_le.mpr ht
      linarith
  · intro z hz
    have hzim : z.im = 0 := (mem_horizontalLine (z := z)).mp hz.1
    have hzre : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hzim]
    have hzT : |z.re| < δ⁻¹ := by
      have h := hz.2
      rw [mem_ball, dist_zero_right, hzre, Complex.norm_real, Real.norm_eq_abs] at h
      exact h
    have hinterval : -crossExtent δ ≤ z.re ∧ z.re ≤ crossExtent δ := by
      dsimp only [crossExtent]
      constructor <;> linarith [(abs_lt.mp hzT).1, (abs_lt.mp hzT).2]
    by_cases hleft : z.re ≤ 3 / 4 - crossHeight δ
    · refine ⟨z, ⟨Or.inl (Or.inl ⟨z.re, ⟨hinterval.1, hleft⟩, hzre.symm⟩), hz.2⟩, ?_⟩
      simp
    · by_cases hright : 3 / 4 + crossHeight δ ≤ z.re
      · refine ⟨z, ⟨Or.inl (Or.inr ⟨z.re, ⟨hright, hinterval.2⟩, hzre.symm⟩), hz.2⟩, ?_⟩
        simp
      · refine ⟨((3 / 4 - crossHeight δ : ℝ) : ℂ), ⟨?_, ?_⟩, ?_⟩
        · refine Or.inl (Or.inl ⟨3 / 4 - crossHeight δ, ⟨?_, le_rfl⟩, rfl⟩)
          linarith
        · rw [mem_ball, dist_zero_right, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by linarith : 0 < 3 / 4 - crossHeight δ)]
          exact (lt_of_not_ge hleft).trans ((le_abs_self _).trans_lt hzT)
        · apply (edist_le_ofReal (by positivity : 0 ≤ 2 * crossHeight δ)).mpr
          rw [hzre, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
          apply abs_le.mpr
          constructor <;> linarith

theorem cross_vertical_test {δ : ℝ} (hδ : 0 < δ) :
    crossSet δ ∩ ball crossPoint (crossSmall δ / δ) =
      (AffineSubspace.mk' crossPoint verticalLine : Set ℂ) ∩
        ball crossPoint (crossSmall δ / δ) := by
  obtain ⟨hh, hhδ, hh1, hs, hs1, hratio, hR, hha, hRa⟩ := cross_parameters hδ
  ext z
  constructor
  · intro hz
    refine ⟨?_, hz.2⟩
    have hd : dist z crossPoint < crossHeight δ := (mem_ball.mp hz.2).trans hratio
    rcases hz.1 with (hz | hz) | hz
    · rcases hz with ⟨t, ht, rfl⟩
      have hnorm : dist (t : ℂ) crossPoint = |t - 3 / 4| := by
        simp only [crossPoint, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs]
      rw [hnorm] at hd
      have h := (abs_lt.mp hd).1
      linarith [ht.2]
    · rcases hz with ⟨t, ht, rfl⟩
      have hnorm : dist (t : ℂ) crossPoint = |t - 3 / 4| := by
        simp only [crossPoint, dist_eq_norm, ← Complex.ofReal_sub, Complex.norm_real,
          Real.norm_eq_abs]
      rw [hnorm] at hd
      have h := (abs_lt.mp hd).2
      linarith [ht.1]
    · rcases hz with ⟨t, ht, rfl⟩
      apply AffineSubspace.mem_mk'.mpr
      change crossPoint + (t : ℂ) * Complex.I - crossPoint ∈ verticalLine
      rw [mem_verticalLine]
      simp [crossPoint]
  · intro hz
    refine ⟨Or.inr ⟨z.im, ?_, ?_⟩, hz.2⟩
    · have him : |z.im| < crossHeight δ := by
        have h := Complex.abs_im_le_norm (z - crossPoint)
        simp only [Complex.sub_im, crossPoint, Complex.ofReal_im, sub_zero] at h
        have hd : ‖z - crossPoint‖ < crossHeight δ := by
          simpa only [dist_eq_norm] using (mem_ball.mp hz.2).trans hratio
        exact h.trans_lt hd
      exact ⟨(abs_lt.mp him).1.le, (abs_lt.mp him).2.le⟩
    · apply Complex.ext <;> simp [crossPoint]
      have h := (mem_verticalLine (z := z - crossPoint)).mp (AffineSubspace.mem_mk'.mp hz.1)
      simp only [Complex.sub_re, crossPoint, Complex.ofReal_re] at h
      linarith

theorem cross_cloud_tests {δ : ℝ} (hδ : 0 < δ) :
    (∀ x : crossCentres, Module.finrank ℝ (crossPlane x) = 1) ∧
      ∀ x : crossCentres,
        hausdorffEDist (crossSet δ ∩ ball (x : ℂ) (crossRadius δ x / δ))
          ((AffineSubspace.mk' (x : ℂ) (crossPlane x) : Set ℂ) ∩
            ball (x : ℂ) (crossRadius δ x / δ)) ≤ ENNReal.ofReal (δ * crossRadius δ x) := by
  refine ⟨crossPlane_finrank, ?_⟩
  intro x
  have hx := x.property
  simp only [crossCentres, mem_insert_iff, mem_singleton_iff] at hx
  rcases hx with hx | hx
  · have hline : (AffineSubspace.mk' (0 : ℂ) horizontalLine : Set ℂ) = horizontalLine := by
      ext z
      simp only [AffineSubspace.mem_mk', vsub_eq_sub, sub_zero, SetLike.mem_coe]
    have hheight := (cross_parameters hδ).2.1
    have hplane : crossPlane x = horizontalLine := by simp [crossPlane, hx]
    rw [hplane, hx, crossRadius_zero hδ, one_div, mul_one, hline]
    exact (cross_horizontal_test hδ).trans
      (ENNReal.ofReal_le_ofReal (by linarith : 2 * crossHeight δ ≤ δ))
  · have hp : crossPoint ≠ (0 : ℂ) := by norm_num [crossPoint]
    have hplane : crossPlane x = verticalLine := by simp [crossPlane, hx, hp]
    rw [hplane, hx, crossRadius_point hδ]
    rw [cross_vertical_test hδ, hausdorffEDist_self]
    exact bot_le

end GC.MetricGeometry.CloudCounterexample
