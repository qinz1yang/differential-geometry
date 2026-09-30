import DifferentialGeometry.Geometry.Metric.Approximation.KleinerLottApproximation
import DifferentialGeometry.Geometry.Metric.Scaling.Rescale

set_option autoImplicit false

open Set Metric

namespace GC.MetricGeometry.KleinerLottApprox

variable {X : Type*} [mX : MetricSpace X] {p : X} {C L s δ c : ℝ}

noncomputable def recenterRescaleInterval (hC : 0 ≤ C)
    (f : KleinerLottApprox p (⟨0, le_rfl, hC⟩ : Icc (0 : ℝ) C) s)
    (a : X) (hc : 0 < c) (hδ : 0 < δ) (hδone : δ < 1)
    (hCL : c * C ≤ L)
    (hdomain : dist a p + δ⁻¹ / c + 2 * s ≤ s⁻¹)
    (hradial : c * (dist a p + 3 * s) ≤ δ)
    (hdistortion : c * s + 2 * (c * (f.toFun a).val) ≤ δ)
    (hcoverage : L - c * C + 2 * c * s + c * (f.toFun a).val ≤ δ) :
    letI : MetricSpace X := mX.rescale c hc
    KleinerLottApprox a
      (⟨0, le_rfl, (mul_nonneg hc.le hC).trans hCL⟩ : Icc (0 : ℝ) L) δ := by
  classical
  have hs := f.error_pos
  have hi : 0 < δ⁻¹ / c := div_pos (inv_pos.mpr hδ) hc
  have hL : 0 ≤ L := (mul_nonneg hc.le hC).trans hCL
  let F : X → Icc (0 : ℝ) L := fun x =>
    if x = a then ⟨0, le_rfl, hL⟩ else
      ⟨c * (f.toFun x).val, mul_nonneg hc.le (f.toFun x).property.1,
        (mul_le_mul_of_nonneg_left (f.toFun x).property.2 hc.le).trans hCL⟩
  have hF (x : X) : dist (F x).val (c * (f.toFun x).val) ≤ c * (f.toFun a).val := by
    by_cases hx : x = a
    · subst x
      simp only [F, ite_true, Real.dist_eq, zero_sub, abs_neg,
        abs_of_nonneg (mul_nonneg hc.le (f.toFun a).property.1), le_refl]
    · simp only [F, ite_eq_right hx, dist_self]
      exact mul_nonneg hc.le (f.toFun a).property.1
  have hin (x : X) (hx : c * dist x a < δ⁻¹) : x ∈ ball p s⁻¹ := by
    have hh : dist x a < δ⁻¹ / c := (lt_div_iff₀ hc).mpr (by nlinarith)
    have ht := dist_triangle x a p
    change dist x p < _
    linarith
  have hscaled (x y : X) :
      dist (c * (f.toFun x).val) (c * (f.toFun y).val) = c * dist (f.toFun x) (f.toFun y) := by
    rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hc, Subtype.dist_eq, Real.dist_eq]
  have hd (x y : X) (hx : c * dist x a < δ⁻¹) (hy : c * dist y a < δ⁻¹) :
      |dist (F x) (F y) - c * dist x y| ≤ δ := by
    have hpair := dist_dist_dist_le (F x).val (F y).val (c * (f.toFun x).val) (c * (f.toFun y).val)
    rw [hscaled x y, Real.dist_eq] at hpair
    have horig := f.distortion x (hin x hx) y (hin y hy)
    have hmul : |c * dist (f.toFun x) (f.toFun y) - c * dist x y| ≤ c * s := by
      rw [← mul_sub, abs_mul, abs_of_pos hc]
      exact mul_le_mul_of_nonneg_left horig hc.le
    have ht := abs_add_le (dist (F x) (F y) - c * dist (f.toFun x) (f.toFun y))
      (c * dist (f.toFun x) (f.toFun y) - c * dist x y)
    rw [sub_add_sub_cancel] at ht
    change |dist (F x) (F y) - c * dist (f.toFun x) (f.toFun y)| ≤
      dist (F x).val (c * (f.toFun x).val) + dist (F y).val (c * (f.toFun y).val) at hpair
    linarith [hF x, hF y]
  have hcover (y : Icc (0 : ℝ) L) (hy : y.val < δ⁻¹ - δ) :
      ∃ x : X, c * dist x a < δ⁻¹ ∧ dist y (F x) ≤ δ := by
    let z : Icc (0 : ℝ) C := ⟨min (y.val / c) C,
      le_min (div_nonneg y.property.1 hc.le) hC, min_le_right _ _⟩
    have hz0 : 0 ≤ z.val := z.property.1
    have hzy : c * z.val ≤ y.val := by
      have hh := min_le_left (y.val / c) C
      simpa only [mul_comm] using (le_div_iff₀ hc).mp hh
    have hcz : c * z.val = min y.val (c * C) := by
      dsimp [z]
      rw [mul_min_of_nonneg _ _ hc.le, mul_div_cancel₀ _ hc.ne']
    have hgap : dist y.val (c * z.val) ≤ L - c * C := by
      rw [Real.dist_eq, abs_of_nonneg (sub_nonneg.mpr hzy), hcz]
      by_cases h : y.val ≤ c * C
      · rw [min_eq_left h]; linarith
      · rw [min_eq_right (le_of_not_ge h)]; linarith [y.property.2]
    have hzrad : dist z (⟨0, le_rfl, hC⟩ : Icc (0 : ℝ) C) = z.val := by
      rw [Subtype.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg hz0]
    have hzbound : z.val < s⁻¹ - s := by
      have hz' : z.val < δ⁻¹ / c := by
        apply (lt_div_iff₀ hc).mpr
        nlinarith
      linarith [dist_nonneg (x := a) (y := p)]
    obtain ⟨x, hx, hxf⟩ := f.coverage_witness z (by rwa [hzrad])
    have hrad := (abs_le.mp (f.radial_error x hx)).1
    have htri := dist_triangle (f.toFun x) z (⟨0, le_rfl, hC⟩ : Icc (0 : ℝ) C)
    rw [dist_comm (f.toFun x) z, hzrad] at htri
    have hsource : c * dist x a < δ⁻¹ := by
      have hxa := dist_triangle x p a
      rw [dist_comm p a] at hxa
      nlinarith [mul_lt_mul_of_pos_left hxf hc, mul_le_mul_of_nonneg_left hrad hc.le,
        mul_le_mul_of_nonneg_left htri hc.le, mul_le_mul_of_nonneg_left hxa hc.le]
    have hscalederror : dist (c * z.val) (c * (f.toFun x).val) < 2 * c * s := by
      rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos hc]
      change |z.val - (f.toFun x).val| < 2 * s at hxf
      nlinarith [mul_lt_mul_of_pos_left hxf hc]
    have htarget : dist y (F x) ≤ δ := by
      have ht1 := dist_triangle y.val (c * z.val) (c * (f.toFun x).val)
      have ht2 := dist_triangle y.val (c * (f.toFun x).val) (F x).val
      rw [dist_comm (c * (f.toFun x).val) (F x).val] at ht2
      change dist y.val (F x).val ≤ δ
      linarith [hF x]
    exact ⟨x, hsource, htarget⟩
  letI : MetricSpace X := mX.rescale c hc
  refine ⟨hδ, hδone, F, ?_, ?_, ?_⟩
  · simp only [F, ite_true]
  · exact fun x hx y hy => hd x y hx hy
  · intro y hy
    have hyr : y.val < δ⁻¹ - δ := by
      simpa only [Subtype.dist_eq, Real.dist_eq, sub_zero, abs_of_nonneg y.property.1] using hy
    obtain ⟨x, hx, hd⟩ := hcover y hyr
    exact (infDist_le_dist_of_mem (show F x ∈ F '' ball a δ⁻¹ from ⟨x, hx, rfl⟩)).trans hd


theorem recenterRescaleInterval_apply (hC : 0 ≤ C)
    (f : KleinerLottApprox p (⟨0, le_rfl, hC⟩ : Icc (0 : ℝ) C) s)
    (a : X) (hc : 0 < c) (hδ : 0 < δ) (hδone : δ < 1)
    (hCL : c * C ≤ L)
    (hdomain : dist a p + δ⁻¹ / c + 2 * s ≤ s⁻¹)
    (hradial : c * (dist a p + 3 * s) ≤ δ)
    (hdistortion : c * s + 2 * (c * (f.toFun a).val) ≤ δ)
    (hcoverage : L - c * C + 2 * c * s + c * (f.toFun a).val ≤ δ) (x : X) :
    letI : Decidable (x = a) := Classical.propDecidable _
    let value := c * (f.toFun x).val
    let g := f.recenterRescaleInterval hC a hc hδ hδone hCL hdomain hradial hdistortion hcoverage
    letI : MetricSpace X := mX.rescale c hc
    (g.toFun x).val = if x = a then 0 else value := by
  classical
  dsimp only
  by_cases hx : x = a
  · simp only [recenterRescaleInterval, hx, ite_true]
  · simp only [recenterRescaleInterval, ite_eq_right hx]

variable {H : ℝ}

theorem exists_recenterRescaleInterval_strict (hC : 0 ≤ C)
    (f : KleinerLottApprox p (⟨0, le_rfl, hC⟩ : Icc (0 : ℝ) C) s)
    (a : X) (hc : 0 < c) (hδ : 0 < δ) (hδone : δ < 1)
    (hH : H ≤ C) (hclose : H * (1 - c) ≤ δ / 100)
    (hdomain : dist a p + δ⁻¹ / c + 2 * s ≤ s⁻¹)
    (hbudget : 2 * c * dist a p + 3 * c * s ≤ δ / 2) :
    let values := fun x => c * (f.toFun x).val
    let : MetricSpace X := mX.rescale c hc
    ∃ (L : ℝ) (hL : 0 ≤ L), H < L ∧ L = max (c * C) (H + δ / 100) ∧
      ∃ g : KleinerLottApprox a (⟨0, le_rfl, hL⟩ : Icc (0 : ℝ) L) δ,
        g.toFun a = ⟨0, le_rfl, hL⟩ ∧ ∀ x, x ≠ a → (g.toFun x).val = values x := by
  have hs := f.error_pos
  have hi : 0 < δ⁻¹ / c := div_pos (inv_pos.mpr hδ) hc
  have ha : a ∈ ball p s⁻¹ := by change dist a p < _; linarith
  have hfa : (f.toFun a).val ≤ dist a p + s := by
    have h := (abs_le.mp (f.radial_error a ha)).2
    simp only [Subtype.dist_eq, Real.dist_eq, sub_zero,
      abs_of_nonneg (f.toFun a).property.1] at h
    linarith
  let L := max (c * C) (H + δ / 100)
  have hL : 0 ≤ L := (mul_nonneg hc.le hC).trans (le_max_left _ _)
  have hLH : H < L := lt_of_lt_of_le (by linarith) (le_max_right _ _)
  have hLC : c * C ≤ L := le_max_left _ _
  have hgap : L - c * C ≤ δ / 50 := by
    dsimp [L]
    apply sub_le_iff_le_add.mpr
    apply max_le
    · linarith
    · nlinarith [mul_le_mul_of_nonneg_left hH hc.le]
  have hdist0 : 0 ≤ c * dist a p := mul_nonneg hc.le dist_nonneg
  have hfa' := mul_le_mul_of_nonneg_left hfa hc.le
  have hr : c * (dist a p + 3 * s) ≤ δ := by nlinarith
  have hd : c * s + 2 * (c * (f.toFun a).val) ≤ δ := by nlinarith
  have hcov : L - c * C + 2 * c * s + c * (f.toFun a).val ≤ δ := by nlinarith
  let g := f.recenterRescaleInterval hC a hc hδ hδone hLC hdomain hr hd hcov
  have hg (x : X) (hx : x ≠ a) :
      (@KleinerLottApprox.toFun X _ (mX.rescale c hc) inferInstance a
        (⟨0, le_rfl, hL⟩ : Icc (0 : ℝ) L) δ g x).val = c * (f.toFun x).val := by
    have h := f.recenterRescaleInterval_apply hC a hc hδ hδone hLC hdomain hr hd hcov x
    simpa only [ite_eq_right hx] using h
  let : MetricSpace X := mX.rescale c hc
  exact ⟨L, hL, hLH, rfl, g, g.basepoint, hg⟩

end GC.MetricGeometry.KleinerLottApprox
