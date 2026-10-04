import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PantsCornerMaps
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.PlanarModels

/-!
# Topological lemmas for the K16f fold

Packet K16f, tier 2. `triangleSet` is the closed ideal triangle as a subset of `ℂ`
(`coe_mem_triangleSet_iff`). `exists_isPreconnected_path_top` joins every point of the
triangle outside the closed core disc `‖w - foldCenter‖ ≤ 1/10` to the point `1/4 + Y i`
(`Y ≥ 1`) by a preconnected set of at most three segments inside the triangle and outside the
disc. The open upper half `foldPantsUpper` of the open pants is preconnected
(`isPreconnected_foldPantsUpper`: vertical segments up to the arc `|u| = 5/2`, or radial segments
down to it). `image_mem_nhds_of_det_ne_zero` is the inverse function theorem in the form used
for openness of the image.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff Topology

namespace GC.Seifert

def triangleSet : Set ℂ :=
  {w | 0 < w.im ∧ 0 ≤ w.re ∧ w.re ≤ 1 / 2 ∧ 0 ≤ wallTwo w.re w.im}

def foldPantsUpper : Set ℂ := {u | planarFunction 3 u < 0 ∧ 0 < u.im}

theorem coe_mem_triangleSet_iff (z : UpperHalfPlane) :
    (z : ℂ) ∈ triangleSet ↔ z ∈ idealTriangle := by
  rw [mem_idealTriangle_iff]
  constructor
  · rintro ⟨-, h0, h1, h2⟩ i
    fin_cases i
    · exact h0
    · change 0 ≤ 1 / 2 - (z : ℂ).re
      linarith
    · change 0 ≤ wallSide 2 z
      rw [wallSide_two]
      exact h2
  · intro h
    refine ⟨z.im_pos, h 0, ?_, ?_⟩
    · have := h 1
      change 0 ≤ 1 / 2 - z.re at this
      change z.re ≤ 1 / 2
      linarith
    · have := h 2
      rw [wallSide_two] at this
      exact this

theorem norm_sub_foldCenter_sq (w : ℂ) :
    ‖w - foldCenter‖ ^ 2 = (w.re - 1 / 4) ^ 2 + (w.im - 37 / 100) ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [foldCenter]
  ring

theorem one_tenth_lt_norm_iff (w : ℂ) :
    1 / 10 < ‖w - foldCenter‖ ↔ 1 / 100 < (w.re - 1 / 4) ^ 2 + (w.im - 37 / 100) ^ 2 := by
  rw [← norm_sub_foldCenter_sq, show (1 / 100 : ℝ) = (1 / 10) ^ 2 by norm_num]
  exact (sq_lt_sq₀ (by norm_num) (norm_nonneg _)).symm

private def vSeg (x a b : ℝ) : Set ℂ := (fun t : ℝ => (x : ℂ) + (t : ℂ) * Complex.I) '' Set.Icc a b

private def hSeg (y a b : ℝ) : Set ℂ := (fun s : ℝ => (s : ℂ) + (y : ℂ) * Complex.I) '' Set.uIcc a b

private theorem isPreconnected_vSeg (x a b : ℝ) : IsPreconnected (vSeg x a b) :=
  isPreconnected_Icc.image _ (by fun_prop)

private theorem isPreconnected_hSeg (y a b : ℝ) : IsPreconnected (hSeg y a b) :=
  isPreconnected_uIcc.image _ (by fun_prop)

private theorem mem_vSeg {x a b : ℝ} {w : ℂ} (hw : w ∈ vSeg x a b) :
    w.re = x ∧ a ≤ w.im ∧ w.im ≤ b := by
  obtain ⟨t, ⟨ht1, ht2⟩, rfl⟩ := hw
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Complex.add_im,
    Complex.mul_im, zero_add]
  exact ⟨trivial, ht1, ht2⟩

private theorem mem_hSeg {y a b : ℝ} {w : ℂ} (hw : w ∈ hSeg y a b) :
    w.im = y ∧ min a b ≤ w.re ∧ w.re ≤ max a b := by
  obtain ⟨s, ⟨hs1, hs2⟩, rfl⟩ := hw
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, Complex.add_im,
    Complex.mul_im, zero_add]
  exact ⟨trivial, hs1, hs2⟩

private theorem start_mem_vSeg (x a b : ℝ) (h : a ≤ b) :
    (x : ℂ) + (a : ℂ) * Complex.I ∈ vSeg x a b := ⟨a, ⟨le_rfl, h⟩, rfl⟩

private theorem end_mem_vSeg (x a b : ℝ) (h : a ≤ b) :
    (x : ℂ) + (b : ℂ) * Complex.I ∈ vSeg x a b := ⟨b, ⟨h, le_rfl⟩, rfl⟩

private theorem left_mem_hSeg (y a b : ℝ) : (a : ℂ) + (y : ℂ) * Complex.I ∈ hSeg y a b :=
  ⟨a, Set.left_mem_uIcc, rfl⟩

private theorem right_mem_hSeg (y a b : ℝ) : (b : ℂ) + (y : ℂ) * Complex.I ∈ hSeg y a b :=
  ⟨b, Set.right_mem_uIcc, rfl⟩

private theorem eq_re_add_im (w : ℂ) : w = (w.re : ℂ) + (w.im : ℂ) * Complex.I :=
  (Complex.re_add_im w).symm

theorem exists_isPreconnected_path_top {z : ℂ} (hz : z ∈ triangleSet)
    (hout : 1 / 10 < ‖z - foldCenter‖) {Y : ℝ} (hY1 : 1 ≤ Y) (hYz : z.im ≤ Y) :
    ∃ P : Set ℂ, IsPreconnected P ∧ z ∈ P ∧
      ((1 / 4 : ℝ) : ℂ) + (Y : ℂ) * Complex.I ∈ P ∧ P ⊆ triangleSet ∧
        ∀ w ∈ P, 1 / 10 < ‖w - foldCenter‖ := by
  obtain ⟨hy, hx0, hx1, hw⟩ := hz
  rw [one_tenth_lt_norm_iff] at hout
  unfold wallTwo at hw
  have htop : ∀ w : ℂ, w.im = Y → 0 ≤ w.re → w.re ≤ 1 / 2 →
      w ∈ triangleSet ∧ 1 / 10 < ‖w - foldCenter‖ := by
    intro w hwY h0 h1
    refine ⟨⟨by rw [hwY]; linarith, h0, h1, ?_⟩, ?_⟩
    · unfold wallTwo
      rw [hwY]
      nlinarith
    · rw [one_tenth_lt_norm_iff, hwY]
      nlinarith
  rcases le_or_gt (37 / 100) z.im with hzi | hzi
  · refine ⟨vSeg z.re z.im Y ∪ hSeg Y z.re (1 / 4),
      (isPreconnected_vSeg _ _ _).union _ (end_mem_vSeg _ _ _ hYz) (left_mem_hSeg _ _ _)
        (isPreconnected_hSeg _ _ _), Or.inl ?_, Or.inr (right_mem_hSeg _ _ _), ?_, ?_⟩
    · rw [eq_re_add_im z]
      simpa using start_mem_vSeg z.re z.im Y hYz
    · rintro w (hwv | hwh)
      · obtain ⟨hre, h1, h2⟩ := mem_vSeg hwv
        refine ⟨by linarith, by rw [hre]; exact hx0, by rw [hre]; exact hx1, ?_⟩
        unfold wallTwo
        rw [hre]
        nlinarith
      · obtain ⟨him, h1, h2⟩ := mem_hSeg hwh
        exact (htop w him (le_trans (le_min hx0 (by norm_num)) h1)
          (le_trans h2 (max_le hx1 (by norm_num)))).1
    · rintro w (hwv | hwh)
      · obtain ⟨hre, h1, h2⟩ := mem_vSeg hwv
        rw [one_tenth_lt_norm_iff, hre]
        nlinarith
      · obtain ⟨him, h1, h2⟩ := mem_hSeg hwh
        exact (htop w him (le_trans (le_min hx0 (by norm_num)) h1)
          (le_trans h2 (max_le hx1 (by norm_num)))).2
  · rcases le_total z.re (1 / 4) with hzr | hzr
    · refine ⟨hSeg z.im z.re 0 ∪ (vSeg 0 z.im Y ∪ hSeg Y 0 (1 / 4)), ?_, Or.inl ?_,
        Or.inr (Or.inr (right_mem_hSeg _ _ _)), ?_, ?_⟩
      · refine (isPreconnected_hSeg _ _ _).union ((0 : ℝ) + (z.im : ℂ) * Complex.I)
          (right_mem_hSeg _ _ _) (Or.inl (start_mem_vSeg _ _ _ hYz)) ?_
        exact (isPreconnected_vSeg _ _ _).union _ (end_mem_vSeg _ _ _ hYz) (left_mem_hSeg _ _ _)
          (isPreconnected_hSeg _ _ _)
      · have h := left_mem_hSeg z.im z.re (0 : ℝ)
        rwa [← eq_re_add_im z] at h
      · rintro w (hwh | hwv | hwh)
        · obtain ⟨him, h1, h2⟩ := mem_hSeg hwh
          rw [min_eq_right hx0] at h1
          rw [max_eq_left hx0] at h2
          refine ⟨by rw [him]; exact hy, h1, by linarith, ?_⟩
          unfold wallTwo
          rw [him]
          nlinarith
        · obtain ⟨hre, h1, h2⟩ := mem_vSeg hwv
          refine ⟨by linarith, by rw [hre], by rw [hre]; norm_num, ?_⟩
          unfold wallTwo
          rw [hre]
          nlinarith
        · obtain ⟨him, h1, h2⟩ := mem_hSeg hwh
          exact (htop w him (le_trans (by norm_num) h1) (le_trans h2 (by norm_num))).1
      · rintro w (hwh | hwv | hwh)
        · obtain ⟨him, h1, h2⟩ := mem_hSeg hwh
          rw [min_eq_right hx0] at h1
          rw [max_eq_left hx0] at h2
          rw [one_tenth_lt_norm_iff, him]
          nlinarith
        · obtain ⟨hre, h1, h2⟩ := mem_vSeg hwv
          rw [one_tenth_lt_norm_iff, hre]
          nlinarith
        · obtain ⟨him, h1, h2⟩ := mem_hSeg hwh
          exact (htop w him (le_trans (by norm_num) h1) (le_trans h2 (by norm_num))).2
    · refine ⟨hSeg z.im z.re (1 / 2) ∪ (vSeg (1 / 2) z.im Y ∪ hSeg Y (1 / 2) (1 / 4)), ?_,
        Or.inl ?_, Or.inr (Or.inr (right_mem_hSeg _ _ _)), ?_, ?_⟩
      · refine (isPreconnected_hSeg _ _ _).union (((1 / 2 : ℝ) : ℂ) + (z.im : ℂ) * Complex.I)
          (right_mem_hSeg _ _ _) (Or.inl (start_mem_vSeg _ _ _ hYz)) ?_
        exact (isPreconnected_vSeg _ _ _).union _ (end_mem_vSeg _ _ _ hYz) (left_mem_hSeg _ _ _)
          (isPreconnected_hSeg _ _ _)
      · have h := left_mem_hSeg z.im z.re (1 / 2 : ℝ)
        rwa [← eq_re_add_im z] at h
      · rintro w (hwh | hwv | hwh)
        · obtain ⟨him, h1, h2⟩ := mem_hSeg hwh
          rw [min_eq_left hx1] at h1
          rw [max_eq_right hx1] at h2
          refine ⟨by rw [him]; exact hy, by linarith, h2, ?_⟩
          unfold wallTwo
          rw [him]
          nlinarith
        · obtain ⟨hre, h1, h2⟩ := mem_vSeg hwv
          refine ⟨by linarith, by rw [hre]; norm_num, by rw [hre], ?_⟩
          unfold wallTwo
          rw [hre]
          nlinarith
        · obtain ⟨him, h1, h2⟩ := mem_hSeg hwh
          exact (htop w him (le_trans (by norm_num) h1) (le_trans h2 (by norm_num))).1
      · rintro w (hwh | hwv | hwh)
        · obtain ⟨him, h1, h2⟩ := mem_hSeg hwh
          rw [min_eq_left hx1] at h1
          rw [max_eq_right hx1] at h2
          rw [one_tenth_lt_norm_iff, him]
          nlinarith
        · obtain ⟨hre, h1, h2⟩ := mem_vSeg hwv
          rw [one_tenth_lt_norm_iff, hre]
          nlinarith
        · obtain ⟨him, h1, h2⟩ := mem_hSeg hwh
          exact (htop w him (le_trans (by norm_num) h1) (le_trans h2 (by norm_num))).2

theorem image_mem_nhds_of_det_ne_zero {F : ℂ → ℂ} {z : ℂ} {s : Set ℂ} (hs : s ∈ 𝓝 z)
    (hF : ContDiffAt ℝ ∞ F z) (hdet : (fderiv ℝ F z).det ≠ 0) : F '' s ∈ 𝓝 (F z) := by
  have hstrict := hF.hasStrictFDerivAt (by decide)
  have hrange : LinearMap.range (fderiv ℝ F z : ℂ →ₗ[ℝ] ℂ) = ⊤ := by
    have hu : IsUnit ((fderiv ℝ F z) : ℂ →ₗ[ℝ] ℂ) :=
      (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet)
    exact (LinearMap.isUnit_iff_range_eq_top _).1 hu
  rw [← hstrict.map_nhds_eq_of_surj hrange]
  exact Filter.image_mem_map hs

theorem planarFunction_three_neg_iff (u : ℂ) : planarFunction 3 u < 0 ↔
    ‖u‖ < 3 ∧ 1 / 2 < ‖u - 3 / 2‖ ∧ 1 / 2 < ‖u + 3 / 2‖ := by
  have e1 : u - (((3 / 2 : ℝ)) : ℂ) = u - 3 / 2 := by push_cast; ring
  have e2 : u - (((-(3 / 2) : ℝ)) : ℂ) = u + 3 / 2 := by push_cast; ring
  rw [planarFunction_three, e1, e2]
  have hsep : 3 ≤ ‖u - 3 / 2‖ + ‖u + 3 / 2‖ := by
    have := norm_sub_le (u + 3 / 2) (u - 3 / 2)
    have h3 : (u + 3 / 2) - (u - 3 / 2) = 3 := by ring
    rw [h3] at this
    have h4 : ‖(3 : ℂ)‖ = 3 := by norm_num
    linarith
  have t1 : ‖u‖ ≤ ‖u - 3 / 2‖ + 3 / 2 := by
    have := norm_add_le (u - 3 / 2) (3 / 2 : ℂ)
    have h4 : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by norm_num
    simp only [sub_add_cancel] at this
    linarith
  have t2 : ‖u‖ ≤ ‖u + 3 / 2‖ + 3 / 2 := by
    have := norm_sub_le (u + 3 / 2) (3 / 2 : ℂ)
    have h4 : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by norm_num
    simp only [add_sub_cancel_right] at this
    linarith
  have hn := norm_nonneg u
  have ha := norm_nonneg (u - 3 / 2)
  have hb := norm_nonneg (u + 3 / 2)
  constructor
  · intro h
    by_contra hc
    simp only [not_and_or, not_lt] at hc
    rcases hc with hc | hc | hc
    · have h1 : 0 ≤ ‖u‖ ^ 2 - 3 ^ 2 := by nlinarith
      have h2' : 3 / 2 ≤ ‖u - 3 / 2‖ := by linarith
      have h3' : 3 / 2 ≤ ‖u + 3 / 2‖ := by linarith
      have h2 : 0 < ‖u - 3 / 2‖ ^ 2 - (1 / 2) ^ 2 := by nlinarith
      have h3 : 0 < ‖u + 3 / 2‖ ^ 2 - (1 / 2) ^ 2 := by nlinarith
      have := mul_nonneg h1 (mul_pos h2 h3).le
      linarith
    · have h3' : 5 / 2 ≤ ‖u + 3 / 2‖ := by linarith
      have h1' : ‖u‖ ≤ 2 := by linarith
      have h2 : ‖u - 3 / 2‖ ^ 2 - (1 / 2) ^ 2 ≤ 0 := by nlinarith
      have h3 : 0 < ‖u + 3 / 2‖ ^ 2 - (1 / 2) ^ 2 := by nlinarith
      have h1 : ‖u‖ ^ 2 - 3 ^ 2 < 0 := by nlinarith
      have := mul_nonneg_of_nonpos_of_nonpos h1.le (mul_nonpos_of_nonpos_of_nonneg h2 h3.le)
      linarith
    · have h2' : 5 / 2 ≤ ‖u - 3 / 2‖ := by linarith
      have h1' : ‖u‖ ≤ 2 := by linarith
      have h3 : ‖u + 3 / 2‖ ^ 2 - (1 / 2) ^ 2 ≤ 0 := by nlinarith
      have h2 : 0 < ‖u - 3 / 2‖ ^ 2 - (1 / 2) ^ 2 := by nlinarith
      have h1 : ‖u‖ ^ 2 - 3 ^ 2 < 0 := by nlinarith
      have := mul_nonneg_of_nonpos_of_nonpos h1.le (mul_nonpos_of_nonneg_of_nonpos h2.le h3)
      linarith
  · rintro ⟨h1, h2, h3⟩
    have a1 : ‖u‖ ^ 2 - 3 ^ 2 < 0 := by nlinarith
    have a2 : 0 < ‖u - 3 / 2‖ ^ 2 - (1 / 2) ^ 2 := by nlinarith
    have a3 : 0 < ‖u + 3 / 2‖ ^ 2 - (1 / 2) ^ 2 := by nlinarith
    exact mul_neg_of_neg_of_pos a1 (mul_pos a2 a3)

private def arcSet : Set ℂ :=
  (fun θ : ℝ => ((5 / 2 : ℝ) : ℂ) * Complex.exp (θ * Complex.I)) '' Set.Ioo 0 Real.pi

private theorem isPreconnected_arcSet : IsPreconnected arcSet :=
  isPreconnected_Ioo.image _ (by fun_prop)

private theorem mem_arcSet {v : ℂ} (hv : ‖v‖ = 5 / 2) (him : 0 < v.im) : v ∈ arcSet := by
  refine ⟨Complex.arg v, ⟨lt_of_le_of_ne (Complex.arg_nonneg_iff.2 him.le) fun h => by
    have := Complex.arg_eq_zero_iff.1 h.symm
    linarith [this.2], ?_⟩, ?_⟩
  · exact lt_of_le_of_ne (Complex.arg_le_pi v) fun h => by
      have := Complex.arg_eq_pi_iff.1 h
      linarith [this.2]
  · change ((5 / 2 : ℝ) : ℂ) * Complex.exp ((Complex.arg v : ℂ) * Complex.I) = v
    rw [← hv]
    exact Complex.norm_mul_exp_arg_mul_I v

private theorem arcSet_subset : arcSet ⊆ foldPantsUpper := by
  rintro _ ⟨θ, ⟨h0, h1⟩, rfl⟩
  have hn : ‖((5 / 2 : ℝ) : ℂ) * Complex.exp (θ * Complex.I)‖ = 5 / 2 := by
    rw [norm_mul, Complex.norm_exp_ofReal_mul_I, Complex.norm_real]
    norm_num
  refine ⟨(planarFunction_three_neg_iff _).2 ⟨by rw [hn]; norm_num, ?_, ?_⟩, ?_⟩
  · have := norm_sub_le_norm_sub_add_norm_sub ((5 / 2 : ℝ) * Complex.exp (θ * Complex.I))
      (3 / 2 : ℂ) 0
    have h2 := norm_sub_norm_le (((5 / 2 : ℝ) : ℂ) * Complex.exp (θ * Complex.I)) (3 / 2 : ℂ)
    rw [hn] at h2
    have : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by norm_num
    linarith
  · have h2 := norm_sub_norm_le (((5 / 2 : ℝ) : ℂ) * Complex.exp (θ * Complex.I)) (-(3 / 2) : ℂ)
    rw [hn, sub_neg_eq_add] at h2
    have : ‖(-(3 / 2) : ℂ)‖ = 3 / 2 := by norm_num
    linarith
  · rw [Complex.mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    have := Real.sin_pos_of_pos_of_lt_pi h0 h1
    positivity

theorem isPreconnected_foldPantsUpper : IsPreconnected foldPantsUpper := by
  have hbase : ((5 / 2 : ℝ) : ℂ) * Complex.exp ((Real.pi / 2 : ℝ) * Complex.I) ∈ arcSet :=
    ⟨Real.pi / 2, ⟨by positivity, by linarith [Real.pi_pos]⟩, rfl⟩
  refine isPreconnected_of_forall (((5 / 2 : ℝ) : ℂ) * Complex.exp ((Real.pi / 2 : ℝ) * Complex.I))
    fun u hu => ?_
  obtain ⟨hp, him⟩ := hu
  obtain ⟨hn3, hh1, hh2⟩ := (planarFunction_three_neg_iff u).1 hp
  have hu0 : 0 < ‖u‖ := by
    rw [norm_pos_iff]
    rintro rfl
    simp at him
  rcases le_or_gt (5 / 2) ‖u‖ with hbig | hsmall
  · let seg := (fun t : ℝ => (t : ℂ) * u) '' Set.Icc ((5 / 2) / ‖u‖) 1
    have hk : (5 / 2) / ‖u‖ ≤ 1 := (div_le_one hu0).2 hbig
    refine ⟨seg ∪ arcSet, ?_, Or.inr hbase, Or.inl ⟨1, ⟨hk, le_rfl⟩, by simp⟩,
      (isPreconnected_Icc.image _ (by fun_prop)).union _ ⟨(5 / 2) / ‖u‖, ⟨le_rfl, hk⟩, rfl⟩
        (mem_arcSet ?_ ?_) isPreconnected_arcSet⟩
    · rintro w (⟨t, ⟨ht1, ht2⟩, rfl⟩ | hw)
      · have ht0 : 0 < t := lt_of_lt_of_le (by positivity) ht1
        have hnt : ‖(t : ℂ) * u‖ = t * ‖u‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]
        have hlo : 5 / 2 ≤ t * ‖u‖ := by rwa [div_le_iff₀ hu0] at ht1
        have hhi : t * ‖u‖ ≤ ‖u‖ := by nlinarith
        refine ⟨(planarFunction_three_neg_iff _).2 ⟨by rw [hnt]; linarith, ?_, ?_⟩, ?_⟩
        · have h2 := norm_sub_norm_le ((t : ℂ) * u) (3 / 2 : ℂ)
          have : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by norm_num
          rw [hnt] at h2
          linarith
        · have h2 := norm_sub_norm_le ((t : ℂ) * u) (-(3 / 2) : ℂ)
          rw [sub_neg_eq_add] at h2
          have : ‖(-(3 / 2) : ℂ)‖ = 3 / 2 := by norm_num
          rw [hnt] at h2
          linarith
        · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
          positivity
      · exact arcSet_subset hw
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      field_simp
    · simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
      positivity
  · have hre : |u.re| < 5 / 2 := by
      have := Complex.abs_re_le_norm u
      linarith
    have hq : 0 < 25 / 4 - u.re ^ 2 := by
      have := sq_lt_sq' (abs_lt.1 hre).1 (abs_lt.1 hre).2
      nlinarith
    set T := Real.sqrt (25 / 4 - u.re ^ 2)
    have hT2 : T ^ 2 = 25 / 4 - u.re ^ 2 := Real.sq_sqrt hq.le
    have hT0 : 0 < T := Real.sqrt_pos.2 hq
    have hnu : ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    have hiT : u.im < T := by nlinarith
    let seg := (fun t : ℝ => (u.re : ℂ) + (t : ℂ) * Complex.I) '' Set.Icc u.im T
    have hend : (u.re : ℂ) + (T : ℂ) * Complex.I ∈ arcSet := by
      apply mem_arcSet
      · have : ‖(u.re : ℂ) + (T : ℂ) * Complex.I‖ ^ 2 = (5 / 2) ^ 2 := by
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp
          nlinarith
        exact (sq_eq_sq₀ (norm_nonneg _) (by norm_num)).1 this
      · simpa using hT0
    refine ⟨seg ∪ arcSet, ?_, Or.inr hbase, Or.inl ⟨u.im, ⟨le_rfl, hiT.le⟩, ?_⟩,
      (isPreconnected_Icc.image _ (by fun_prop)).union _ ⟨T, ⟨hiT.le, le_rfl⟩, rfl⟩ hend
        isPreconnected_arcSet⟩
    · rintro w (⟨t, ⟨ht1, ht2⟩, rfl⟩ | hw)
      · have hw2 : ∀ c : ℝ, ‖(u.re : ℂ) + (t : ℂ) * Complex.I - c‖ ^ 2 =
            (u.re - c) ^ 2 + t ^ 2 := by
          intro c
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp
          ring
        have hu2 : ∀ c : ℝ, ‖u - c‖ ^ 2 = (u.re - c) ^ 2 + u.im ^ 2 := by
          intro c
          rw [Complex.sq_norm, Complex.normSq_apply]
          simp
          ring
        refine ⟨(planarFunction_three_neg_iff _).2 ⟨?_, ?_, ?_⟩, ?_⟩
        · have h0 := hw2 0
          simp only [Complex.ofReal_zero, sub_zero] at h0
          have : ‖(u.re : ℂ) + (t : ℂ) * Complex.I‖ ^ 2 < 3 ^ 2 := by nlinarith
          exact (sq_lt_sq₀ (norm_nonneg _) (by norm_num)).1 this
        · have h0 := hw2 (3 / 2)
          have h1 := hu2 (3 / 2)
          push_cast at h0 h1
          have : (1 / 2) ^ 2 < ‖(u.re : ℂ) + (t : ℂ) * Complex.I - 3 / 2‖ ^ 2 := by nlinarith
          exact (sq_lt_sq₀ (by norm_num) (norm_nonneg _)).1 this
        · have h0 := hw2 (-(3 / 2))
          have h1 := hu2 (-(3 / 2))
          push_cast at h0 h1
          rw [sub_neg_eq_add] at h0 h1
          have : (1 / 2) ^ 2 < ‖(u.re : ℂ) + (t : ℂ) * Complex.I + 3 / 2‖ ^ 2 := by nlinarith
          exact (sq_lt_sq₀ (by norm_num) (norm_nonneg _)).1 this
        · simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
            Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add]
          linarith
      · exact arcSet_subset hw
    · exact Complex.re_add_im u

end GC.Seifert
