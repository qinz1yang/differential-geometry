import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryFlatPatches

/-!
# Wall images and the sign of the fold on a flat triangle

Lane B3 (design `docs/geometrization/handoffs/20261004-design-b3-closed-triangle-assembly.md`,
§3 step 3, with review 27: the image domains of the certificate). For a fold datum `D` on a flat
triangle `σ` the fold is real on the walls (`im_f_of_wall`), `f v₁ = 3/2`, `f v₂ = -3/2`, and the
open walls go to the three disjoint real segments: wall `1` (from `0` to `v₁`) into `(3/2, 7/2)`,
wall `0` (from `0` to `v₂`) into `(-7/2, -3/2)`, wall `2` (from `v₁` to `v₂`) into `(-3/2, 3/2)`
(`re_f_wallOne`, `re_f_wallZero`, `re_f_wallTwo`; intermediate value argument on the open segments,
anchored by the outer and apex germs). By the open mapping property at points of positive
Jacobian, `Im f > 0` on the open triangle (`im_f_pos_of_intT`), hence `Im f < 0` on the part of a
patch outside the triangle.
-/

set_option autoImplicit false

noncomputable section
open Set Complex Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace ClosedTriangle

open TwoConeFold

variable {σ : EuclidShape} (D : σ.toCompactShape.FoldData)

theorem im_f_of_wall {i : Fin 3} {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide i z = 0)
    (h0 : z ≠ 0) : (D.f z).im = 0 := by
  have hV : z ∈ D.V i := foldWall_diff_subset_V' D i ⟨⟨hz, hw⟩, h0⟩
  have h := f_refl' D i hV
  rw [σ.refl_of_wallSide_eq_zero hw] at h
  exact Complex.conj_eq_iff_im.1 h.symm

omit D in
theorem vertexOne_ne_zero : σ.vertexOne ≠ 0 := by
  intro h
  have := congrArg norm h
  rw [σ.norm_vertexOne, norm_zero] at this
  exact σ.sin_θ₂_pos.ne' this

omit D in
theorem vertexTwo_ne_zero : σ.vertexTwo ≠ 0 := by
  intro h
  have := congrArg norm h
  rw [σ.norm_vertexTwo, norm_zero] at this
  exact σ.sin_θ₁_pos.ne' this

omit D in
theorem vertexOne_ne_vertexTwo : σ.vertexOne ≠ σ.vertexTwo := by
  intro h
  have := σ.norm_vertexOne_sub_vertexTwo
  rw [h, sub_self, norm_zero] at this
  exact σ.sin_θ₃_pos.ne' this.symm

theorem f_vertexOne : D.f σ.vertexOne = 3 / 2 := by
  have h : σ.vertexOne ∈ discOne D := by
    change ‖σ.vertexOne - σ.vertexOne‖ < radOne D
    rw [sub_self, norm_zero]; exact radOne_pos D
  rw [(f_of_mem_discOne D h).2, EuclidShape.apexOne, σ.rotOne_vertexOne,
    zero_pow (by have := σ.two_le_p₁; omega)]
  ring

theorem f_vertexTwo : D.f σ.vertexTwo = -(3 / 2) := by
  have h : σ.vertexTwo ∈ discTwo D := by
    change ‖σ.vertexTwo - σ.vertexTwo‖ < radTwo D
    rw [sub_self, norm_zero]; exact radTwo_pos D
  rw [(f_of_mem_discTwo D h).2, EuclidShape.apexTwo, σ.rotTwo_vertexTwo,
    zero_pow (by have := σ.two_le_p₂; omega)]
  ring

theorem norm_f_lt {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) : ‖D.f z‖ < 7 / 2 :=
  ((bijOn_f' D).mapsTo ⟨hz, h0⟩).1

theorem im_f_nonneg {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) : 0 ≤ (D.f z).im :=
  ((bijOn_f' D).mapsTo ⟨hz, h0⟩).2

theorem eq_of_f_eq {z w : ℂ} (hz : z ∈ σ.triangle) (hz0 : z ≠ 0) (hw : w ∈ σ.triangle)
    (hw0 : w ≠ 0) (h : D.f z = D.f w) : z = w :=
  (bijOn_f' D).injOn ⟨hz, hz0⟩ ⟨hw, hw0⟩ h

theorem wall_image_aux {S : Set ℂ} (hS : IsPreconnected S) (hsub : S ⊆ σ.triangle \ {0})
    {a b : ℝ} (ha : ∀ z ∈ S, (D.f z).re ≠ a) (hb : ∀ z ∈ S, (D.f z).re ≠ b) {z₀ : ℂ}
    (hz₀ : z₀ ∈ S) (h₀ : a < (D.f z₀).re ∧ (D.f z₀).re < b) :
    ∀ z ∈ S, a < (D.f z).re ∧ (D.f z).re < b := by
  have hc : ContinuousOn (fun w => (D.f w).re) S :=
    continuous_re.comp_continuousOn (D.contDiffOn_f.continuousOn.mono
      (fun w hw => triangle_diff_subset_U' D (hsub hw)))
  exact preconnected_real_avoid hS hc ha hb hz₀ h₀

omit D in
theorem wallSide_smul_vertexOne (t : ℝ) :
    σ.wallSide 0 ((t : ℂ) * σ.vertexOne) = t * (Real.sin σ.θ₂ * Real.sin σ.θ₃) ∧
      σ.wallSide 1 ((t : ℂ) * σ.vertexOne) = 0 ∧
      σ.wallSide 2 ((t : ℂ) * σ.vertexOne) = (1 - t) * (Real.sin σ.θ₁ * Real.sin σ.θ₂) := by
  have he := σ.sin_θ₁_eq
  refine ⟨?_, ?_, ?_⟩
  · rw [EuclidShape.wallSide_zero_apply, mul_im, ofReal_re, ofReal_im, zero_mul, add_zero,
      vertexOne_im]
  · rw [EuclidShape.wallSide_one_apply, mul_re, mul_im, ofReal_re, ofReal_im, vertexOne_re,
      vertexOne_im]
    ring
  · rw [EuclidShape.wallSide_two_apply, mul_re, mul_im, ofReal_re, ofReal_im, vertexOne_re,
      vertexOne_im, he]
    ring

omit D in
theorem wallSide_smul_vertexTwo (t : ℝ) :
    σ.wallSide 0 ((t : ℂ) * σ.vertexTwo) = 0 ∧
      σ.wallSide 1 ((t : ℂ) * σ.vertexTwo) = t * (Real.sin σ.θ₁ * Real.sin σ.θ₃) ∧
      σ.wallSide 2 ((t : ℂ) * σ.vertexTwo) = (1 - t) * (Real.sin σ.θ₁ * Real.sin σ.θ₂) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [EuclidShape.wallSide_zero_apply, EuclidShape.vertexTwo, ← ofReal_mul, ofReal_im]
  · rw [EuclidShape.wallSide_one_apply, EuclidShape.vertexTwo, ← ofReal_mul, ofReal_re,
      ofReal_im]
    ring
  · rw [EuclidShape.wallSide_two_apply, EuclidShape.vertexTwo, ← ofReal_mul, ofReal_re,
      ofReal_im]
    ring

omit D in
theorem wallSide_segTwo (t : ℝ) :
    σ.wallSide 0 (σ.vertexTwo + (t : ℂ) * (σ.vertexOne - σ.vertexTwo)) =
        t * (Real.sin σ.θ₂ * Real.sin σ.θ₃) ∧
      σ.wallSide 1 (σ.vertexTwo + (t : ℂ) * (σ.vertexOne - σ.vertexTwo)) =
        (1 - t) * (Real.sin σ.θ₁ * Real.sin σ.θ₃) ∧
      σ.wallSide 2 (σ.vertexTwo + (t : ℂ) * (σ.vertexOne - σ.vertexTwo)) = 0 := by
  have he := σ.sin_θ₁_eq
  refine ⟨?_, ?_, ?_⟩
  · rw [EuclidShape.wallSide_zero_apply]
    simp only [add_im, mul_im, sub_im, sub_re, ofReal_re, ofReal_im, vertexOne_im, vertexOne_re,
      EuclidShape.vertexTwo]
    ring
  · rw [EuclidShape.wallSide_one_apply]
    simp only [add_im, add_re, mul_im, mul_re, sub_im, sub_re, ofReal_re, ofReal_im, vertexOne_im,
      vertexOne_re, EuclidShape.vertexTwo]
    ring
  · rw [EuclidShape.wallSide_two_apply]
    simp only [add_im, add_re, mul_im, mul_re, sub_im, sub_re, ofReal_re, ofReal_im, vertexOne_im,
      vertexOne_re, EuclidShape.vertexTwo]
    rw [he]
    ring

theorem mem_triangle_of_sides {z : ℂ} (h0 : 0 ≤ σ.wallSide 0 z) (h1 : 0 ≤ σ.wallSide 1 z)
    (h2 : 0 ≤ σ.wallSide 2 z) : z ∈ σ.triangle := by
  intro i
  fin_cases i
  exacts [h0, h1, h2]

omit D in
theorem eq_smul_vertexOne_of_wallOne {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 1 z = 0) :
    z = ((σ.baryOne z : ℝ) : ℂ) * σ.vertexOne ∧ 0 ≤ σ.baryOne z ∧ σ.baryOne z ≤ 1 := by
  have hb := σ.eq_bary z
  have h2 : σ.baryTwo z = 0 := by rw [EuclidShape.baryTwo, hw, zero_div]
  rw [h2, ofReal_zero, zero_mul, zero_add] at hb
  obtain ⟨n1, -, n3⟩ := σ.bary_nonneg hz
  have hs := σ.bary_sum z
  exact ⟨hb, n1, by linarith⟩

omit D in
theorem eq_smul_vertexTwo_of_wallZero {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 0 z = 0) :
    z = ((σ.baryTwo z : ℝ) : ℂ) * σ.vertexTwo ∧ 0 ≤ σ.baryTwo z ∧ σ.baryTwo z ≤ 1 := by
  have hb := σ.eq_bary z
  have h1 : σ.baryOne z = 0 := by rw [EuclidShape.baryOne, hw, zero_div]
  rw [h1, ofReal_zero, zero_mul, add_zero] at hb
  obtain ⟨-, n2, n3⟩ := σ.bary_nonneg hz
  have hs := σ.bary_sum z
  exact ⟨hb, n2, by linarith⟩

omit D in
theorem eq_seg_of_wallTwo {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 2 z = 0) :
    z = σ.vertexTwo + ((σ.baryOne z : ℝ) : ℂ) * (σ.vertexOne - σ.vertexTwo) ∧
      0 ≤ σ.baryOne z ∧ σ.baryOne z ≤ 1 := by
  have hb := σ.eq_bary z
  have h3 : σ.baryThree z = 0 := by rw [EuclidShape.baryThree, hw, zero_div]
  have hs := σ.bary_sum z
  obtain ⟨n1, n2, -⟩ := σ.bary_nonneg hz
  have h2 : σ.baryTwo z = 1 - σ.baryOne z := by linarith
  refine ⟨?_, n1, by linarith⟩
  calc z = ((σ.baryTwo z : ℝ) : ℂ) * σ.vertexTwo + ((σ.baryOne z : ℝ) : ℂ) * σ.vertexOne := hb
    _ = _ := by rw [h2]; push_cast; ring

omit D in
theorem outerGerm_smul_vertexOne {t : ℝ} (ht : 0 < t) :
    compactOuterGerm σ.p₃ ((t : ℂ) * σ.vertexOne) =
      ((7 / 2 - ‖(t : ℂ) * σ.vertexOne‖ ^ σ.p₃ / 2 : ℝ) : ℂ) := by
  have hpos : 0 < t * Real.sin σ.θ₂ := mul_pos ht σ.sin_θ₂_pos
  have hz : (t : ℂ) * σ.vertexOne = ((t * Real.sin σ.θ₂ : ℝ) : ℂ) * exp ((σ.θ₃ : ℂ) * I) := by
    rw [EuclidShape.vertexOne]; push_cast; ring
  have hn : ‖(t : ℂ) * σ.vertexOne‖ = t * Real.sin σ.θ₂ := by
    rw [hz, norm_mul, Complex.norm_real, Real.norm_of_nonneg hpos.le, EuclidShape.norm_exp_mul_I,
      mul_one]
  have hc : conj ((t : ℂ) * σ.vertexOne) / ‖(t : ℂ) * σ.vertexOne‖ = exp (-((σ.θ₃ : ℂ) * I)) := by
    rw [hn, hz, map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
    have hne : ((t * Real.sin σ.θ₂ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hpos.ne'
    rw [mul_div_cancel_left₀ _ hne]
    congr 1
    simp [map_mul, conj_ofReal, conj_I]
  have hp : exp (-((σ.θ₃ : ℂ) * I)) ^ σ.p₃ = -1 := by
    rw [← Complex.exp_nat_mul, show (σ.p₃ : ℂ) * -((σ.θ₃ : ℂ) * I) =
      -(((σ.θ₃ * σ.p₃ : ℝ) : ℂ) * I) by push_cast; ring, σ.θ₃_mul, Complex.exp_neg,
      Complex.exp_pi_mul_I]
    norm_num
  unfold compactOuterGerm
  rw [hc, hp]
  ring

omit D in
theorem outerGerm_smul_vertexTwo {t : ℝ} (ht : 0 < t) :
    compactOuterGerm σ.p₃ ((t : ℂ) * σ.vertexTwo) =
      -((7 / 2 - ‖(t : ℂ) * σ.vertexTwo‖ ^ σ.p₃ / 2 : ℝ) : ℂ) := by
  have hpos : 0 < t * Real.sin σ.θ₁ := mul_pos ht σ.sin_θ₁_pos
  have hz : (t : ℂ) * σ.vertexTwo = ((t * Real.sin σ.θ₁ : ℝ) : ℂ) := by
    rw [EuclidShape.vertexTwo]; push_cast; ring
  have hc : conj ((t : ℂ) * σ.vertexTwo) / ‖(t : ℂ) * σ.vertexTwo‖ = 1 := by
    rw [hz, Complex.conj_ofReal, Complex.norm_real, Real.norm_of_nonneg hpos.le]
    exact div_self (by exact_mod_cast hpos.ne')
  unfold compactOuterGerm
  rw [hc, one_pow, mul_one]

omit D in
theorem rotOne_segOne (τ : ℝ) :
    σ.rotOne (σ.vertexOne + (τ : ℂ) * (σ.vertexTwo - σ.vertexOne)) =
      ((τ * Real.sin σ.θ₃ : ℝ) : ℂ) * exp ((σ.θ₁ : ℂ) * I) := by
  rw [EuclidShape.rotOne, add_sub_cancel_left, σ.vertexTwo_sub_vertexOne]
  have hs := σ.θ_sum
  have e : exp (-((σ.θ₃ : ℂ) * I)) * exp (-((σ.θ₂ : ℂ) * I)) = -exp ((σ.θ₁ : ℂ) * I) := by
    rw [← Complex.exp_add, show -((σ.θ₃ : ℂ) * I) + -((σ.θ₂ : ℂ) * I) =
      (σ.θ₁ : ℂ) * I + -(Real.pi * I) by
        rw [show σ.θ₁ = Real.pi - σ.θ₂ - σ.θ₃ by linarith]; push_cast; ring,
      Complex.exp_add, Complex.exp_neg, Complex.exp_pi_mul_I]
    ring
  rw [ofReal_mul]
  linear_combination (-((τ : ℂ) * ((Real.sin σ.θ₃ : ℝ) : ℂ))) * e

theorem re_f_wallOne {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 1 z = 0) (h0 : z ≠ 0)
    (h1 : z ≠ σ.vertexOne) : 3 / 2 < (D.f z).re ∧ (D.f z).re < 7 / 2 := by
  set S : Set ℂ := (fun t : ℝ => (t : ℂ) * σ.vertexOne) '' Ioo 0 1 with hS
  have hpc : IsPreconnected S := isPreconnected_Ioo.image _ (by fun_prop)
  have hsub : S ⊆ σ.triangle \ {0} := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨e0, e1, e2⟩ := wallSide_smul_vertexOne (σ := σ) t
    have p23 := mul_pos σ.sin_θ₂_pos σ.sin_θ₃_pos
    have p12 := mul_pos σ.sin_θ₁_pos σ.sin_θ₂_pos
    have g0 : 0 ≤ σ.wallSide 0 ((t : ℂ) * σ.vertexOne) := by rw [e0]; nlinarith [ht.1]
    have g1 : 0 ≤ σ.wallSide 1 ((t : ℂ) * σ.vertexOne) := by rw [e1]
    have g2 : 0 ≤ σ.wallSide 2 ((t : ℂ) * σ.vertexOne) := by rw [e2]; nlinarith [ht.2]
    refine ⟨mem_triangle_of_sides g0 g1 g2, ?_⟩
    simp only [mem_singleton_iff, mul_eq_zero, ofReal_eq_zero]
    rintro (h | h)
    · exact ht.1.ne' h
    · exact vertexOne_ne_zero h
  have hwall : ∀ w ∈ S, σ.wallSide 1 w = 0 := by
    rintro _ ⟨t, -, rfl⟩
    exact (wallSide_smul_vertexOne t).2.1
  have hv1 : σ.vertexOne ∈ σ.triangle \ {0} := ⟨σ.vertexOne_mem_triangle, vertexOne_ne_zero⟩
  have hres := wall_image_aux D hpc hsub (a := 3 / 2) (b := 7 / 2)
    (fun w hw' heq => by
      have him := im_f_of_wall D (hsub hw').1 (hwall w hw') (hsub hw').2
      have hfw : D.f w = D.f σ.vertexOne := by
        rw [f_vertexOne]; apply Complex.ext <;> simp [heq, him]
      have := eq_of_f_eq D (hsub hw').1 (hsub hw').2 hv1.1 hv1.2 hfw
      obtain ⟨t, ht, rfl⟩ := hw'
      have this' : (t : ℂ) * σ.vertexOne = σ.vertexOne := this
      have h' : ((t : ℂ) - 1) * σ.vertexOne = 0 := by rw [sub_mul, this', one_mul, sub_self]
      rcases mul_eq_zero.mp h' with h'' | h''
      · have : t = 1 := by exact_mod_cast sub_eq_zero.mp h''
        exact ht.2.ne this
      · exact vertexOne_ne_zero h'')
    (fun w hw' heq => by
      have := norm_f_lt D (hsub hw').1 (hsub hw').2
      have := Complex.abs_re_le_norm (D.f w)
      rw [heq] at this
      norm_num at this
      linarith)
    (z₀ := ((radThree D / 2 : ℝ) : ℂ) * σ.vertexOne)
    ⟨radThree D / 2, ⟨by linarith [radThree_pos D], by linarith [radThree_le_half D]⟩, rfl⟩
    (by
      have ht : 0 < radThree D / 2 := by linarith [radThree_pos D]
      have hn : ‖((radThree D / 2 : ℝ) : ℂ) * σ.vertexOne‖ < radThree D := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le, σ.norm_vertexOne]
        have := Real.sin_le_one σ.θ₂
        nlinarith [radThree_pos D]
      have hne : ((radThree D / 2 : ℝ) : ℂ) * σ.vertexOne ≠ 0 :=
        mul_ne_zero (by exact_mod_cast ht.ne') vertexOne_ne_zero
      rw [(f_of_mem_discThree D hn hne).2, outerGerm_smul_vertexOne ht, ofReal_re]
      have hle : ‖((radThree D / 2 : ℝ) : ℂ) * σ.vertexOne‖ ^ σ.p₃ ≤ 1 :=
        pow_le_one₀ (norm_nonneg _) (by linarith [radThree_le_half D])
      have hpos : 0 < ‖((radThree D / 2 : ℝ) : ℂ) * σ.vertexOne‖ ^ σ.p₃ :=
        pow_pos (norm_pos_iff.mpr hne) _
      constructor <;> linarith)
  obtain ⟨hzb, n0, n1⟩ := eq_smul_vertexOne_of_wallOne hz hw
  apply hres z
  refine ⟨σ.baryOne z, ⟨lt_of_le_of_ne n0 ?_, lt_of_le_of_ne n1 ?_⟩, hzb.symm⟩
  · intro h
    apply h0
    rw [hzb, ← h, ofReal_zero, zero_mul]
  · intro h
    apply h1
    rw [hzb, h, ofReal_one, one_mul]

theorem re_f_wallZero {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 0 z = 0) (h0 : z ≠ 0)
    (h2 : z ≠ σ.vertexTwo) : -(7 / 2) < (D.f z).re ∧ (D.f z).re < -(3 / 2) := by
  set S : Set ℂ := (fun t : ℝ => (t : ℂ) * σ.vertexTwo) '' Ioo 0 1 with hS
  have hpc : IsPreconnected S := isPreconnected_Ioo.image _ (by fun_prop)
  have hsub : S ⊆ σ.triangle \ {0} := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨e0, e1, e2⟩ := wallSide_smul_vertexTwo (σ := σ) t
    have p13 := mul_pos σ.sin_θ₁_pos σ.sin_θ₃_pos
    have p12 := mul_pos σ.sin_θ₁_pos σ.sin_θ₂_pos
    have g0 : 0 ≤ σ.wallSide 0 ((t : ℂ) * σ.vertexTwo) := by rw [e0]
    have g1 : 0 ≤ σ.wallSide 1 ((t : ℂ) * σ.vertexTwo) := by rw [e1]; nlinarith [ht.1]
    have g2 : 0 ≤ σ.wallSide 2 ((t : ℂ) * σ.vertexTwo) := by rw [e2]; nlinarith [ht.2]
    refine ⟨mem_triangle_of_sides g0 g1 g2, ?_⟩
    simp only [mem_singleton_iff, mul_eq_zero, ofReal_eq_zero]
    rintro (h | h)
    · exact ht.1.ne' h
    · exact vertexTwo_ne_zero h
  have hwall : ∀ w ∈ S, σ.wallSide 0 w = 0 := by
    rintro _ ⟨t, -, rfl⟩
    exact (wallSide_smul_vertexTwo t).1
  have hv2 : σ.vertexTwo ∈ σ.triangle \ {0} := ⟨σ.vertexTwo_mem_triangle, vertexTwo_ne_zero⟩
  have hres := wall_image_aux D hpc hsub (a := -(7 / 2)) (b := -(3 / 2))
    (fun w hw' heq => by
      have := norm_f_lt D (hsub hw').1 (hsub hw').2
      have := Complex.abs_re_le_norm (D.f w)
      rw [heq] at this
      norm_num at this
      linarith)
    (fun w hw' heq => by
      have him := im_f_of_wall D (hsub hw').1 (hwall w hw') (hsub hw').2
      have hfw : D.f w = D.f σ.vertexTwo := by
        rw [f_vertexTwo]; apply Complex.ext <;> simp [heq, him]
      have := eq_of_f_eq D (hsub hw').1 (hsub hw').2 hv2.1 hv2.2 hfw
      obtain ⟨t, ht, rfl⟩ := hw'
      have this' : (t : ℂ) * σ.vertexTwo = σ.vertexTwo := this
      have h' : ((t : ℂ) - 1) * σ.vertexTwo = 0 := by rw [sub_mul, this', one_mul, sub_self]
      rcases mul_eq_zero.mp h' with h'' | h''
      · have : t = 1 := by exact_mod_cast sub_eq_zero.mp h''
        exact ht.2.ne this
      · exact vertexTwo_ne_zero h'')
    (z₀ := ((radThree D / 2 : ℝ) : ℂ) * σ.vertexTwo)
    ⟨radThree D / 2, ⟨by linarith [radThree_pos D], by linarith [radThree_le_half D]⟩, rfl⟩
    (by
      have ht : 0 < radThree D / 2 := by linarith [radThree_pos D]
      have hn : ‖((radThree D / 2 : ℝ) : ℂ) * σ.vertexTwo‖ < radThree D := by
        rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le, σ.norm_vertexTwo]
        have := Real.sin_le_one σ.θ₁
        nlinarith [radThree_pos D]
      have hne : ((radThree D / 2 : ℝ) : ℂ) * σ.vertexTwo ≠ 0 :=
        mul_ne_zero (by exact_mod_cast ht.ne') vertexTwo_ne_zero
      rw [(f_of_mem_discThree D hn hne).2, outerGerm_smul_vertexTwo ht, neg_re, ofReal_re]
      have hle : ‖((radThree D / 2 : ℝ) : ℂ) * σ.vertexTwo‖ ^ σ.p₃ ≤ 1 :=
        pow_le_one₀ (norm_nonneg _) (by linarith [radThree_le_half D])
      have hpos : 0 < ‖((radThree D / 2 : ℝ) : ℂ) * σ.vertexTwo‖ ^ σ.p₃ :=
        pow_pos (norm_pos_iff.mpr hne) _
      constructor <;> linarith)
  obtain ⟨hzb, n0, n1⟩ := eq_smul_vertexTwo_of_wallZero hz hw
  apply hres z
  refine ⟨σ.baryTwo z, ⟨lt_of_le_of_ne n0 ?_, lt_of_le_of_ne n1 ?_⟩, hzb.symm⟩
  · intro h
    apply h0
    rw [hzb, ← h, ofReal_zero, zero_mul]
  · intro h
    apply h2
    rw [hzb, h, ofReal_one, one_mul]

theorem re_f_wallTwo {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 2 z = 0)
    (h1 : z ≠ σ.vertexOne) (h2 : z ≠ σ.vertexTwo) :
    -(3 / 2) < (D.f z).re ∧ (D.f z).re < 3 / 2 := by
  set S : Set ℂ := (fun t : ℝ => σ.vertexTwo + (t : ℂ) * (σ.vertexOne - σ.vertexTwo)) ''
    Ioo 0 1 with hS
  have hpc : IsPreconnected S := isPreconnected_Ioo.image _ (by fun_prop)
  have hzero : ∀ t ∈ Ioo (0 : ℝ) 1, σ.vertexTwo + (t : ℂ) * (σ.vertexOne - σ.vertexTwo) ≠ 0 := by
    intro t ht h
    have := (wallSide_segTwo (σ := σ) t).2.1
    rw [h, EuclidShape.wallSide_one_zero] at this
    have := mul_pos σ.sin_θ₁_pos σ.sin_θ₃_pos
    nlinarith [ht.2]
  have hsub : S ⊆ σ.triangle \ {0} := by
    rintro _ ⟨t, ht, rfl⟩
    obtain ⟨e0, e1, e2⟩ := wallSide_segTwo (σ := σ) t
    have p23 := mul_pos σ.sin_θ₂_pos σ.sin_θ₃_pos
    have p13 := mul_pos σ.sin_θ₁_pos σ.sin_θ₃_pos
    have g0 : 0 ≤ σ.wallSide 0 (σ.vertexTwo + (t : ℂ) * (σ.vertexOne - σ.vertexTwo)) := by
      rw [e0]; nlinarith [ht.1]
    have g1 : 0 ≤ σ.wallSide 1 (σ.vertexTwo + (t : ℂ) * (σ.vertexOne - σ.vertexTwo)) := by
      rw [e1]; nlinarith [ht.2]
    have g2 : 0 ≤ σ.wallSide 2 (σ.vertexTwo + (t : ℂ) * (σ.vertexOne - σ.vertexTwo)) := by
      rw [e2]
    exact ⟨mem_triangle_of_sides g0 g1 g2, hzero t ht⟩
  have hwall : ∀ w ∈ S, σ.wallSide 2 w = 0 := by
    rintro _ ⟨t, -, rfl⟩
    exact (wallSide_segTwo t).2.2
  have hv1 : σ.vertexOne ∈ σ.triangle \ {0} := ⟨σ.vertexOne_mem_triangle, vertexOne_ne_zero⟩
  have hv2 : σ.vertexTwo ∈ σ.triangle \ {0} := ⟨σ.vertexTwo_mem_triangle, vertexTwo_ne_zero⟩
  have hsub' : σ.vertexOne - σ.vertexTwo ≠ 0 := sub_ne_zero.mpr vertexOne_ne_vertexTwo
  have hres := wall_image_aux D hpc hsub (a := -(3 / 2)) (b := 3 / 2)
    (fun w hw' heq => by
      have him := im_f_of_wall D (hsub hw').1 (hwall w hw') (hsub hw').2
      have hfw : D.f w = D.f σ.vertexTwo := by
        rw [f_vertexTwo]; apply Complex.ext <;> simp [heq, him]
      have := eq_of_f_eq D (hsub hw').1 (hsub hw').2 hv2.1 hv2.2 hfw
      obtain ⟨t, ht, rfl⟩ := hw'
      have this' : σ.vertexTwo + (t : ℂ) * (σ.vertexOne - σ.vertexTwo) = σ.vertexTwo := this
      have h' : (t : ℂ) * (σ.vertexOne - σ.vertexTwo) = 0 := by
        linear_combination this'
      rcases mul_eq_zero.mp h' with h'' | h''
      · exact ht.1.ne' (by exact_mod_cast h'')
      · exact hsub' h'')
    (fun w hw' heq => by
      have him := im_f_of_wall D (hsub hw').1 (hwall w hw') (hsub hw').2
      have hfw : D.f w = D.f σ.vertexOne := by
        rw [f_vertexOne]; apply Complex.ext <;> simp [heq, him]
      have := eq_of_f_eq D (hsub hw').1 (hsub hw').2 hv1.1 hv1.2 hfw
      obtain ⟨t, ht, rfl⟩ := hw'
      have this' : σ.vertexTwo + (t : ℂ) * (σ.vertexOne - σ.vertexTwo) = σ.vertexOne := this
      have h' : ((t : ℂ) - 1) * (σ.vertexOne - σ.vertexTwo) = 0 := by
        linear_combination this'
      rcases mul_eq_zero.mp h' with h'' | h''
      · have : t = 1 := by exact_mod_cast sub_eq_zero.mp h''
        exact ht.2.ne this
      · exact hsub' h'')
    (z₀ := σ.vertexTwo + ((1 - radOne D / 2 : ℝ) : ℂ) * (σ.vertexOne - σ.vertexTwo))
    ⟨1 - radOne D / 2, ⟨by linarith [radOne_le_half D], by linarith [radOne_pos D]⟩, rfl⟩
    (by
      have ht : 0 < radOne D / 2 := by linarith [radOne_pos D]
      have hz₀ : σ.vertexTwo + ((1 - radOne D / 2 : ℝ) : ℂ) * (σ.vertexOne - σ.vertexTwo) =
          σ.vertexOne + ((radOne D / 2 : ℝ) : ℂ) * (σ.vertexTwo - σ.vertexOne) := by
        push_cast; ring
      have hn : ‖σ.vertexOne + ((radOne D / 2 : ℝ) : ℂ) * (σ.vertexTwo - σ.vertexOne) -
          σ.vertexOne‖ < radOne D := by
        rw [add_sub_cancel_left, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht.le,
          norm_sub_rev, σ.norm_vertexOne_sub_vertexTwo]
        have := Real.sin_le_one σ.θ₃
        nlinarith [radOne_pos D]
      rw [hz₀, (f_of_mem_discOne D hn).2, EuclidShape.apexOne, rotOne_segOne, mul_pow,
        ← Complex.exp_nat_mul,
        show (σ.p₁ : ℂ) * ((σ.θ₁ : ℂ) * I) = ((σ.θ₁ * σ.p₁ : ℝ) : ℂ) * I by push_cast; ring,
        σ.θ₁_mul, Complex.exp_pi_mul_I, ← ofReal_pow]
      have hpos : 0 < (radOne D / 2 * Real.sin σ.θ₃) ^ σ.p₁ :=
        pow_pos (mul_pos ht σ.sin_θ₃_pos) _
      have hle : (radOne D / 2 * Real.sin σ.θ₃) ^ σ.p₁ ≤ 1 := by
        apply pow_le_one₀ (mul_pos ht σ.sin_θ₃_pos).le
        have := Real.sin_le_one σ.θ₃
        nlinarith [radOne_le_half D]
      simp only [add_re, div_ofNat_re, mul_re, ofReal_re, ofReal_im, neg_re, one_re, neg_im,
        one_im]
      norm_num
      constructor <;> linarith)
  obtain ⟨hzb, n0, n1⟩ := eq_seg_of_wallTwo hz hw
  apply hres z
  refine ⟨σ.baryOne z, ⟨lt_of_le_of_ne n0 ?_, lt_of_le_of_ne n1 ?_⟩, hzb.symm⟩
  · intro h
    apply h2
    rw [hzb, ← h, ofReal_zero, zero_mul, add_zero]
  · intro h
    apply h1
    rw [hzb, h, ofReal_one, one_mul]
    ring

omit D in
theorem ne_vertexOne_of_mem_intT {z : ℂ} (hz : z ∈ intT σ) : z ≠ σ.vertexOne := by
  rintro rfl
  have := hz 1
  rw [σ.wallSide_one_vertexOne] at this
  exact lt_irrefl _ this

omit D in
theorem ne_vertexTwo_of_mem_intT {z : ℂ} (hz : z ∈ intT σ) : z ≠ σ.vertexTwo := by
  rintro rfl
  have := hz 0
  rw [σ.wallSide_zero_vertexTwo] at this
  exact lt_irrefl _ this

theorem map_nhds_f {z : ℂ} (hz : z ∈ D.U) (h1 : z ≠ σ.vertexOne) (h2 : z ≠ σ.vertexTwo) :
    Filter.map D.f (𝓝 z) = 𝓝 (D.f z) := by
  have hcd : ContDiffAt ℝ ∞ D.f z := D.contDiffOn_f.contDiffAt (D.isOpen_U.mem_nhds hz)
  have hs : HasStrictFDerivAt D.f (fderiv ℝ D.f z) z := hcd.hasStrictFDerivAt (by simp)
  have hdet := det_fderiv_pos' D hz h1 h2
  have hu : IsUnit ((fderiv ℝ D.f z : ℂ →L[ℝ] ℂ) : ℂ →ₗ[ℝ] ℂ) :=
    (LinearMap.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet.ne')
  have hsurj : (fderiv ℝ D.f z).range = ⊤ := by
    have := (LinearMap.isUnit_iff_range_eq_top _).1 hu
    exact this
  exact hs.map_nhds_eq_of_surj hsurj

theorem im_f_pos_of_intT {z : ℂ} (hz : z ∈ intT σ) : 0 < (D.f z).im := by
  have hz0 := ne_zero_of_mem_intT hz
  have hzT := intT_subset_triangle hz
  rcases (im_f_nonneg D hzT hz0).lt_or_eq with h | h
  · exact h
  exfalso
  have hmap := map_nhds_f D (intT_subset_U D hz) (ne_vertexOne_of_mem_intT hz)
    (ne_vertexTwo_of_mem_intT hz)
  have himg : D.f '' intT σ ∈ 𝓝 (D.f z) := by
    rw [← hmap]
    exact Filter.image_mem_map (isOpen_intT.mem_nhds hz)
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp himg
  have hu : D.f z - ((ε / 2 : ℝ) : ℂ) * I ∈ Metric.ball (D.f z) ε := by
    rw [Metric.mem_ball, dist_eq_norm, sub_sub_cancel_left, norm_neg, norm_mul, Complex.norm_I,
      mul_one, Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    linarith
  obtain ⟨w, hw, hfw⟩ := hball hu
  have := im_f_nonneg D (intT_subset_triangle hw) (ne_zero_of_mem_intT hw)
  rw [hfw, sub_im, mul_im, ofReal_re, ofReal_im, I_re, I_im, ← h] at this
  linarith

theorem im_f_neg_of_patchOne {z : ℂ} (hz : z ∈ patchOne D) (hT : z ∉ σ.triangle) :
    (D.f z).im < 0 := by
  have h := im_f_pos_of_intT D (refl_mem_intT_of_patchOne D hz hT)
  rw [f_refl' D 1 hz.1, conj_im] at h
  linarith

theorem im_f_neg_of_patchTwo {z : ℂ} (hz : z ∈ patchTwo D) (hT : z ∉ σ.triangle) :
    (D.f z).im < 0 := by
  have h := im_f_pos_of_intT D (refl_mem_intT_of_patchTwo D hz hT)
  rw [f_refl' D 2 hz.1, conj_im] at h
  linarith

theorem im_f_neg_of_patchZero {z : ℂ} (hz : z ∈ patchZero D) (hT : z ∉ σ.triangle) :
    (D.f z).im < 0 := by
  have h := im_f_pos_of_intT D (refl_mem_intT_of_patchZero D hz hT)
  rw [f_refl' D 0 hz.1, conj_im] at h
  linarith

end ClosedTriangle

end GC.Seifert
