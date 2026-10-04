import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryHypSectors
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ClosedTriangleGeometryFlatCover

/-!
# The hyperbolic triangle is covered by the main set and the vertex discs

Lane B3c (design `docs/geometrization/handoffs/20261004-design-b3c-hyperbolic-rows.md`, §3; the
hyperbolic analogue of B3's `ClosedTriangleGeometryFlatCover`, with review 33 §4.2: explicit
margins, no uniform margin on the punctured triangle). Every point of the hyperbolic triangle other
than the outer vertex lies in the main set or in one of the three vertex discs
(`triangle_diff_subset_cover`). Interior points are in the open triangle. On wall `1` (`z = t
e^{iθ₃}`, `0 < t < t₁`) the coordinate `rotOne z = (t₁ - t)/(1 - t₁ t)` is real and `t₁ w₂(z) = t₂
sin θ₂ (t₁ - t)(1 - t₁ t)` (`HypFold.wallSide_two_ray`), so `w₂ ≤ κ` forces `z ∈ discOne`, and `w₀ =
t sin θ₃ ≤ κ` forces `z ∈ discThree`; otherwise `z` is in `patchOne` (`mem_cover_of_wallOne`). Wall
`0` is the real segment, with `e^{-iθ₂} rotTwo x = (t₂ - x)/(1 - t₂ x)` (`mem_cover_of_wallZero`).
On wall `2` the coordinate `rotTwo z = r` is real and nonnegative, and `e^{-iθ₁} rotOne z = (s -
r)/(1 - s r)` (`HypFold.exp_neg_mul_rotOne`); the side functions `w₀`, `w₁` are positive multiples
of `r` and of `|rotOne z|` (`mem_cover_of_wallTwo`).
-/

set_option autoImplicit false

noncomputable section

open Set Complex
open scoped ComplexConjugate ContDiff

namespace GC.Seifert

namespace ClosedTriangle

namespace Hyp

open TwoConeFold

variable {σ : CompactShape} {D : σ.FoldData} (hσ : σ.curv = .hyperbolic)
include hσ

omit hσ in
theorem exp_neg_mul_exp (x : ℝ) : exp (-((x : ℂ) * I)) * exp ((x : ℂ) * I) = 1 := by
  rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]

omit hσ in
theorem conj_exp_ofReal_mul_I (x : ℝ) : conj (exp ((x : ℂ) * I)) = exp (-((x : ℂ) * I)) := by
  rw [← Complex.exp_conj, map_mul, conj_ofReal, conj_I, mul_neg]

theorem rotOne_ray {t : ℝ} (ht : t < 1) :
    σ.rotOne ((t : ℂ) * exp ((σ.θ₃ : ℂ) * I)) =
      (((σ.sideTanOne - t) / (1 - σ.sideTanOne * t) : ℝ) : ℂ) := by
  have h1 := sideTanOne_lt_one hσ
  have h0 := σ.sideTanOne_pos
  have hd : (1 : ℝ) - σ.sideTanOne * t ≠ 0 := by
    intro h
    by_cases htn : t ≤ 0
    · nlinarith
    · nlinarith
  have hd' : (1 : ℂ) - (σ.sideTanOne : ℂ) * t ≠ 0 := by exact_mod_cast hd
  rw [HypFold.rotOne_eq_mul_mob hσ, HypFold.mob, σ.vertexOne_eq_ray, map_mul, conj_ofReal,
    conj_exp_ofReal_mul_I]
  have hEE := exp_neg_mul_exp σ.θ₃
  have e2 : 1 - (σ.sideTanOne : ℂ) * exp (-((σ.θ₃ : ℂ) * I)) * ((t : ℂ) *
      exp ((σ.θ₃ : ℂ) * I)) = 1 - (σ.sideTanOne : ℂ) * t := by
    linear_combination (-(σ.sideTanOne : ℂ) * t) * hEE
  rw [e2]
  push_cast
  rw [← mul_div_assoc]
  congr 1
  linear_combination ((σ.sideTanOne : ℂ) - t) * hEE

theorem exp_neg_mul_rotTwo_real {x : ℝ} (hx : x < 1) :
    exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo (x : ℂ) =
      (((σ.sideTanTwo - x) / (1 - σ.sideTanTwo * x) : ℝ) : ℂ) := by
  have h1 := sideTanTwo_lt_one hσ
  have h0 := σ.sideTanTwo_pos
  have hd : (1 : ℝ) - σ.sideTanTwo * x ≠ 0 := by
    intro h
    by_cases hxn : x ≤ 0
    · nlinarith
    · nlinarith
  have hd' : (1 : ℂ) - (σ.sideTanTwo : ℂ) * x ≠ 0 := by exact_mod_cast hd
  rw [HypFold.exp_neg_mul_rotTwo hσ, HypFold.mob, σ.vertexTwo_eq_real, conj_ofReal]
  push_cast
  field_simp
  ring

theorem rotTwo_real {x : ℝ} (hx : x < 1) :
    σ.rotTwo (x : ℂ) = exp ((σ.θ₂ : ℂ) * I) *
      (((σ.sideTanTwo - x) / (1 - σ.sideTanTwo * x) : ℝ) : ℂ) := by
  rw [← exp_neg_mul_rotTwo_real hσ hx, ← mul_assoc, ← Complex.exp_add, add_neg_cancel,
    Complex.exp_zero, one_mul]

theorem mem_discOne_vertexOne : σ.vertexOne ∈ discOne D := by
  refine ⟨HypFold.norm_vertexOne_lt_one hσ, ?_⟩
  rw [HypFold.norm_rotOne hσ, HypFold.mob_self, norm_zero]
  exact radOne_pos D

theorem mem_discTwo_vertexTwo : σ.vertexTwo ∈ discTwo D := by
  refine ⟨HypFold.norm_vertexTwo_lt_one hσ, ?_⟩
  rw [HypFold.norm_rotTwo hσ, HypFold.mob_self, norm_zero]
  exact radTwo_pos D

omit hσ in
theorem cOne_le_one : cOne σ ≤ σ.sideTanTwo * Real.sin σ.θ₂ * (1 - σ.sideTanOne) ^ 2 :=
  mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)

omit hσ in
theorem cOne_le_two : cOne σ ≤ Real.sin σ.θ₁ * (1 - σ.sideTanOne) ^ 2 :=
  mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)

theorem mem_cover_of_wallOne {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 1 z = 0)
    (h0 : z ≠ 0) : z ∈ mainSet D ∪ discOne D ∪ discTwo D ∪ discThree D := by
  by_cases h1 : z = σ.vertexOne
  · left; left; right; rw [h1]; exact mem_discOne_vertexOne hσ
  have hzT := hz
  obtain ⟨t, ht0, ht1, rfl⟩ := σ.eq_ray_of_wallOne hz hw
  have htp : 0 < t := lt_of_le_of_ne ht0 fun h => h0 (by rw [← h, ofReal_zero, zero_mul])
  have htl : t < σ.sideTanOne := lt_of_le_of_ne ht1 fun h => h1 (by rw [h, σ.vertexOne_eq_ray])
  have hs1 := sideTanOne_lt_one hσ
  have hs0 := σ.sideTanOne_pos
  have hs2 := σ.sideTanTwo_pos
  have s1 := σ.sin_θ₁_pos
  have s2 := σ.sin_θ₂_pos
  have s3 := σ.sin_θ₃_pos
  have hk := kap_pos D hσ
  have e0 : σ.wallSide 0 ((t : ℂ) * exp ((σ.θ₃ : ℂ) * I)) = t * Real.sin σ.θ₃ := σ.ray_im t
  have hnz : ‖(t : ℂ) * exp ((σ.θ₃ : ℂ) * I)‖ = t := σ.norm_ray ht0
  by_cases hk0 : σ.wallSide 0 ((t : ℂ) * exp ((σ.θ₃ : ℂ) * I)) ≤ kap D
  · right
    change ‖(t : ℂ) * exp ((σ.θ₃ : ℂ) * I)‖ < radThree D
    rw [hnz]
    have := kap_lt_three D
    rw [e0] at hk0
    nlinarith
  have e2 := HypFold.wallSide_two_ray hσ t
  have hd : σ.sideTanOne * t ≤ σ.sideTanOne := by nlinarith
  have hR := rotOne_ray hσ (htl.trans hs1)
  have hdpos : 0 < 1 - σ.sideTanOne * t := by nlinarith
  by_cases hk2 : σ.wallSide 2 ((t : ℂ) * exp ((σ.θ₃ : ℂ) * I)) ≤ kap D
  · left; left; right
    refine ⟨by rw [hnz]; linarith, ?_⟩
    rw [hR, Complex.norm_real, Real.norm_of_nonneg (div_nonneg (by linarith) hdpos.le)]
    have hc := cOne_le_one (σ := σ)
    have hko := kap_lt_one D hσ
    have hrad := radOne_pos D
    change HypFold.sideOneThree σ * _ = HypFold.sideTwoThree σ * _ * _ * _ at e2
    change σ.sideTanOne * σ.wallSide 2 _ = σ.sideTanTwo * Real.sin σ.θ₂ *
      (σ.sideTanOne - t) * (1 - σ.sideTanOne * t) at e2
    rw [div_lt_iff₀ hdpos]
    have hw2 : 0 ≤ σ.wallSide 2 ((t : ℂ) * exp ((σ.θ₃ : ℂ) * I)) := hzT.2 2
    set K := σ.sideTanTwo * Real.sin σ.θ₂ with hKdef
    set d := 1 - σ.sideTanOne * t with hddef
    set w := σ.wallSide 2 ((t : ℂ) * exp ((σ.θ₃ : ℂ) * I)) with hwdef
    have hK : 0 < K := by positivity
    have st1 : K * (σ.sideTanOne - t) * d ≤ w := by
      have : K * (σ.sideTanOne - t) * d = σ.sideTanOne * w := by rw [e2]
      rw [this]
      nlinarith [mul_nonneg (show (0 : ℝ) ≤ 1 - σ.sideTanOne by linarith) hw2]
    have st2 : w < radOne D * (K * (1 - σ.sideTanOne) ^ 2) := by
      have := mul_le_mul_of_nonneg_left hc hrad.le
      linarith
    have st3 : (1 - σ.sideTanOne) ^ 2 ≤ d ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by nlinarith) 2
    have st4 : K * d * (σ.sideTanOne - t) < K * d * (radOne D * d) := by
      have := mul_le_mul_of_nonneg_left st3 (mul_nonneg hrad.le hK.le)
      nlinarith
    exact lt_of_mul_lt_mul_left st4 (by positivity)
  left; left; left; left; right
  simp only [not_le] at hk0 hk2
  have hpl : ‖(t : ℂ) * exp ((σ.θ₃ : ℂ) * I)‖ < 1 := by rw [hnz]; linarith
  have hr : σ.refl 1 ((t : ℂ) * exp ((σ.θ₃ : ℂ) * I)) = (t : ℂ) * exp ((σ.θ₃ : ℂ) * I) :=
    HypFold.refl_eq_self hσ 1 hpl hw
  refine ⟨D.foldWall_diff_subset_V 1 ⟨⟨hz, hw⟩, h0⟩, hk0, hk2, by rwa [hr], by rwa [hr],
    (D.re_f_wallOne ⟨hz, hw⟩ h0 h1).1, Or.inr ?_, Or.inr ?_⟩
  · rw [hR]
    exact ofReal_mem_wedgeSet (div_pos (by linarith) hdpos) (by linarith [σ.θ₁_pos])
  · rw [← mul_assoc, mul_comm (exp _) (t : ℂ), mul_assoc, exp_neg_mul_exp, mul_one]
    exact ofReal_mem_wedgeSet htp (by linarith [σ.θ₃_pos])

omit hσ in
theorem normSq_one_sub_ge {a z : ℂ} {t : ℝ} (ha : ‖a‖ ≤ t) (ht : t < 1) (hz : ‖z‖ < 1) :
    (1 - t) ^ 2 ≤ normSq (1 - a * z) := by
  rw [normSq_eq_norm_sq]
  have h1 : 1 - t ≤ ‖1 - a * z‖ := by
    have := norm_sub_norm_le (1 : ℂ) (a * z)
    rw [norm_one, norm_mul] at this
    have : ‖a‖ * ‖z‖ ≤ t := by
      calc ‖a‖ * ‖z‖ ≤ t * 1 := mul_le_mul ha hz.le (norm_nonneg _) ((norm_nonneg a).trans ha)
        _ = t := mul_one t
    linarith
  exact pow_le_pow_left₀ (by linarith) h1 2

omit hσ in
theorem im_exp_mul_ofReal (θ R : ℝ) : (exp ((θ : ℂ) * I) * (R : ℂ)).im = R * Real.sin θ := by
  rw [mul_im, exp_ofReal_mul_I_re, exp_ofReal_mul_I_im, ofReal_re, ofReal_im]
  ring

omit hσ in
theorem im_exp_neg_mul_ofReal (θ R : ℝ) :
    (exp (-((θ : ℂ) * I)) * (R : ℂ)).im = -(R * Real.sin θ) := by
  rw [show -((θ : ℂ) * I) = ((-θ : ℝ) : ℂ) * I by push_cast; ring, im_exp_mul_ofReal,
    Real.sin_neg]
  ring

omit hσ in
theorem eq_of_mob_eq_zero {v z : ℂ} (hd : 1 - conj v * z ≠ 0) (h : HypFold.mob v z = 0) :
    z = v := by
  rw [HypFold.mob, div_eq_zero_iff] at h
  rcases h with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hd

theorem mem_cover_of_wallZero {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 0 z = 0)
    (h0 : z ≠ 0) : z ∈ mainSet D ∪ discOne D ∪ discTwo D ∪ discThree D := by
  by_cases h2 : z = σ.vertexTwo
  · left; right; rw [h2]; exact mem_discTwo_vertexTwo hσ
  have hzT := hz
  obtain ⟨x, hx0, hx1, rfl⟩ := σ.eq_real_of_wallZero hz hw
  have hxp : 0 < x := lt_of_le_of_ne hx0 fun h => h0 (by rw [← h, ofReal_zero])
  have hxl : x < σ.sideTanTwo := lt_of_le_of_ne hx1 fun h => h2 (by rw [h, σ.vertexTwo_eq_real])
  have hs1 := sideTanTwo_lt_one hσ
  have hs2 := σ.sideTanTwo_pos
  have s2 := σ.sin_θ₂_pos
  have s3 := σ.sin_θ₃_pos
  have hk := kap_pos D hσ
  have e1 : σ.wallSide 1 (x : ℂ) = Real.sin σ.θ₃ * x := by
    rw [σ.wallSide_one_eq, ofReal_re, ofReal_im]; ring
  have hnz : ‖(x : ℂ)‖ = x := by rw [Complex.norm_real, Real.norm_of_nonneg hx0]
  by_cases hk1 : σ.wallSide 1 (x : ℂ) ≤ kap D
  · right
    change ‖(x : ℂ)‖ < radThree D
    rw [hnz]
    have := kap_lt_three D
    rw [e1] at hk1
    nlinarith
  have e2 : σ.wallSide 2 (x : ℂ) =
      Real.sin σ.θ₂ * ((σ.sideTanTwo - x) * (1 - σ.sideTanTwo * x)) := by
    rw [σ.wallSide_two_real, CompactShape.eps_of_hyp σ hσ, one_mul]
  have hdpos : 0 < 1 - σ.sideTanTwo * x := by nlinarith
  have hR := exp_neg_mul_rotTwo_real hσ (hxl.trans hs1)
  have hnR : ‖σ.rotTwo (x : ℂ)‖ = (σ.sideTanTwo - x) / (1 - σ.sideTanTwo * x) := by
    have := congrArg norm hR
    rw [norm_mul, show -((σ.θ₂ : ℂ) * I) = ((-σ.θ₂ : ℝ) : ℂ) * I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
      Real.norm_of_nonneg (div_nonneg (by linarith) hdpos.le)] at this
    exact this
  by_cases hk2 : σ.wallSide 2 (x : ℂ) ≤ kap D
  · left; right
    refine ⟨by rw [hnz]; linarith, ?_⟩
    rw [hnR, div_lt_iff₀ hdpos]
    have hrad := radTwo_pos D
    have hko := kap_lt_two D hσ
    have st3 : (1 - σ.sideTanTwo) ^ 2 ≤ (1 - σ.sideTanTwo * x) ^ 2 :=
      pow_le_pow_left₀ (by linarith) (by nlinarith) 2
    have st4 : Real.sin σ.θ₂ * (1 - σ.sideTanTwo * x) * (σ.sideTanTwo - x) <
        Real.sin σ.θ₂ * (1 - σ.sideTanTwo * x) * (radTwo D * (1 - σ.sideTanTwo * x)) := by
      have := mul_le_mul_of_nonneg_left st3 (mul_nonneg hrad.le s2.le)
      unfold cTwo at hko
      nlinarith
    exact lt_of_mul_lt_mul_left st4 (by positivity)
  left; left; left; left; left; right
  simp only [not_le] at hk1 hk2
  have hr : σ.refl 0 (x : ℂ) = x := by change conj (x : ℂ) = x; rw [conj_ofReal]
  refine ⟨D.foldWall_diff_subset_V 0 ⟨⟨hz, hw⟩, h0⟩, hk1, hk2, by rwa [hr], by rwa [hr],
    (D.re_f_wallZero ⟨hz, hw⟩ h0 h2).2, Or.inr ?_, Or.inr ?_⟩
  · rw [hR]
    exact ofReal_mem_wedgeSet (div_pos (by linarith) hdpos) (by linarith [σ.θ₂_pos])
  · exact ofReal_mem_wedgeSet hxp (by linarith [σ.θ₃_pos])

theorem mem_cover_of_wallTwo {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 2 z = 0)
    (h0 : z ≠ 0) : z ∈ mainSet D ∪ discOne D ∪ discTwo D ∪ discThree D := by
  by_cases h1 : z = σ.vertexOne
  · left; left; right; rw [h1]; exact mem_discOne_vertexOne hσ
  by_cases h2 : z = σ.vertexTwo
  · left; right; rw [h2]; exact mem_discTwo_vertexTwo hσ
  have hz1 : ‖z‖ < 1 := HypFold.norm_lt_one_of_mem hσ hz
  have hd2 := HypFold.one_sub_vertexTwo_mul_ne_zero hσ hz1
  have hd1 := HypFold.one_sub_conj_vertexOne_mul_ne_zero hσ hz1
  have hp2 := HypFold.normSq_pos_of_ne hd2
  have hk := kap_pos D hσ
  have ht1 := sideTanOne_lt_one hσ
  have ht2 := sideTanTwo_lt_one hσ
  have ht10 := σ.sideTanOne_pos
  have ht20 := σ.sideTanTwo_pos
  have s1 := σ.sin_θ₁_pos
  have s2 := σ.sin_θ₂_pos
  have him : (σ.rotTwo z).im = 0 := by
    have e := HypFold.wallSide_two_eq_rotTwo hσ z
    rw [hw] at e
    exact (mul_eq_zero.mp e.symm).resolve_right hp2.ne'
  set r := (σ.rotTwo z).re with hrdef
  have hrot : σ.rotTwo z = (r : ℂ) := Complex.ext (by simp [hrdef]) (by simp [him])
  have hr0 : 0 ≤ r := by
    have := (HypFold.sector_two hσ hz).2
    rw [hrot, im_exp_neg_mul_ofReal] at this
    nlinarith
  have hrne : r ≠ 0 := by
    intro h
    apply h2
    have h' : σ.rotTwo z = 0 := by rw [hrot, h, ofReal_zero]
    rw [HypFold.rotTwo_eq_mul_mob hσ] at h'
    have hne : -exp ((σ.θ₂ : ℂ) * I) ≠ 0 := neg_ne_zero.mpr (Complex.exp_ne_zero _)
    have hm := (mul_eq_zero.mp h').resolve_left hne
    exact eq_of_mob_eq_zero (by rw [HypFold.conj_vertexTwo (σ := σ)]; exact hd2) hm
  have hrp : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hrne)
  have hr1 : r < 1 := by
    have := HypFold.norm_rotTwo_lt_one hσ hz1
    rw [hrot, Complex.norm_real, Real.norm_of_nonneg hr0] at this
    exact this
  set s := HypFold.sideOneTwo σ with hsdef
  have hs0 : 0 < s := HypFold.sideOneTwo_pos hσ
  have hs1 : s < 1 := HypFold.sideOneTwo_lt_one hσ
  have hdr : 0 < 1 - s * r := by nlinarith
  have hR1 : exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z = (((s - r) / (1 - s * r) : ℝ) : ℂ) := by
    rw [HypFold.exp_neg_mul_rotOne hσ hz1, hrot, HypFold.mob, conj_ofReal]
    have : (1 : ℂ) - (s : ℂ) * r ≠ 0 := by exact_mod_cast hdr.ne'
    push_cast
    field_simp
    ring
  set R := (s - r) / (1 - s * r) with hRdef
  have hrotOne : σ.rotOne z = exp ((σ.θ₁ : ℂ) * I) * (R : ℂ) := by
    rw [← hR1, ← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
  have hR0 : 0 ≤ R := by
    have := (HypFold.sector_one hσ hz).1
    rw [hrotOne, im_exp_mul_ofReal] at this
    nlinarith
  have hRne : R ≠ 0 := by
    intro h
    apply h1
    have h' : σ.rotOne z = 0 := by rw [hrotOne, h, ofReal_zero, mul_zero]
    rw [HypFold.rotOne_eq_mul_mob hσ] at h'
    have hne : -exp (-((σ.θ₃ : ℂ) * I)) ≠ 0 := neg_ne_zero.mpr (Complex.exp_ne_zero _)
    exact eq_of_mob_eq_zero hd1 ((mul_eq_zero.mp h').resolve_left hne)
  have hRp : 0 < R := lt_of_le_of_ne hR0 (Ne.symm hRne)
  have hnR : ‖σ.rotOne z‖ = R := by
    rw [hrotOne, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, Complex.norm_real,
      Real.norm_of_nonneg hR0]
  by_cases hk0 : σ.wallSide 0 z ≤ kap D
  · left; right
    refine ⟨hz1, ?_⟩
    rw [hrot, Complex.norm_real, Real.norm_of_nonneg hr0]
    have e := HypFold.rotTwo_rot_im_mul_normSq hσ z
    rw [hrot, im_exp_neg_mul_ofReal] at e
    have hN : (1 - σ.sideTanTwo) ^ 2 ≤ normSq (1 - σ.vertexTwo * z) := by
      refine normSq_one_sub_ge ?_ ht2 hz1
      rw [σ.vertexTwo_eq_real, Complex.norm_real, Real.norm_of_nonneg ht20.le]
    have hw0 : 0 ≤ σ.wallSide 0 z := hz.2 0
    have hko := kap_lt_two D hσ
    have hrad := radTwo_pos D
    unfold cTwo at hko
    have st1 : r * Real.sin σ.θ₂ * normSq (1 - σ.vertexTwo * z) ≤ σ.wallSide 0 z := by
      nlinarith [mul_nonneg (sq_nonneg σ.sideTanTwo) hw0]
    have st2 : Real.sin σ.θ₂ * (1 - σ.sideTanTwo) ^ 2 * r <
        Real.sin σ.θ₂ * (1 - σ.sideTanTwo) ^ 2 * radTwo D := by
      have := mul_le_mul_of_nonneg_left hN (mul_nonneg hr0 s2.le)
      nlinarith
    exact lt_of_mul_lt_mul_left st2 (by nlinarith)
  by_cases hk1 : σ.wallSide 1 z ≤ kap D
  · left; left; right
    refine ⟨hz1, ?_⟩
    rw [hnR]
    have e := HypFold.rotOne_im_mul_normSq hσ hz1
    rw [hrotOne, im_exp_mul_ofReal] at e
    have hN : (1 - σ.sideTanOne) ^ 2 ≤ normSq (1 - conj σ.vertexOne * z) := by
      refine normSq_one_sub_ge ?_ ht1 hz1
      rw [Complex.norm_conj, σ.norm_vertexOne]
    have hw1 : 0 ≤ σ.wallSide 1 z := hz.2 1
    have hko := kap_lt_one D hσ
    have hc := cOne_le_two (σ := σ)
    have hrad := radOne_pos D
    change R * Real.sin σ.θ₁ * normSq (1 - conj σ.vertexOne * z) =
      (1 - σ.sideTanOne ^ 2) * σ.wallSide 1 z at e
    have st1 : R * Real.sin σ.θ₁ * normSq (1 - conj σ.vertexOne * z) ≤ σ.wallSide 1 z := by
      nlinarith [mul_nonneg (sq_nonneg σ.sideTanOne) hw1]
    have st2 : Real.sin σ.θ₁ * (1 - σ.sideTanOne) ^ 2 * R <
        Real.sin σ.θ₁ * (1 - σ.sideTanOne) ^ 2 * radOne D := by
      have := mul_le_mul_of_nonneg_left hN (mul_nonneg hR0 s1.le)
      have := mul_le_mul_of_nonneg_left hc hrad.le
      nlinarith
    exact lt_of_mul_lt_mul_left st2 (by nlinarith)
  left; left; left; right
  simp only [not_le] at hk0 hk1
  have hr : σ.refl 2 z = z := HypFold.refl_eq_self hσ 2 hz1 hw
  have hre := D.re_f_wallTwo ⟨hz, hw⟩ h1 h2
  have hfim := D.im_f_of_wall ⟨hz, hw⟩ h0
  refine ⟨D.foldWall_diff_subset_V 2 ⟨⟨hz, hw⟩, h0⟩, hk0, hk1, by rwa [hr], by rwa [hr],
    hre.1, hre.2, ?_, Or.inr ?_, Or.inr ?_⟩
  · rw [normSq_apply, hfim, mul_zero, add_zero]
    nlinarith [hre.1, hre.2]
  · rw [hR1]
    exact ofReal_mem_wedgeSet hRp (by linarith [σ.θ₁_pos])
  · rw [hrot]
    exact ofReal_mem_wedgeSet hrp (by linarith [σ.θ₂_pos])

theorem triangle_diff_subset_cover :
    σ.triangle \ {0} ⊆ mainSet D ∪ discOne D ∪ discTwo D ∪ discThree D := by
  rintro z ⟨hz, h0⟩
  have h0' : z ≠ 0 := h0
  by_cases hi : ∀ i, 0 < σ.wallSide i z
  · left; left; left; left; left; left; exact ⟨hz.1, hi⟩
  simp only [not_forall, not_lt] at hi
  obtain ⟨i, hi⟩ := hi
  have hw : σ.wallSide i z = 0 := le_antisymm hi (hz.2 i)
  fin_cases i
  · exact mem_cover_of_wallZero hσ hz hw h0'
  · exact mem_cover_of_wallOne hσ hz hw h0'
  · exact mem_cover_of_wallTwo hσ hz hw h0'

end Hyp

end ClosedTriangle

end GC.Seifert
