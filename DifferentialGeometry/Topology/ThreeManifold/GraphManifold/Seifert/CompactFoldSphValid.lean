import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldSphLayout
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldSphWalls

/-!
# Pointwise validity facts on the spherical triangle

Lane CF-S3, tier 3, curvature `+4` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §5, review 23 §6.1). Facts at single points of the
triangle `T`, used by the open pieces, their cover of `T` and the injectivity of `sphPreFold`:
* far from the other vertices: on `T` the canonical sums `Tᵢ + Tⱼ` are nonnegative, so a point
  inside the canonical disc of one vertex lies outside the canonical discs of the two others
  (`sphDist_gt_of_cornerOne`, `sphDist_gt_of_cornerTwo`, `sphDist_gt_of_outer`);
* strict real parts of the bridges: `3/2 < Re M₁` inside the canonical disc of `v₁`,
  `Re M₀ < -3/2` inside that of `v₂`, `|Re M₂| < 3/2` everywhere, from the moduli bounds;
* the lens stays away from `v₃ = 0`: a point of `T` outside the corner disc of `v₁` with side
  coordinate `Im rotTwo ≤ sphSwitchTop` is horizontally within `9s/512` of the contact point
  `τ₂` (the bound of `sphInCore_of_band`), so `T₂ < s/4`, hence `T₃ > -s/4` and
  `‖z‖ > τ₃/2` (`sph_norm_gt_of_lens`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace CompactShape

variable {σ : CompactShape}

section Spherical

variable (hs : σ.curv = .spherical)
include hs

theorem sphCanon_neg_of_lt_sph {j : Fin 3} {z : ℂ} (h : σ.sphDist j z < σ.sphTau j) :
    σ.sphCanon j z < 0 :=
  div_neg_of_neg_of_pos (by linarith) (one_add_sphDist_mul_pos hs j z)

theorem sphCanon_nonpos_of_le_sph {j : Fin 3} {z : ℂ} (h : σ.sphDist j z ≤ σ.sphTau j) :
    σ.sphCanon j z ≤ 0 :=
  div_nonpos_of_nonpos_of_nonneg (by linarith) (one_add_sphDist_mul_pos hs j z).le

theorem lt_sphDist_of_pos_sph {j : Fin 3} {z : ℂ} (h : 0 < σ.sphCanon j z) :
    σ.sphTau j < σ.sphDist j z := by
  rw [sphCanon, lt_div_iff₀ (one_add_sphDist_mul_pos hs j z), zero_mul] at h
  linarith

theorem sphDist_gt_of_lt_tau_zero {z : ℂ} (hz : z ∈ σ.triangle) (h : ‖σ.rotOne z‖ < σ.sphTau 0) :
    σ.sphTau 1 < ‖σ.rotTwo z‖ ∧ σ.sphTau 2 < ‖z‖ := by
  have hc := sphCanon_neg_of_lt_sph hs (j := 0) h
  have a := sphCanon_add_two_nonneg hs hz
  have b := sphCanon_add_one_nonneg hs hz
  exact ⟨lt_sphDist_of_pos_sph hs (j := 1) (by linarith),
    lt_sphDist_of_pos_sph hs (j := 2) (by linarith)⟩

theorem sphDist_gt_of_lt_tau_one {z : ℂ} (hz : z ∈ σ.triangle) (h : ‖σ.rotTwo z‖ < σ.sphTau 1) :
    σ.sphTau 0 < ‖σ.rotOne z‖ ∧ σ.sphTau 2 < ‖z‖ := by
  have hc := sphCanon_neg_of_lt_sph hs (j := 1) h
  have a := sphCanon_add_two_nonneg hs hz
  have b := sphCanon_add_zero_nonneg hs hz
  exact ⟨lt_sphDist_of_pos_sph hs (j := 0) (by linarith),
    lt_sphDist_of_pos_sph hs (j := 2) (by linarith)⟩

theorem sphDist_gt_of_cornerOne {z : ℂ} (hz : z ∈ σ.triangle)
    (h : ‖σ.rotOne z‖ ≤ σ.sphCornerRad 0) :
    σ.sphTau 1 < ‖σ.rotTwo z‖ ∧ σ.sphTau 2 < ‖z‖ :=
  sphDist_gt_of_lt_tau_zero hs hz (h.trans_lt (sphCornerRad_bounds hs 0).2)

theorem sphDist_gt_of_cornerTwo {z : ℂ} (hz : z ∈ σ.triangle)
    (h : ‖σ.rotTwo z‖ ≤ σ.sphCornerRad 1) :
    σ.sphTau 0 < ‖σ.rotOne z‖ ∧ σ.sphTau 2 < ‖z‖ :=
  sphDist_gt_of_lt_tau_one hs hz (h.trans_lt (sphCornerRad_bounds hs 1).2)

theorem sphDist_gt_of_outer {z : ℂ} (hz : z ∈ σ.triangle) (h : ‖z‖ < σ.sphTau 2) :
    σ.sphTau 0 < ‖σ.rotOne z‖ ∧ σ.sphTau 1 < ‖σ.rotTwo z‖ := by
  have hc := sphCanon_neg_of_lt_sph hs (j := 2) h
  have a := sphCanon_add_one_nonneg hs hz
  have b := sphCanon_add_zero_nonneg hs hz
  exact ⟨lt_sphDist_of_pos_sph hs (j := 0) (by linarith),
    lt_sphDist_of_pos_sph hs (j := 1) (by linarith)⟩

theorem three_halves_lt_re_sphBridgeOne {z : ℂ} (hz : z ∈ σ.triangle)
    (h : ‖σ.rotOne z‖ ≤ σ.sphTau 0) : 3 / 2 < (σ.sphBridgeOne z).re := by
  have hA := sphModThree_mem hs hz
  have hB := sphModOne_mem hs hz
  have hc := sphCanon_nonpos_of_le_sph hs (j := 0) h
  have hle : σ.sphModOne z ≤ 3 / 2 := by
    unfold sphModOne compactProfileSlope
    linarith
  rw [sphBridgeOne, twoCircle_re]
  have e : (0 : ℝ) + (σ.sphModThree z ^ 2 - σ.sphModOne z ^ 2 + (3 / 2 - 0) ^ 2) /
      (2 * (3 / 2 - 0)) = (σ.sphModThree z ^ 2 - σ.sphModOne z ^ 2 + 9 / 4) / 3 := by ring
  rw [e, lt_div_iff₀ (by norm_num)]
  nlinarith

theorem re_sphBridgeZero_lt_sph {z : ℂ} (hz : z ∈ σ.triangle)
    (h : ‖σ.rotTwo z‖ ≤ σ.sphTau 1) : (σ.sphBridgeZero z).re < -(3 / 2) := by
  have hA := sphModThree_mem hs hz
  have hB := sphModTwo_mem hs hz
  have hc := sphCanon_nonpos_of_le_sph hs (j := 1) h
  have hle : σ.sphModTwo z ≤ 3 / 2 := by
    unfold sphModTwo compactProfileSlope
    linarith
  rw [sphBridgeZero, twoCircle_re]
  have e : (0 : ℝ) + (σ.sphModThree z ^ 2 - σ.sphModTwo z ^ 2 + (-(3 / 2) - 0) ^ 2) /
      (2 * (-(3 / 2) - 0)) = -((σ.sphModThree z ^ 2 - σ.sphModTwo z ^ 2 + 9 / 4) / 3) := by
    ring
  rw [e, neg_lt_neg_iff, lt_div_iff₀ (by norm_num)]
  nlinarith

theorem re_sphBridgeTwo_mem_sph {z : ℂ} (hz : z ∈ σ.triangle) :
    -(3 / 2) < (σ.sphBridgeTwo z).re ∧ (σ.sphBridgeTwo z).re < 3 / 2 := by
  have hA := sphModOne_mem hs hz
  have hB := sphModTwo_mem hs hz
  rw [sphBridgeTwo, twoCircle_re]
  have e : (3 / 2 : ℝ) + (σ.sphModOne z ^ 2 - σ.sphModTwo z ^ 2 + (-(3 / 2) - 3 / 2) ^ 2) /
      (2 * (-(3 / 2) - 3 / 2)) = (σ.sphModTwo z ^ 2 - σ.sphModOne z ^ 2) / 6 := by ring
  rw [e]
  constructor
  · rw [lt_div_iff₀ (by norm_num)]
    nlinarith
  · rw [div_lt_iff₀ (by norm_num)]
    nlinarith

theorem re_rotTwo_le_of_mem_sph {z : ℂ} (hz : z ∈ σ.triangle) :
    (σ.rotTwo z).re ≤ σ.sphTOneTwo := by
  have hq := re_sphMoeb_nonpos_of_mem hs hz
  set ζ := σ.rotTwo z
  set t := σ.sphTOneTwo
  have ht := tOneTwo_pos_sph hs
  have hx := re_rotTwo_nonneg_sph hs hz
  have hden : 0 < Complex.normSq (1 + (t : ℂ) * ζ) := by
    rw [normSq_one_add_real_sph]
    positivity
  have hre : (sphMoeb (t : ℂ) ζ).re * Complex.normSq (1 + (t : ℂ) * ζ) =
      ζ.re * (1 - t ^ 2) + t * (ζ.re ^ 2 + ζ.im ^ 2) - t := by
    rw [sphMoeb, Complex.conj_ofReal, Complex.div_re, add_mul, div_mul_cancel₀ _ hden.ne',
      div_mul_cancel₀ _ hden.ne']
    simp only [sub_re, sub_im, add_re, add_im, mul_re, mul_im, ofReal_re, ofReal_im, one_re,
      one_im]
    ring
  have hA : ζ.re * (1 - t ^ 2) + t * (ζ.re ^ 2 + ζ.im ^ 2) - t ≤ 0 := by
    rw [← hre]
    exact mul_nonpos_of_nonpos_of_nonneg hq hden.le
  by_contra hc
  push Not at hc
  have h1 : 0 < (ζ.re - t) * (1 + t * ζ.re) := mul_pos (by linarith) (by positivity)
  have h2 : 0 ≤ t * ζ.im ^ 2 := by positivity
  nlinarith

theorem sph_re_rotTwo_le_of_band {z : ℂ} (hz : z ∈ σ.triangle)
    (hy : σ.sphSideTwo z ≤ σ.sphSwitchTop)
    (h1 : σ.sphCornerRad 0 ≤ ‖σ.rotOne z‖) :
    (σ.rotTwo z).re ≤ σ.sphTau 1 + 9 * σ.sphScale / 512 := by
  have hv1 := one_add_conj_vertexOne_ne_sph hs hz
  have hv2 : 1 + conj σ.vertexTwo * z ≠ 0 := by
    rw [conj_vertexTwo_sph]
    exact one_add_vertexTwo_ne_sph hs hz
  rw [norm_rotOne_eq_sphMoeb_rotTwo hs hv1 hv2] at h1
  have hy0 : 0 ≤ (σ.rotTwo z).im := (sector_two_sph hs hz).1
  have hy' : (σ.rotTwo z).im ≤ σ.sphScale / 8 := hy
  have hx0 : 0 ≤ (σ.rotTwo z).re := re_rotTwo_nonneg_sph hs hz
  have hxt := re_rotTwo_le_of_mem_sph hs hz
  set ζ := σ.rotTwo z with hζ
  set t := σ.sphTOneTwo
  set x := ζ.re
  set y := ζ.im
  have hs0 := sphScale_pos hs
  have hle0 := sphScale_le_tau hs 0
  have hle1 := sphScale_le_tau hs 1
  have t0 := sphTau_pos hs 0
  have t1 := sphTau_pos hs 1
  have u1 := sphTau_lt_one hs 1
  have ht := tOneTwo_pos_sph hs
  obtain ⟨c0l, c0u⟩ := sphCornerRad_bounds hs 0
  have hdd : σ.sphCornerShrink = σ.sphScale / 256 := rfl
  set c₁ := σ.sphCornerRad 0
  set d := σ.sphCornerShrink
  set τ₂ := σ.sphTau 1
  have hc1s : 8 * σ.sphScale < c₁ := by linarith
  have ht' : (0 : ℝ) < t := ht
  have hup : x ≤ (τ₂ + d) / (1 - τ₂ * d) + σ.sphScale / 512 := by
    have hq : c₁ ^ 2 * ((1 + t * x) ^ 2 + t ^ 2 * y ^ 2) ≤ (x - t) ^ 2 + y ^ 2 := by
      have hn := sq_norm_sphMoeb_real t ζ (by positivity)
      have : c₁ ^ 2 ≤ ‖sphMoeb (t : ℂ) ζ‖ ^ 2 := pow_le_pow_left₀ (by linarith) h1 2
      rw [← hn]
      exact mul_le_mul_of_nonneg_right this (by positivity)
    have hu := sub_tan_cornerRad hs
    set u := (τ₂ + d) / (1 - τ₂ * d)
    have hct : 0 < 1 + t * c₁ := by
      have := mul_pos ht' (by linarith : (0 : ℝ) < c₁)
      linarith
    have hu' : t - c₁ = u * (1 + t * c₁) := (div_eq_iff hct.ne').1 hu
    have hP : c₁ ≤ (t - x) + c₁ * (1 + t * x) := by
      have : (0 : ℝ) ≤ c₁ * t * x := mul_nonneg (mul_nonneg (by linarith) ht'.le) hx0
      nlinarith
    have hfac : (1 + t * c₁) * (u - x) * ((t - x) + c₁ * (1 + t * x)) ≥ -y ^ 2 := by
      have e : (1 + t * c₁) * (u - x) = (t - x) - c₁ * (1 + t * x) := by
        linear_combination (-1 : ℝ) * hu'
      rw [e]
      have : c₁ ^ 2 * t ^ 2 * y ^ 2 ≥ 0 := by positivity
      nlinarith
    have hyb : y ^ 2 ≤ (σ.sphScale / 8) ^ 2 := pow_le_pow_left₀ hy0 hy' 2
    by_contra hc
    push Not at hc
    have hux : σ.sphScale / 512 < x - u := by linarith
    have hct' : 1 ≤ 1 + t * c₁ := by
      have := mul_pos ht' (by linarith : (0 : ℝ) < c₁)
      linarith
    have hA : σ.sphScale / 512 ≤ (1 + t * c₁) * (x - u) := by
      have := mul_le_mul hct' hux.le (by positivity) (by linarith)
      linarith
    have hB : σ.sphScale / 512 * c₁ ≤ (1 + t * c₁) * (x - u) * ((t - x) + c₁ * (1 + t * x)) :=
      mul_le_mul hA hP (by linarith) (by linarith)
    have e2 : (1 + t * c₁) * (x - u) * ((t - x) + c₁ * (1 + t * x)) =
        -((1 + t * c₁) * (u - x) * ((t - x) + c₁ * (1 + t * x))) := by ring
    have hC := mul_lt_mul_of_pos_left hc1s (by positivity : (0 : ℝ) < σ.sphScale / 512)
    have hs2 : 0 < σ.sphScale * σ.sphScale := mul_pos hs0 hs0
    nlinarith
  have hd0 : 0 < d := by rw [hdd]; positivity
  have hdτ : d ≤ τ₂ / 4096 := by rw [hdd]; linarith
  have hτd1 : τ₂ * d ≤ d := by
    have := mul_le_mul_of_nonneg_right u1.le hd0.le
    linarith
  have hτd : τ₂ * d ≤ 1 / 2 := by linarith
  have hττd : τ₂ * τ₂ * d ≤ d := by
    have h1' := mul_le_mul_of_nonneg_right u1.le (mul_nonneg t1.le hd0.le)
    nlinarith only [h1', hτd1]
  have hue : (τ₂ + d) / (1 - τ₂ * d) - τ₂ ≤ 4 * d := by
    have hden : 0 < 1 - τ₂ * d := by linarith
    rw [sub_le_iff_le_add, div_le_iff₀ hden]
    have : 0 ≤ τ₂ * d * d := by positivity
    nlinarith only [hττd, this, hd0, hτd, t1]
  linarith [hdd]

theorem sph_norm_gt_of_lens {z : ℂ} (hz : z ∈ σ.triangle) (hy : σ.sphSideTwo z ≤ σ.sphSwitchTop)
    (h1 : σ.sphCornerRad 0 ≤ ‖σ.rotOne z‖) : σ.sphTau 2 / 2 < ‖z‖ := by
  have hx := sph_re_rotTwo_le_of_band hs hz hy h1
  have hy0 : 0 ≤ (σ.rotTwo z).im := (sector_two_sph hs hz).1
  have hy' : (σ.rotTwo z).im ≤ σ.sphScale / 8 := hy
  have hx0 : 0 ≤ (σ.rotTwo z).re := re_rotTwo_nonneg_sph hs hz
  have hs0 := sphScale_pos hs
  have hle2 := sphScale_le_tau hs 2
  have t1 := sphTau_pos hs 1
  have t2 := sphTau_pos hs 2
  have u2 := sphTau_lt_one hs 2
  have hn : ‖σ.rotTwo z‖ ≤ σ.sphTau 1 + 73 * σ.sphScale / 512 := by
    have := Complex.norm_le_abs_re_add_abs_im (σ.rotTwo z)
    rw [abs_of_nonneg hx0, abs_of_nonneg hy0] at this
    linarith
  have hT2 : σ.sphCanon 1 z ≤ 73 * σ.sphScale / 512 := by
    rw [sphCanon, div_le_iff₀ (one_add_sphDist_mul_pos hs 1 z)]
    change ‖σ.rotTwo z‖ - σ.sphTau 1 ≤ 73 * σ.sphScale / 512 * (1 + ‖σ.rotTwo z‖ * σ.sphTau 1)
    have : 0 ≤ 73 * σ.sphScale / 512 * (‖σ.rotTwo z‖ * σ.sphTau 1) := by positivity
    nlinarith
  have hsum := sphCanon_add_zero_nonneg hs hz
  by_contra hc
  push Not at hc
  have hT3 : σ.sphCanon 2 z ≤ -(σ.sphTau 2 / 3) := by
    rw [sphCanon, div_le_iff₀ (one_add_sphDist_mul_pos hs 2 z)]
    change ‖z‖ - σ.sphTau 2 ≤ -(σ.sphTau 2 / 3) * (1 + ‖z‖ * σ.sphTau 2)
    have h0 := norm_nonneg z
    have h3 : ‖z‖ * σ.sphTau 2 ≤ ‖z‖ := mul_le_of_le_one_right h0 u2.le
    have h4 : ‖z‖ * σ.sphTau 2 * σ.sphTau 2 ≤ ‖z‖ :=
      (mul_le_of_le_one_right (by positivity) u2.le).trans h3
    nlinarith
  linarith

end Spherical

end CompactShape

end GC.Seifert
