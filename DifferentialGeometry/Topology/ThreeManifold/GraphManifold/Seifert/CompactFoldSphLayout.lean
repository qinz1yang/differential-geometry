import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldSphPieces

/-!
# Layout certificates of the spherical fold in the coordinate of wall 2

Lane CF-S, tier 3, curvature `+4` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §5, review 23 §6.1). In the coordinate
`ζ = rotTwo z = x + iy` wall 2 is the segment `[0, t₁₂]` of the real axis, `v₂ = 0`, `v₁ = t₁₂`,
and the chordal distances to `v₂`, `v₁` are `‖ζ‖` and `‖q‖`, `q = sphMoeb t₁₂ ζ`. On the triangle
`x ≥ 0` and `Re q ≤ 0` (the sector at `v₁`, `re_sphMoeb_nonpos_of_mem`), hence `x < t₁₂` above the
real axis. Outside the corner disc of `v₂` (`‖ζ‖ ≥ c₂`) a point of height `y ≤ β'` has
`x ≥ c₂ - β'²/c₂`; outside the corner disc of `v₁` (`‖q‖ ≥ c₁`) it has `x ≤ (t₁₂ ⊖ c₁) + y²/c₁`, and
`t₁₂ ⊖ c₁ = τ₂ ⊕ shrink` (`sub_tan_cornerRad`). So the lens arc and the switch windows, which lie
in the band `β ≤ y ≤ β'` outside both corner discs, are within `5s/512` of the contact point
`τ₂` horizontally, and they lie in the shrunk core disc about `τ₂ + i s/2`
(`sphInCore_of_band`).
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

theorem re_sphMoeb_nonpos_of_mem {z : ℂ} (hz : z ∈ σ.triangle) :
    (sphMoeb σ.sphTOneTwo (σ.rotTwo z)).re ≤ 0 := by
  have h1 := one_add_conj_vertexOne_ne_sph hs hz
  have h2 : 1 + conj σ.vertexTwo * z ≠ 0 := by
    rw [conj_vertexTwo_sph]
    exact one_add_vertexTwo_ne_sph hs hz
  obtain ⟨a, b⟩ := sector_one_sph hs hz
  have e := rotOne_eq_rotTwo_sph hs h1 h2
  set q := sphMoeb (σ.sphTOneTwo : ℂ) (σ.rotTwo z)
  have hq : q = -(exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z) := by
    rw [e]
    have := exp_mul_exp_neg_sph σ.θ₁
    linear_combination (-q) * this
  rw [hq, neg_re, exp_neg_ofReal_mul_I_sph]
  simp only [mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_neg,
    Real.sin_neg]
  rw [im_exp_mul_conj_sph] at b
  have hc := σ.cos_θ₁_nonneg_sph
  have hsn := σ.sin_θ₁_pos_sph
  nlinarith [mul_nonneg hc (re_rotOne_nonneg_sph hs hz), mul_nonneg hsn.le a]

theorem re_rotTwo_lt_of_mem {z : ℂ} (hz : z ∈ σ.triangle) (hy : 0 < (σ.rotTwo z).im) :
    (σ.rotTwo z).re < σ.sphTOneTwo := by
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
  have := mul_pos ht (pow_pos hy 2)
  nlinarith [mul_nonneg (sub_nonneg.2 hc) (sub_nonneg.2 hc), mul_nonneg ht.le hx]


theorem sub_tan_cornerRad :
    (σ.sphTOneTwo - σ.sphCornerRad 0) / (1 + σ.sphTOneTwo * σ.sphCornerRad 0) =
      (σ.sphTau 1 + σ.sphCornerShrink) / (1 - σ.sphTau 1 * σ.sphCornerShrink) := by
  have hplus := sphTau_oplus_onetwo hs
  have t0 := sphTau_pos hs 0
  have t1 := sphTau_pos hs 1
  have u0 := sphTau_lt_one hs 0
  have u1 := sphTau_lt_one hs 1
  have hs0 := sphScale_pos hs
  have hle := sphScale_le_tau hs 1
  have hd : 0 < σ.sphCornerShrink := by unfold sphCornerShrink; positivity
  have hd1 : σ.sphCornerShrink < 1 := by unfold sphCornerShrink; linarith
  have hm : 0 < 1 - σ.sphTau 0 * σ.sphTau 1 := by nlinarith
  have ht : σ.sphTOneTwo = (σ.sphTau 0 + σ.sphTau 1) / (1 - σ.sphTau 0 * σ.sphTau 1) := by
    rw [eq_div_iff hm.ne']
    linarith
  have hden1 : 0 < 1 + σ.sphTau 0 * σ.sphCornerShrink := by positivity
  have hden2 : 0 < 1 - σ.sphTau 1 * σ.sphCornerShrink := by nlinarith
  have hc : σ.sphCornerRad 0 = (σ.sphTau 0 - σ.sphCornerShrink) /
      (1 + σ.sphTau 0 * σ.sphCornerShrink) := rfl
  have hD : 0 < 1 + σ.sphTOneTwo * σ.sphCornerRad 0 := by
    have := (sphCornerRad_bounds hs 0).1
    have := tOneTwo_pos_sph hs
    nlinarith
  rw [div_eq_div_iff hD.ne' hden2.ne', ht, hc]
  field_simp
  ring

theorem sphInCore_of_band {z : ℂ} (hz : z ∈ σ.triangle)
    (hy1 : σ.sphLensWidth ≤ (σ.rotTwo z).im) (hy2 : (σ.rotTwo z).im ≤ σ.sphSwitchTop)
    (h2 : σ.sphCornerRad 1 ≤ ‖σ.rotTwo z‖)
    (h1 : σ.sphCornerRad 0 ≤ ‖sphMoeb σ.sphTOneTwo (σ.rotTwo z)‖) : σ.sphInCore z := by
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
  obtain ⟨c1l, c1u⟩ := sphCornerRad_bounds hs 1
  have hβ : σ.sphLensWidth = σ.sphScale / 16 := rfl
  have hβ' : σ.sphSwitchTop = σ.sphScale / 8 := rfl
  have hdd : σ.sphCornerShrink = σ.sphScale / 256 := rfl
  have hy0 : 0 < y := by rw [hβ] at hy1; linarith
  have hx0 : 0 ≤ x := re_rotTwo_nonneg_sph hs hz
  have hxt : x < t := re_rotTwo_lt_of_mem hs hz hy0
  have ht' : (0 : ℝ) < t := ht
  set c₁ := σ.sphCornerRad 0
  set c₂ := σ.sphCornerRad 1
  set d := σ.sphCornerShrink
  set τ₂ := σ.sphTau 1
  have hc1s : 8 * σ.sphScale < c₁ := by linarith
  have hc2s : 8 * σ.sphScale < c₂ := by linarith
  have hlow : c₂ - σ.sphScale / 512 ≤ x := by
    have hsq : c₂ ^ 2 ≤ x ^ 2 + y ^ 2 := by
      rw [← CompactShape.sq_norm_eq_sph ζ]
      exact pow_le_pow_left₀ (by linarith) h2 2
    have hyb : y ^ 2 ≤ (σ.sphScale / 8) ^ 2 := by
      rw [hβ'] at hy2
      exact pow_le_pow_left₀ hy0.le hy2 2
    by_contra hc
    push Not at hc
    have hpos : 0 ≤ x := hx0
    have hx2 : x ^ 2 < (c₂ - σ.sphScale / 512) ^ 2 :=
      pow_lt_pow_left₀ hc hpos two_ne_zero
    nlinarith only [hx2, hsq, hyb, hc2s, hs0]
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
    have hyb : y ^ 2 ≤ (σ.sphScale / 8) ^ 2 := by
      rw [hβ'] at hy2
      exact pow_le_pow_left₀ hy0.le hy2 2
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
  have hc2e : τ₂ - c₂ ≤ 2 * d := by
    have hden : 0 < 1 + τ₂ * d := by positivity
    have : c₂ = (τ₂ - d) / (1 + τ₂ * d) := rfl
    rw [this, sub_le_iff_le_add, ← sub_le_iff_le_add', le_div_iff₀ hden]
    have : 0 ≤ τ₂ * d * d := by positivity
    nlinarith only [hττd, this, hd0]
  have hue : (τ₂ + d) / (1 - τ₂ * d) - τ₂ ≤ 4 * d := by
    have hden : 0 < 1 - τ₂ * d := by linarith
    rw [sub_le_iff_le_add, div_le_iff₀ hden]
    have : 0 ≤ τ₂ * d * d := by positivity
    nlinarith only [hττd, this, hd0, hτd, t1]
  have hxm : |x - τ₂| ≤ 9 * σ.sphScale / 512 := by
    rw [abs_le]
    constructor <;> linarith
  have hcen : σ.rotTwo z - σ.sphCoreCenter =
      ((x - τ₂ : ℝ) : ℂ) + ((y - σ.sphScale / 2 : ℝ) : ℂ) * I := by
    apply Complex.ext <;> simp [sphCoreCenter, x, y, τ₂, ζ]
  have hn : ‖σ.rotTwo z - σ.sphCoreCenter‖ ^ 2 = (x - τ₂) ^ 2 + (y - σ.sphScale / 2) ^ 2 := by
    rw [hcen, CompactShape.sq_norm_eq_sph]
    simp
  have hR : σ.sphCoreRadius - σ.sphCoreMargin = 59 * σ.sphScale / 128 := by
    unfold sphCoreRadius sphCoreMargin
    rw [hβ]
    ring
  unfold sphInCore
  rw [hR]
  have hxb : (x - τ₂) ^ 2 ≤ (9 * σ.sphScale / 512) ^ 2 := by
    rw [← sq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) hxm 2
  have hyb : (y - σ.sphScale / 2) ^ 2 ≤ (7 * σ.sphScale / 16) ^ 2 := by
    rw [hβ] at hy1
    rw [hβ'] at hy2
    nlinarith only [hy1, hy2, hs0]
  have hlt : ‖σ.rotTwo z - σ.sphCoreCenter‖ ^ 2 < (59 * σ.sphScale / 128) ^ 2 := by
    rw [hn]
    nlinarith only [hxb, hyb, hs0]
  exact (pow_lt_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).1 hlt


theorem sphScale_le_tau_sin :
    σ.sphScale ≤ σ.sphTau 0 * Real.sin σ.θ₁ / 16 ∧
      σ.sphScale ≤ σ.sphTau 1 * Real.sin σ.θ₂ / 16 := by
  have t0 := sphTau_pos hs 0
  have t1 := sphTau_pos hs 1
  have t2 := sphTau_pos hs 2
  have u0 := sphTau_lt_one hs 0
  have u1 := sphTau_lt_one hs 1
  have u2 := sphTau_lt_one hs 2
  have s1 := σ.sin_θ₁_pos_sph
  have s2 := σ.sin_θ₂_pos_sph
  have s3 := σ.sin_θ₃_pos_sph
  have l1 := Real.sin_le_one σ.θ₁
  have l2 := Real.sin_le_one σ.θ₂
  have l3 := Real.sin_le_one σ.θ₃
  have a : σ.sphTau 1 * σ.sphTau 2 * (Real.sin σ.θ₂ * Real.sin σ.θ₃) ≤ 1 := by
    have h1 : σ.sphTau 1 * σ.sphTau 2 ≤ 1 := by nlinarith
    have h2 : Real.sin σ.θ₂ * Real.sin σ.θ₃ ≤ 1 := by nlinarith
    have h3 : 0 ≤ Real.sin σ.θ₂ * Real.sin σ.θ₃ := by positivity
    nlinarith
  have b : σ.sphTau 0 * σ.sphTau 2 * (Real.sin σ.θ₁ * Real.sin σ.θ₃) ≤ 1 := by
    have h1 : σ.sphTau 0 * σ.sphTau 2 ≤ 1 := by nlinarith
    have h2 : Real.sin σ.θ₁ * Real.sin σ.θ₃ ≤ 1 := by nlinarith
    have h3 : 0 ≤ Real.sin σ.θ₁ * Real.sin σ.θ₃ := by positivity
    nlinarith
  have p0 : 0 ≤ σ.sphTau 0 * Real.sin σ.θ₁ := by positivity
  have p1 : 0 ≤ σ.sphTau 1 * Real.sin σ.θ₂ := by positivity
  unfold sphScale
  constructor
  · have e : σ.sphTau 0 * σ.sphTau 1 * σ.sphTau 2 *
        (Real.sin σ.θ₁ * Real.sin σ.θ₂ * Real.sin σ.θ₃) =
        (σ.sphTau 0 * Real.sin σ.θ₁) * (σ.sphTau 1 * σ.sphTau 2 *
          (Real.sin σ.θ₂ * Real.sin σ.θ₃)) := by ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left a p0]
  · have e : σ.sphTau 0 * σ.sphTau 1 * σ.sphTau 2 *
        (Real.sin σ.θ₁ * Real.sin σ.θ₂ * Real.sin σ.θ₃) =
        (σ.sphTau 1 * Real.sin σ.θ₂) * (σ.sphTau 0 * σ.sphTau 2 *
          (Real.sin σ.θ₁ * Real.sin σ.θ₃)) := by ring
    rw [e]
    nlinarith [mul_le_mul_of_nonneg_left b p1]


theorem sphCore_band {ζ : ℂ} (hc : ‖ζ - σ.sphCoreCenter‖ < σ.sphCoreRadius + σ.sphCoreMargin) :
    σ.sphTau 1 - σ.sphScale / 2 < ζ.re ∧ ζ.re < σ.sphTau 1 + σ.sphScale / 2 ∧
      0 < ζ.im ∧ ζ.im < σ.sphScale := by
  have hs0 := sphScale_pos hs
  have hR : σ.sphCoreRadius + σ.sphCoreMargin = σ.sphScale / 2 - 3 * (σ.sphScale / 16) / 8 := by
    unfold sphCoreRadius sphCoreMargin sphLensWidth
    ring
  have hre : (ζ - σ.sphCoreCenter).re = ζ.re - σ.sphTau 1 := by simp [sphCoreCenter]
  have him : (ζ - σ.sphCoreCenter).im = ζ.im - σ.sphScale / 2 := by simp [sphCoreCenter]
  have h1 := Complex.abs_re_le_norm (ζ - σ.sphCoreCenter)
  have h2 := Complex.abs_im_le_norm (ζ - σ.sphCoreCenter)
  rw [hre] at h1
  rw [him] at h2
  rw [hR] at hc
  obtain ⟨r1, r2⟩ := abs_le.1 h1
  obtain ⟨i1, i2⟩ := abs_le.1 h2
  refine ⟨by linarith, by linarith, by linarith, by linarith⟩

theorem sphCore_ineqs {ζ : ℂ}
    (hc : ‖ζ - σ.sphCoreCenter‖ < σ.sphCoreRadius + σ.sphCoreMargin) :
    0 < ζ.im ∧ 0 < Real.sin σ.θ₂ * ζ.re - Real.cos σ.θ₂ * ζ.im ∧
      0 < Real.sin σ.θ₁ * σ.sphTOneTwo * (1 - ‖ζ‖ ^ 2) -
        Real.sin σ.θ₁ * (1 - σ.sphTOneTwo ^ 2) * ζ.re -
        Real.cos σ.θ₁ * (1 + σ.sphTOneTwo ^ 2) * ζ.im := by
  obtain ⟨x1, x2, y0, y1⟩ := sphCore_band hs hc
  have hs0 := sphScale_pos hs
  obtain ⟨k1, k2⟩ := sphScale_le_tau_sin hs
  have hle0 := sphScale_le_tau hs 0
  have hle1 := sphScale_le_tau hs 1
  have t0 := sphTau_pos hs 0
  have t1 := sphTau_pos hs 1
  have u0 := sphTau_lt_one hs 0
  have sn1 := σ.sin_θ₁_pos_sph
  have sn2 := σ.sin_θ₂_pos_sph
  have cs1 := σ.cos_θ₁_nonneg_sph
  have cl1 := Real.cos_le_one σ.θ₁
  have cl2 := Real.cos_le_one σ.θ₂
  have sl1 := Real.sin_le_one σ.θ₁
  have ht := tOneTwo_pos_sph hs
  have ht1 := tOneTwo_le_one_sph hs
  have hplus := sphTau_oplus_onetwo hs
  set x := ζ.re
  set y := ζ.im
  set t := σ.sphTOneTwo
  set s := σ.sphScale
  set τ₀ := σ.sphTau 0
  set τ₁ := σ.sphTau 1
  have htτ : τ₁ + τ₀ ≤ t := by
    have := mul_pos (mul_pos t0 t1) ht
    nlinarith only [hplus, this]
  have hs1 : s ≤ 1 := by linarith
  refine ⟨y0, ?_, ?_⟩
  · have hx : τ₁ * (31 / 32) < x := by linarith
    have a1 : Real.sin σ.θ₂ * (τ₁ * (31 / 32)) < Real.sin σ.θ₂ * x :=
      mul_lt_mul_of_pos_left hx sn2
    have a2 : Real.cos σ.θ₂ * y ≤ y := mul_le_of_le_one_left y0.le cl2
    linarith
  · have hn : ‖ζ‖ ^ 2 = x ^ 2 + y ^ 2 := sq_norm_eq_sph ζ
    rw [hn]
    have e : Real.sin σ.θ₁ * t * (1 - (x ^ 2 + y ^ 2)) - Real.sin σ.θ₁ * (1 - t ^ 2) * x -
        Real.cos σ.θ₁ * (1 + t ^ 2) * y =
        Real.sin σ.θ₁ * ((t - x) * (1 + t * x)) - Real.sin σ.θ₁ * (t * y ^ 2) -
          Real.cos σ.θ₁ * ((1 + t ^ 2) * y) := by ring
    rw [e]
    have hx0 : 0 < x := by linarith
    have htx : τ₀ / 2 ≤ t - x := by linarith
    have h1x : 1 ≤ 1 + t * x := by nlinarith only [ht, hx0]
    have hprod : τ₀ / 2 ≤ (t - x) * (1 + t * x) := by
      nlinarith only [htx, h1x, t0]
    have b1 : Real.sin σ.θ₁ * (τ₀ / 2) ≤ Real.sin σ.θ₁ * ((t - x) * (1 + t * x)) :=
      mul_le_mul_of_nonneg_left hprod sn1.le
    have hy2 : t * y ^ 2 ≤ s := by nlinarith only [ht1, ht, y0, y1, hs1]
    have b2 : Real.sin σ.θ₁ * (t * y ^ 2) ≤ s := by
      have : 0 ≤ t * y ^ 2 := by positivity
      nlinarith only [sl1, this, hy2, sn1]
    have ht2 : t ^ 2 ≤ 1 := by nlinarith only [ht1, ht]
    have hy3 : (1 + t ^ 2) * y ≤ 2 * s := by
      have := mul_le_mul_of_nonneg_right (by linarith : 1 + t ^ 2 ≤ 2) y0.le
      linarith
    have b3 : Real.cos σ.θ₁ * ((1 + t ^ 2) * y) ≤ 2 * s := by
      have : 0 ≤ (1 + t ^ 2) * y := by positivity
      nlinarith only [cl1, cs1, this, hy3]
    have k1' : 3 * s < Real.sin σ.θ₁ * (τ₀ / 2) := by nlinarith only [k1, sn1, t0]
    linarith

end Spherical

end CompactShape

end GC.Seifert
