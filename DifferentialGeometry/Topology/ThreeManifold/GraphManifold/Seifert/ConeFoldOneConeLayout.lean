import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldConeCornerWalls
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldLayout

/-!
# The layout of the cone fold in the coordinates of the corner maps

Lane A4b2 (errata after review 15 to the design
`docs/geometrization/handoffs/20261004-design-a4-cone-fold.md`, and `SF/ConeFoldLayout.lean`).
The layout regions are `R₂ = {η₀ < h}` (cusp `0`), `R₁ = {η₁ < h}` (cone vertex `v₁`) with
`h = foldH = √K/λ`, `λ = 21/20`, and the lens `|sinh n| < 1/10` along the circle wall, where
`sinh n = 2 wallSide₂/Im z` is the sinh of the signed distance to the circle wall. This file
translates the layout into the coordinates used by the corner maps:
* near the cusp `0`: `sinh n = 4 η₀ (horoX + 1/2)` (`sinhN_eq_horoX`), so the switch window
  `1/10 ≤ sinh n ≤ 7/50` of `∂R₂` is `foldA₀ ≤ horoX ≤ foldB₀` with
  `foldA₀ = -1/2 + 1/(40h)`, `foldB₀ = -1/2 + 7/(200h)` (`horoX_lt_foldA₀`, `foldB₀_lt_horoX`);
* near `v₁`: `sinh n = sinhRad η₁ · sin (θ₁ - φ)` with `φ = discAngle ω₁` and
  `sinhRad η = (η² - y₁²)/(2 η y₁)` the sinh of the distance to `v₁` (`sinhN_eq_sinhRad`), so on
  `∂R₁` the switch window is `foldPhiA ≤ φ ≤ foldPhiB` with
  `θ₁ - foldPhiA = arcsin (7/(50 sD))`, `θ₁ - foldPhiB = arcsin (1/(10 sD))`, `sD = sinhRad h`
  (`foldPhiB_lt_of_sinhN_lt`, `lt_foldPhiA_of_sinhN_gt`); the radial blend of the cone corner
  runs over `foldA₁ ≤ η₁ ≤ foldB₁` with `8 sinhRad foldA₁ > sD` (erratum 2), so on the band
  `|sinh n| < 1/80` outside the apex zone the cone corner is the pure wall-2 bridge
  (`foldPhiB_lt_of_band`).
The closed regions `R₁`, `R₂` are disjoint (`foldH_lt_etaOne_of_cuspZeroHeight_le`), the triangle
minus `v₁` lies in the domains of both cone bridges with `0 ≤ φ ≤ θ₁`
(`mem_domOne_of_mem_triangle`, `mem_domTwo_of_mem_triangle`, `discAngle_mem_of_mem_triangle`),
and the exact core certificates of `SF/ConeFoldLayout.lean` are restated for points of the
triangle (`inner_core_of_lens`, `inner_core_of_windowOne`, `inner_core_of_windowTwo`,
`wallSide_pos_of_outer_core`).
-/

set_option autoImplicit false

noncomputable section

open Complex
open scoped ComplexConjugate

namespace GC.Seifert

namespace ConeShape

variable (σ : ConeShape)

/-! ### Parameters -/

def foldH : ℝ := 20 / 21 * Real.sqrt σ.constK

def foldA₀ : ℝ := -1 / 2 + 1 / 10 / (4 * σ.foldH)

def foldB₀ : ℝ := -1 / 2 + 7 / 50 / (4 * σ.foldH)

def foldA₁ : ℝ := (σ.vertexOne.im + σ.foldH) / 2

def foldB₁ : ℝ := (σ.vertexOne.im + 3 * σ.foldH) / 4

def sinhRad (η : ℝ) : ℝ := (η ^ 2 - σ.vertexOne.im ^ 2) / (2 * η * σ.vertexOne.im)

def foldSD : ℝ := σ.sinhRad σ.foldH

def foldPhiA : ℝ := σ.θ₁ - Real.arcsin (7 / 50 / σ.foldSD)

def foldPhiB : ℝ := σ.θ₁ - Real.arcsin (1 / 10 / σ.foldSD)

def foldY₁ : ℝ := 41 / 42 * Real.sqrt σ.constK

def foldY₂ : ℝ := 83 / 84 * Real.sqrt σ.constK

def sinhN (z : ℂ) : ℝ := 2 * σ.wallSide 2 z / z.im

section Params

variable (h₁ : Real.cos σ.θ₁ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₁)
  (h₂ : Real.cos σ.θ₂ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₂)

include h₁ h₂ in
theorem tOne_le : σ.tOne ≤ 2 / 3 := by
  have hc1 := σ.cos_θ₁_nonneg
  have hsum := σ.cos_add_cos_pos
  have h2pos := σ.one_add_cos_θ₂_pos
  rw [tOne, div_le_iff₀ h2pos]
  rcases h₂ with h | h
  · rcases h₁ with h1 | h1
    · rw [h1, h] at hsum
      linarith
    · rw [h]
      linarith
  · linarith

theorem quarter_le_sqrt_constK : 1 / 4 ≤ Real.sqrt σ.constK := by
  rw [Real.le_sqrt (by norm_num) σ.constK_pos.le]
  have := σ.cos_θ₁_nonneg
  have := σ.cos_θ₂_nonneg
  unfold constK
  nlinarith

theorem foldH_pos : 0 < σ.foldH := by
  have := σ.sqrt_constK_pos
  unfold foldH
  positivity

theorem foldH_eq : σ.foldH = Real.sqrt σ.constK / (21 / 20) := by
  unfold foldH
  ring

theorem foldH_lt_sqrt : σ.foldH < Real.sqrt σ.constK := by
  have := σ.sqrt_constK_pos
  unfold foldH
  linarith

theorem sqrt_constK_le_half : Real.sqrt σ.constK ≤ 1 / 2 := by
  rw [Real.sqrt_le_left (by norm_num)]
  have h1 := Real.cos_le_one σ.θ₁
  have h2 := Real.cos_le_one σ.θ₂
  have h3 := σ.cos_θ₁_nonneg
  have h4 := σ.cos_θ₂_nonneg
  unfold constK
  nlinarith [mul_le_mul (by linarith : 1 + Real.cos σ.θ₁ ≤ 2) (by linarith : 1 + Real.cos σ.θ₂ ≤ 2)
    (by linarith) (by norm_num)]

theorem foldH_lt_half : σ.foldH < 1 / 2 := by
  have := σ.sqrt_constK_le_half
  unfold foldH
  linarith

theorem five_twentyoneths_le_foldH : 5 / 21 ≤ σ.foldH := by
  have := σ.quarter_le_sqrt_constK
  unfold foldH
  linarith

theorem foldH_sq : σ.foldH ^ 2 = 400 / 441 * σ.constK := by
  unfold foldH
  rw [mul_pow, Real.sq_sqrt σ.constK_pos.le]
  ring

include h₁ h₂ in
theorem vertexOne_im_lt_foldH : σ.vertexOne.im < σ.foldH := by
  have hw := (ConeLayout.window_before_wallOne σ h₁ h₂).1
  have hv := σ.vertexOne_im_pos
  have hH := σ.foldH_pos
  have hK := σ.constK_pos
  have hsq : σ.vertexOne.im ^ 2 < σ.foldH ^ 2 := by
    rw [σ.vertexOne_im_sq, σ.foldH_sq]
    nlinarith
  nlinarith

theorem sinhRad_eq {η : ℝ} (hη : η ≠ 0) :
    σ.sinhRad η = η / (2 * σ.vertexOne.im) - σ.vertexOne.im / (2 * η) := by
  have hv := σ.vertexOne_im_pos.ne'
  unfold sinhRad
  field_simp

theorem sinhRad_le_sinhRad {η η' : ℝ} (hη : 0 < η) (h : η ≤ η') : σ.sinhRad η ≤ σ.sinhRad η' := by
  have hv := σ.vertexOne_im_pos
  rw [σ.sinhRad_eq hη.ne', σ.sinhRad_eq (by linarith : η' ≠ 0)]
  have h1 : η / (2 * σ.vertexOne.im) ≤ η' / (2 * σ.vertexOne.im) :=
    div_le_div_of_nonneg_right h (by positivity)
  have h2 : σ.vertexOne.im / (2 * η') ≤ σ.vertexOne.im / (2 * η) :=
    div_le_div_of_nonneg_left hv.le (by positivity) (by linarith)
  linarith

theorem sinhRad_pos {η : ℝ} (hη : σ.vertexOne.im < η) : 0 < σ.sinhRad η := by
  have hv := σ.vertexOne_im_pos
  unfold sinhRad
  apply div_pos <;> nlinarith

include h₁ h₂ in
theorem foldSD_pos : 0 < σ.foldSD := σ.sinhRad_pos (σ.vertexOne_im_lt_foldH h₁ h₂)

include h₁ h₂ in
theorem window_lt_foldSD_mul : 7 / 50 < σ.foldSD * Real.sin σ.θ₁ := by
  have hw := (ConeLayout.window_before_wallOne σ h₁ h₂).2
  have hv := σ.vertexOne_im_pos
  have hH := σ.foldH_pos
  have hK := σ.constK_pos
  have hvH := σ.vertexOne_im_lt_foldH h₁ h₂
  have hs := σ.sin_θ₁_pos
  have hy : σ.vertexOne.im = Real.sin σ.θ₁ / 4 := σ.vertexOne_im
  have hv2 := σ.vertexOne_im_sq
  have hH2 := σ.foldH_sq
  have key : (2 * σ.foldH * σ.vertexOne.im * (7 / 50)) ^ 2 <
      ((σ.foldH ^ 2 - σ.vertexOne.im ^ 2) * Real.sin σ.θ₁) ^ 2 := by
    have e1 : (2 * σ.foldH * σ.vertexOne.im * (7 / 50)) ^ 2 =
        4 * (7 / 50) ^ 2 * (400 / 441 * σ.constK) * (σ.tOne * σ.constK) := by
      rw [← hH2, ← hv2]
      ring
    have e2 : ((σ.foldH ^ 2 - σ.vertexOne.im ^ 2) * Real.sin σ.θ₁) ^ 2 =
        (400 / 441) ^ 2 * σ.constK ^ 2 *
          (Real.sin σ.θ₁ ^ 2 * (1 - (21 / 20) ^ 2 * σ.tOne) ^ 2) := by
      rw [hH2, hv2]
      ring
    rw [e1, e2]
    have hK2 : 0 < σ.constK ^ 2 := by positivity
    nlinarith
  have hpos : 0 < (σ.foldH ^ 2 - σ.vertexOne.im ^ 2) * Real.sin σ.θ₁ := by
    apply mul_pos _ hs
    nlinarith
  have key' : 2 * σ.foldH * σ.vertexOne.im * (7 / 50) <
      (σ.foldH ^ 2 - σ.vertexOne.im ^ 2) * Real.sin σ.θ₁ :=
    lt_of_pow_lt_pow_left₀ 2 hpos.le key
  unfold foldSD sinhRad
  rw [div_mul_eq_mul_div, lt_div_iff₀ (by positivity)]
  linarith

include h₁ h₂ in
theorem window_lt_foldSD : 7 / 50 < σ.foldSD := by
  have h := σ.window_lt_foldSD_mul h₁ h₂
  have hs := Real.sin_le_one σ.θ₁
  have hD := σ.foldSD_pos h₁ h₂
  nlinarith

include h₁ h₂ in
theorem arg_mem_one {c : ℝ} (hc0 : 0 ≤ c) (hc : c ≤ 7 / 50) : c / σ.foldSD ∈ Set.Icc (-1) 1 := by
  have hD := σ.foldSD_pos h₁ h₂
  have hlt := σ.window_lt_foldSD h₁ h₂
  constructor
  · have : 0 ≤ c / σ.foldSD := div_nonneg hc0 hD.le
    linarith
  · rw [div_le_one hD]
    linarith

include h₁ h₂ in
theorem sin_sub_foldPhiB : Real.sin (σ.θ₁ - σ.foldPhiB) = 1 / 10 / σ.foldSD := by
  have hm := σ.arg_mem_one h₁ h₂ (c := 1 / 10) (by norm_num) (by norm_num)
  rw [foldPhiB, sub_sub_cancel, Real.sin_arcsin hm.1 hm.2]

include h₁ h₂ in
theorem sin_sub_foldPhiA : Real.sin (σ.θ₁ - σ.foldPhiA) = 7 / 50 / σ.foldSD := by
  have hm := σ.arg_mem_one h₁ h₂ (c := 7 / 50) (by norm_num) (by norm_num)
  rw [foldPhiA, sub_sub_cancel, Real.sin_arcsin hm.1 hm.2]

include h₁ h₂ in
theorem foldPhiB_lt : σ.foldPhiB < σ.θ₁ := by
  have hD := σ.foldSD_pos h₁ h₂
  have : 0 < Real.arcsin (1 / 10 / σ.foldSD) := Real.arcsin_pos.2 (by positivity)
  unfold foldPhiB
  linarith

include h₁ h₂ in
theorem foldPhiA_lt_foldPhiB : σ.foldPhiA < σ.foldPhiB := by
  have hD := σ.foldSD_pos h₁ h₂
  have hm := σ.arg_mem_one h₁ h₂ (c := 7 / 50) (by norm_num) (by norm_num)
  have : Real.arcsin (1 / 10 / σ.foldSD) < Real.arcsin (7 / 50 / σ.foldSD) :=
    Real.arcsin_lt_arcsin (by have : 0 ≤ 1 / 10 / σ.foldSD := by positivity
                              linarith)
      (div_lt_div_of_pos_right (by norm_num) hD) hm.2
  unfold foldPhiA foldPhiB
  linarith

include h₁ h₂ in
theorem foldPhiA_pos : 0 < σ.foldPhiA := by
  have hD := σ.foldSD_pos h₁ h₂
  have hm := σ.arg_mem_one h₁ h₂ (c := 7 / 50) (by norm_num) (by norm_num)
  have hw := σ.window_lt_foldSD_mul h₁ h₂
  have hθ := σ.θ₁_pos
  have hθ' := σ.θ₁_le
  have : Real.arcsin (7 / 50 / σ.foldSD) < σ.θ₁ := by
    rw [Real.arcsin_lt_iff_lt_sin hm ⟨by linarith [Real.pi_pos], hθ'⟩, div_lt_iff₀ hD]
    linarith
  unfold foldPhiA
  linarith

include h₁ h₂ in
theorem foldPhiB_pos : 0 < σ.foldPhiB :=
  lt_trans (σ.foldPhiA_pos h₁ h₂) (σ.foldPhiA_lt_foldPhiB h₁ h₂)

include h₁ h₂ in
theorem vertexOne_im_lt_foldA₁ : σ.vertexOne.im < σ.foldA₁ := by
  have := σ.vertexOne_im_lt_foldH h₁ h₂
  unfold foldA₁
  linarith

include h₁ h₂ in
theorem foldA₁_lt_foldB₁ : σ.foldA₁ < σ.foldB₁ := by
  have := σ.vertexOne_im_lt_foldH h₁ h₂
  unfold foldA₁ foldB₁
  linarith

include h₁ h₂ in
theorem foldB₁_lt_foldH : σ.foldB₁ < σ.foldH := by
  have := σ.vertexOne_im_lt_foldH h₁ h₂
  unfold foldB₁
  linarith

include h₁ h₂ in
theorem foldSD_lt_eight_sinhRad : σ.foldSD < 8 * σ.sinhRad σ.foldA₁ := by
  have hv := σ.vertexOne_im_pos
  have hvH := σ.vertexOne_im_lt_foldH h₁ h₂
  have hH := σ.foldH_pos
  unfold foldSD sinhRad foldA₁
  set u := σ.foldH
  set v := σ.vertexOne.im
  rw [div_lt_iff₀ (by positivity)]
  have e : 8 * ((((v + u) / 2) ^ 2 - v ^ 2) / (2 * ((v + u) / 2) * v)) * (2 * u * v) =
      8 * u * (u - v) * (u + 3 * v) / (2 * (v + u)) := by
    field_simp
    ring
  rw [e, lt_div_iff₀ (by positivity)]
  nlinarith [mul_pos (sub_pos.2 hvH) (mul_pos hv hH), mul_pos (sub_pos.2 hvH) (mul_pos hH hH),
    mul_pos (sub_pos.2 hvH) (mul_pos hv hv)]

theorem foldA₀_lt_foldB₀ : σ.foldA₀ < σ.foldB₀ := by
  have := σ.foldH_pos
  unfold foldA₀ foldB₀
  have : 1 / 10 / (4 * σ.foldH) < 7 / 50 / (4 * σ.foldH) :=
    div_lt_div_of_pos_right (by norm_num) (by positivity)
  linarith

theorem neg_half_lt_foldA₀ : -1 / 2 < σ.foldA₀ := by
  have := σ.foldH_pos
  unfold foldA₀
  have : 0 < 1 / 10 / (4 * σ.foldH) := by positivity
  linarith

theorem foldB₀_neg : σ.foldB₀ < 0 := by
  have h5 := σ.five_twentyoneths_le_foldH
  have : 7 / 50 / (4 * σ.foldH) ≤ 7 / 50 / (4 * (5 / 21)) :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  unfold foldB₀
  norm_num at this ⊢
  linarith

theorem foldH_lt_foldY₁ : σ.foldH < σ.foldY₁ := by
  have := σ.sqrt_constK_pos
  unfold foldH foldY₁
  linarith

theorem foldY₁_lt_foldY₂ : σ.foldY₁ < σ.foldY₂ := by
  have := σ.sqrt_constK_pos
  unfold foldY₁ foldY₂
  linarith

theorem foldY₂_lt_sqrt : σ.foldY₂ < Real.sqrt σ.constK := by
  have := σ.sqrt_constK_pos
  unfold foldY₂
  linarith

theorem foldY₁_pos : 0 < σ.foldY₁ := by
  have := σ.sqrt_constK_pos
  unfold foldY₁
  positivity


/-! ### Translation of `sinh n` -/

theorem sinhN_eq_horoX (hθ : σ.θ₂ = 0) {z : ℂ} (hz : 0 < z.im) :
    σ.sinhN z = 4 * cuspZeroHeight z * (horoX z + 1 / 2) := by
  have hz0 : z ≠ 0 := fun h => by rw [h] at hz; simp at hz
  have hn : normSq z ≠ 0 := normSq_eq_zero.not.2 hz0
  have hc := σ.cusp_centre hθ
  have hre : horoX z = -z.re / (4 * normSq z) := by
    simp only [horoX, div_re, normSq_mul]
    simp [normSq_apply]
    field_simp
  rw [sinhN, wallSide, hre, cuspZeroHeight, hc]
  rw [normSq_apply] at hn ⊢
  field_simp
  ring

theorem sinhN_eq_wallTwo {z : ℂ} (hz : 0 < z.im) :
    σ.sinhN z = 2 * σ.wallTwo z / (1 - ‖σ.discOne z‖ ^ 2) := by
  have hv := σ.vertexOne_im_pos
  have hN := normSq_sub_conj_pos hv hz
  have h1 := σ.im_rot_coneDisc_vertexOne_mul z
  have h2 := one_sub_normSq_coneDisc hv hz
  have hs := σ.sin_θ₁_pos
  have hy : σ.vertexOne.im = Real.sin σ.θ₁ / 4 := σ.vertexOne_im
  rw [Complex.sq_norm, discOne, h2, sinhN, wallTwo, discOne, hy]
  field_simp
  linear_combination h1

theorem discOne_polar {z : ℂ} (hz : z ∈ σ.domOne) :
    σ.discOne z = (‖σ.discOne z‖ : ℂ) * exp ((discAngle (σ.discOne z) : ℂ) * I) :=
  halfArg_polar_self (σ.discOne_ne_zero hz) hz.2

theorem rot_discOne_polar {z : ℂ} (hz : z ∈ σ.domOne) :
    exp (-(σ.θ₁ * I)) * σ.discOne z =
      (‖σ.discOne z‖ : ℂ) * exp (((discAngle (σ.discOne z) - σ.θ₁ : ℝ) : ℂ) * I) := by
  conv_lhs => rw [σ.discOne_polar hz]
  rw [mul_left_comm, ← Complex.exp_add]
  congr 2
  push_cast
  ring

theorem wallTwo_eq_polar {z : ℂ} (hz : z ∈ σ.domOne) :
    σ.wallTwo z = ‖σ.discOne z‖ * Real.sin (σ.θ₁ - discAngle (σ.discOne z)) := by
  rw [wallTwo, σ.rot_discOne_polar hz, im_ofReal_mul, Complex.exp_ofReal_mul_I_im,
    show σ.θ₁ - discAngle (σ.discOne z) = -(discAngle (σ.discOne z) - σ.θ₁) by ring, Real.sin_neg]
  ring

theorem rotRe_eq_polar {z : ℂ} (hz : z ∈ σ.domOne) :
    (exp (-(σ.θ₁ * I)) * σ.discOne z).re =
      ‖σ.discOne z‖ * Real.cos (σ.θ₁ - discAngle (σ.discOne z)) := by
  rw [σ.rot_discOne_polar hz, re_ofReal_mul, Complex.exp_ofReal_mul_I_re,
    show σ.θ₁ - discAngle (σ.discOne z) = -(discAngle (σ.discOne z) - σ.θ₁) by ring, Real.cos_neg]

theorem wallOne_eq_polar {z : ℂ} (hz : z ∈ σ.domOne) :
    σ.wallOne z = ‖σ.discOne z‖ * Real.sin (discAngle (σ.discOne z)) := by
  conv_lhs => rw [wallOne, σ.discOne_polar hz]
  rw [im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

theorem norm_discOne_eq {z : ℂ} (hz : 0 < z.im) :
    ‖σ.discOne z‖ = (σ.etaOne z - σ.vertexOne.im) / (σ.etaOne z + σ.vertexOne.im) :=
  (radial_identity σ.vertexOne_im_pos (norm_coneDisc_lt_one σ.vertexOne_im_pos hz)
    (norm_nonneg _)).symm

theorem sinhRad_etaOne {z : ℂ} (hz : 0 < z.im) :
    σ.sinhRad (σ.etaOne z) = 2 * ‖σ.discOne z‖ / (1 - ‖σ.discOne z‖ ^ 2) := by
  have hv := σ.vertexOne_im_pos
  have hr1 : ‖σ.discOne z‖ < 1 := norm_coneDisc_lt_one hv hz
  have hr0 := norm_nonneg (σ.discOne z)
  have h1 : 1 - ‖σ.discOne z‖ ≠ 0 := by linarith
  have h2 : 1 + ‖σ.discOne z‖ ≠ 0 := by linarith
  have h3 : 1 - ‖σ.discOne z‖ ^ 2 ≠ 0 := by nlinarith
  unfold sinhRad etaOne coneHeight
  rw [← discOne]
  field_simp
  ring

theorem sinhN_eq_sinhRad {z : ℂ} (hz : z ∈ σ.domOne) :
    σ.sinhN z = σ.sinhRad (σ.etaOne z) * Real.sin (σ.θ₁ - discAngle (σ.discOne z)) := by
  have hr1 : ‖σ.discOne z‖ < 1 := norm_coneDisc_lt_one σ.vertexOne_im_pos hz.1
  have hr0 := norm_nonneg (σ.discOne z)
  have h3 : 1 - ‖σ.discOne z‖ ^ 2 ≠ 0 := by nlinarith
  rw [σ.sinhN_eq_wallTwo hz.1, σ.wallTwo_eq_polar hz, σ.sinhRad_etaOne hz.1]
  field_simp

/-! ### The triangle minus `v₁` in the bridge domains -/

theorem coneDisc_re_mul (v z : ℂ) :
    (coneDisc v z).re * normSq (z - conj v) = (z.re - v.re) ^ 2 + z.im ^ 2 - v.im ^ 2 := by
  have h := congrArg Complex.re (coneDisc_mul_normSq v z)
  simp only [mul_re, ofReal_re, ofReal_im, mul_zero, sub_zero, sub_re, sub_im, conj_re,
    conj_im] at h
  rw [h]
  ring

theorem rotRe_mul (z : ℂ) :
    (exp (-(σ.θ₁ * I)) * σ.discOne z).re * normSq (z - conj σ.vertexOne) =
      Real.cos σ.θ₁ * ((z.re - σ.centre) ^ 2 + z.im ^ 2 + 1 / 16) - (z.re - σ.centre) / 2 := by
  have h0 := congrArg Complex.re (coneDisc_mul_normSq σ.vertexOne z)
  have h1 := congrArg Complex.im (coneDisc_mul_normSq σ.vertexOne z)
  simp only [mul_re, mul_im, ofReal_re, ofReal_im, mul_zero, sub_zero, zero_add, sub_re, sub_im,
    conj_re, conj_im] at h0 h1
  have e : exp (-(σ.θ₁ * I)) = ⟨Real.cos σ.θ₁, -Real.sin σ.θ₁⟩ := by
    rw [show -((σ.θ₁ : ℂ) * I) = ((-σ.θ₁ : ℝ) : ℂ) * I by push_cast; ring, exp_mul_I_eq,
      Real.cos_neg, Real.sin_neg]
  have hL : (exp (-(σ.θ₁ * I)) * σ.discOne z).re =
      Real.cos σ.θ₁ * (σ.discOne z).re + Real.sin σ.θ₁ * (σ.discOne z).im := by
    rw [e, mul_re]
    ring
  rw [hL, add_mul, mul_assoc, mul_assoc, discOne, h0, h1, vertexOne_re, vertexOne_im, width]
  unfold centre
  have hs := Real.sin_sq_add_cos_sq σ.θ₁
  linear_combination (Real.cos σ.θ₁ / 16 - z.re / 2 + Real.cos σ.θ₂ / 8) * hs

theorem rotRe_nonneg_of_mem_triangle {z : ℂ} (hz : z ∈ σ.triangle) :
    0 ≤ (exp (-(σ.θ₁ * I)) * σ.discOne z).re := by
  have hN := normSq_sub_conj_pos σ.vertexOne_im_pos hz.1
  have h := σ.rotRe_mul z
  have hw1 := hz.2 1
  have hw2 := hz.2 2
  have hc := σ.cos_θ₁_nonneg
  simp only [wallSide] at hw1 hw2
  have hW : σ.width - σ.centre = Real.cos σ.θ₁ / 4 := by unfold width centre; ring
  have key : 0 ≤ Real.cos σ.θ₁ * ((z.re - σ.centre) ^ 2 + z.im ^ 2 + 1 / 16) -
      (z.re - σ.centre) / 2 := by nlinarith [mul_nonneg hc hw2]
  rw [← h] at key
  exact nonneg_of_mul_nonneg_left key hN

theorem wallOne_nonneg_of_mem_triangle {z : ℂ} (hz : z ∈ σ.triangle) : 0 ≤ σ.wallOne z := by
  have hN := normSq_sub_conj_pos σ.vertexOne_im_pos hz.1
  have h := σ.im_coneDisc_vertexOne_mul z
  have hw := hz.2 1
  have : 0 ≤ (coneDisc σ.vertexOne z).im * normSq (z - conj σ.vertexOne) := by
    rw [h]; have := σ.vertexOne_im_pos; positivity
  exact nonneg_of_mul_nonneg_left this hN

theorem wallTwo_nonneg_of_mem_triangle {z : ℂ} (hz : z ∈ σ.triangle) : 0 ≤ σ.wallTwo z := by
  have hN := normSq_sub_conj_pos σ.vertexOne_im_pos hz.1
  have h := σ.im_rot_coneDisc_vertexOne_mul z
  have hw := hz.2 2
  have hs := σ.sin_θ₁_pos
  have : 0 ≤ σ.wallTwo z * normSq (z - conj σ.vertexOne) := by
    rw [wallTwo, discOne, neg_mul, h]; simp only [neg_neg]; positivity
  exact nonneg_of_mul_nonneg_left this hN

theorem discOne_ne_zero_of_ne {z : ℂ} (hz : 0 < z.im) (hzv : z ≠ σ.vertexOne) :
    σ.discOne z ≠ 0 :=
  coneDisc_ne_zero σ.vertexOne_im_pos hz hzv

theorem mem_domOne_of_mem_triangle {z : ℂ} (hz : z ∈ σ.triangle) (hzv : z ≠ σ.vertexOne) :
    z ∈ σ.domOne := by
  refine ⟨hz.1, ?_⟩
  have hw := σ.wallOne_nonneg_of_mem_triangle hz
  have hne := σ.discOne_ne_zero_of_ne hz.1 hzv
  have hn := Complex.abs_re_le_norm (σ.discOne z)
  rcases hw.lt_or_eq with hlt | heq
  · have hlt' : |(σ.discOne z).re| < ‖σ.discOne z‖ := by
      have h2 : (σ.discOne z).re ^ 2 + (σ.discOne z).im ^ 2 = ‖σ.discOne z‖ ^ 2 := by
        rw [Complex.sq_norm, normSq_apply]; ring
      have : (σ.discOne z).re ^ 2 < ‖σ.discOne z‖ ^ 2 := by
        change 0 < (σ.discOne z).im at hlt
        nlinarith
      exact abs_lt_of_sq_lt_sq' this (norm_nonneg _) |>.2 |> fun h => by
        rw [abs_lt]; exact ⟨(abs_lt_of_sq_lt_sq' this (norm_nonneg _)).1, h⟩
    linarith [neg_abs_le (σ.discOne z).re]
  · have him : (σ.discOne z).im = 0 := heq.symm
    have hN := normSq_sub_conj_pos σ.vertexOne_im_pos hz.1
    have hx : z.re = σ.width := by
      have h := σ.im_coneDisc_vertexOne_mul z
      rw [discOne] at him
      rw [him, zero_mul] at h
      have hv := σ.vertexOne_im_pos
      simp only [wallSide] at h
      have : σ.width - z.re = 0 := by
        rcases mul_eq_zero.1 h.symm with h' | h'
        · linarith
        · exact h'
      linarith
    have hy : σ.vertexOne.im < z.im := by
      have hw2 := hz.2 2
      simp only [wallSide] at hw2
      rw [hx] at hw2
      have hW : σ.width - σ.centre = Real.cos σ.θ₁ / 4 := by unfold width centre; ring
      rw [hW] at hw2
      have hs := Real.sin_sq_add_cos_sq σ.θ₁
      have hle : σ.vertexOne.im ≤ z.im := by
        rw [vertexOne_im]
        have hsq : (Real.sin σ.θ₁ / 4) ^ 2 ≤ z.im ^ 2 := by nlinarith
        exact (pow_le_pow_iff_left₀ (by linarith [σ.sin_θ₁_pos]) hz.1.le (by norm_num)).1 hsq
      rcases hle.lt_or_eq with h | h
      · exact h
      · exact absurd (Complex.ext (by rw [hx, vertexOne_re]) h.symm) hzv
    have hre : 0 < (σ.discOne z).re := by
      have h := coneDisc_re_mul σ.vertexOne z
      rw [hx, vertexOne_re, sub_self] at h
      have : 0 < (coneDisc σ.vertexOne z).re * normSq (z - conj σ.vertexOne) := by
        rw [h]; nlinarith [σ.vertexOne_im_pos]
      exact pos_of_mul_pos_left this hN.le
    linarith [norm_nonneg (σ.discOne z)]

theorem mem_domTwo_of_mem_triangle {z : ℂ} (hz : z ∈ σ.triangle) (hzv : z ≠ σ.vertexOne) :
    z ∈ σ.domTwo := by
  refine ⟨hz.1, ?_⟩
  have h := σ.rotRe_nonneg_of_mem_triangle hz
  have hne := σ.discOne_ne_zero_of_ne hz.1 hzv
  have := norm_pos_iff.2 hne
  linarith

theorem discAngle_mem_of_mem_triangle {z : ℂ} (hz : z ∈ σ.triangle) (hzv : z ≠ σ.vertexOne) :
    0 ≤ discAngle (σ.discOne z) ∧ discAngle (σ.discOne z) ≤ σ.θ₁ := by
  have hd := σ.mem_domOne_of_mem_triangle hz hzv
  have hr : 0 < ‖σ.discOne z‖ := norm_pos_iff.2 (σ.discOne_ne_zero hd)
  have hm : discAngle (σ.discOne z) ∈ Set.Ioo (-Real.pi) Real.pi := halfArg_mem _ _ _
  have h1 := σ.wallOne_nonneg_of_mem_triangle hz
  have h2 := σ.wallTwo_nonneg_of_mem_triangle hz
  rw [σ.wallOne_eq_polar hd] at h1
  rw [σ.wallTwo_eq_polar hd] at h2
  have hs1 : 0 ≤ Real.sin (discAngle (σ.discOne z)) := nonneg_of_mul_nonneg_right
    (by linarith [mul_comm ‖σ.discOne z‖ (Real.sin (discAngle (σ.discOne z)))]) hr
  have hs2 : 0 ≤ Real.sin (σ.θ₁ - discAngle (σ.discOne z)) := nonneg_of_mul_nonneg_right
    (by linarith [mul_comm ‖σ.discOne z‖ (Real.sin (σ.θ₁ - discAngle (σ.discOne z)))]) hr
  have hθ := σ.θ₁_pos
  have hθ' := σ.θ₁_le
  have hφ0 : 0 ≤ discAngle (σ.discOne z) := by
    by_contra hneg
    push Not at hneg
    have := Real.sin_neg_of_neg_of_neg_pi_lt hneg hm.1
    linarith
  refine ⟨hφ0, ?_⟩
  by_contra hgt
  push Not at hgt
  have := Real.sin_neg_of_neg_of_neg_pi_lt (by linarith : σ.θ₁ - discAngle (σ.discOne z) < 0)
    (by linarith [hm.2])
  linarith

/-! ### Regions -/

theorem im_le_cuspZeroHeight {z : ℂ} (hz : 0 < z.im) : z.im ≤ cuspZeroHeight z := by
  have := cuspZeroHeight_sub_im hz
  have : 0 ≤ z.re ^ 2 * (1 / z.im) := by positivity
  linarith

theorem im_le_etaOne {z : ℂ} (hz : z ∈ σ.domOne) : z.im ≤ σ.etaOne z := by
  have h := σ.etaOne_sub_im hz
  have := σ.cofOne_pos hz
  nlinarith [sq_nonneg (σ.wallOne z)]

theorem foldH_lt_etaOne_of_cuspZeroHeight_le (hθ : σ.θ₂ = 0) {z : ℂ} (hz : 0 < z.im)
    (h : cuspZeroHeight z ≤ σ.foldH) : σ.foldH < σ.etaOne z := by
  have hK := σ.constK_le_coneHeight_mul_cuspZero hθ hz
  have h0 := cuspZeroHeight_pos hz
  have hH := σ.foldH_pos
  have hs := σ.sqrt_constK_pos
  have hKs : σ.constK = Real.sqrt σ.constK ^ 2 := (Real.sq_sqrt σ.constK_pos.le).symm
  change σ.constK ≤ σ.etaOne z * cuspZeroHeight z at hK
  unfold foldH at h ⊢
  by_contra hle
  push Not at hle
  have : σ.etaOne z * cuspZeroHeight z ≤ 20 / 21 * Real.sqrt σ.constK *
      (20 / 21 * Real.sqrt σ.constK) :=
    mul_le_mul hle h h0.le (by positivity)
  nlinarith

theorem foldH_lt_cuspZeroHeight_of_etaOne_le (hθ : σ.θ₂ = 0) {z : ℂ} (hz : 0 < z.im)
    (h : σ.etaOne z ≤ σ.foldH) : σ.foldH < cuspZeroHeight z := by
  by_contra hle
  push Not at hle
  have := σ.foldH_lt_etaOne_of_cuspZeroHeight_le hθ hz hle
  linarith

/-! ### Switch windows -/

include h₁ h₂ in
theorem sin_lt_of_window {z : ℂ} (hz : z ∈ σ.domOne) (he : σ.etaOne z = σ.foldH) {c : ℝ}
    (hc : σ.sinhN z < c) :
    Real.sin (σ.θ₁ - discAngle (σ.discOne z)) < c / σ.foldSD := by
  have hD := σ.foldSD_pos h₁ h₂
  rw [σ.sinhN_eq_sinhRad hz, he, ← foldSD] at hc
  rw [lt_div_iff₀ hD]
  linarith [mul_comm σ.foldSD (Real.sin (σ.θ₁ - discAngle (σ.discOne z)))]

include h₁ h₂ in
theorem foldPhiB_lt_of_sinhN_lt {z : ℂ} (hz : z ∈ σ.domOne) (he : σ.etaOne z = σ.foldH)
    (hφ : 0 ≤ discAngle (σ.discOne z) ∧ discAngle (σ.discOne z) ≤ σ.θ₁)
    (hs : σ.sinhN z < 1 / 10) : σ.foldPhiB < discAngle (σ.discOne z) := by
  have h := σ.sin_lt_of_window h₁ h₂ hz he hs
  rw [← σ.sin_sub_foldPhiB h₁ h₂] at h
  have hθ := σ.θ₁_le
  have hb := σ.foldPhiB_pos h₁ h₂
  have hb' := σ.foldPhiB_lt h₁ h₂
  by_contra hle
  push Not at hle
  have : Real.sin (σ.θ₁ - σ.foldPhiB) ≤ Real.sin (σ.θ₁ - discAngle (σ.discOne z)) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith) (by linarith)
  linarith

include h₁ h₂ in
theorem lt_foldPhiA_of_sinhN_gt {z : ℂ} (hz : z ∈ σ.domOne) (he : σ.etaOne z = σ.foldH)
    (hφ : 0 ≤ discAngle (σ.discOne z) ∧ discAngle (σ.discOne z) ≤ σ.θ₁)
    (hs : 7 / 50 < σ.sinhN z) : discAngle (σ.discOne z) < σ.foldPhiA := by
  have hD := σ.foldSD_pos h₁ h₂
  rw [σ.sinhN_eq_sinhRad hz, he, ← foldSD] at hs
  have h : 7 / 50 / σ.foldSD < Real.sin (σ.θ₁ - discAngle (σ.discOne z)) := by
    rw [div_lt_iff₀ hD]
    linarith [mul_comm σ.foldSD (Real.sin (σ.θ₁ - discAngle (σ.discOne z)))]
  rw [← σ.sin_sub_foldPhiA h₁ h₂] at h
  have hθ := σ.θ₁_le
  have ha := σ.foldPhiA_pos h₁ h₂
  by_contra hle
  push Not at hle
  have : Real.sin (σ.θ₁ - discAngle (σ.discOne z)) ≤ Real.sin (σ.θ₁ - σ.foldPhiA) :=
    Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith) (by linarith)
  linarith

theorem abs_sub_lt_pi_div_two_of_cos_pos {φ θ : ℝ} (hφ : φ ∈ Set.Ioo (-Real.pi) Real.pi)
    (hθ0 : 0 < θ) (hθ : θ ≤ Real.pi / 2) (hc : 0 < Real.cos (θ - φ)) :
    |θ - φ| < Real.pi / 2 := by
  rw [abs_lt]
  constructor
  · by_contra hle
    push Not at hle
    have : Real.cos (θ - φ) ≤ 0 := by
      rw [← Real.cos_neg]
      exact Real.cos_nonpos_of_pi_div_two_le_of_le (by linarith) (by linarith [hφ.2])
    linarith
  · by_contra hle
    push Not at hle
    have : Real.cos (θ - φ) ≤ 0 :=
      Real.cos_nonpos_of_pi_div_two_le_of_le hle (by linarith [hφ.1])
    linarith

include h₁ h₂ in
theorem foldPhiB_lt_of_band {z : ℂ} (hz : z ∈ σ.domOne) (ha : σ.foldA₁ ≤ σ.etaOne z)
    (hc : 0 < (exp (-(σ.θ₁ * I)) * σ.discOne z).re) (hs : |σ.sinhN z| < 1 / 80) :
    σ.foldPhiB < discAngle (σ.discOne z) ∧
      σ.foldPhiB < 2 * σ.θ₁ - discAngle (σ.discOne z) := by
  have hD := σ.foldSD_pos h₁ h₂
  have h8 := σ.foldSD_lt_eight_sinhRad h₁ h₂
  have hvA := σ.vertexOne_im_lt_foldA₁ h₁ h₂
  have hA : 0 < σ.foldA₁ := lt_trans σ.vertexOne_im_pos hvA
  have hmono := σ.sinhRad_le_sinhRad hA ha
  have hRpos : 0 < σ.sinhRad σ.foldA₁ := σ.sinhRad_pos hvA
  have hm : discAngle (σ.discOne z) ∈ Set.Ioo (-Real.pi) Real.pi := halfArg_mem _ _ _
  have hr : 0 < ‖σ.discOne z‖ := norm_pos_iff.2 (σ.discOne_ne_zero hz)
  rw [σ.rotRe_eq_polar hz] at hc
  have hcos : 0 < Real.cos (σ.θ₁ - discAngle (σ.discOne z)) := pos_of_mul_pos_right hc hr.le
  have hab := abs_sub_lt_pi_div_two_of_cos_pos hm σ.θ₁_pos σ.θ₁_le hcos
  rw [σ.sinhN_eq_sinhRad hz, abs_mul, abs_of_pos (lt_of_lt_of_le hRpos hmono)] at hs
  have hsin : |Real.sin (σ.θ₁ - discAngle (σ.discOne z))| < Real.sin (σ.θ₁ - σ.foldPhiB) := by
    rw [σ.sin_sub_foldPhiB h₁ h₂]
    have h1 : σ.sinhRad σ.foldA₁ * |Real.sin (σ.θ₁ - discAngle (σ.discOne z))| < 1 / 80 :=
      lt_of_le_of_lt (mul_le_mul_of_nonneg_right hmono (abs_nonneg _)) hs
    rw [lt_div_iff₀ hD]
    nlinarith [abs_nonneg (Real.sin (σ.θ₁ - discAngle (σ.discOne z)))]
  have hb := σ.foldPhiB_pos h₁ h₂
  have hb' := σ.foldPhiB_lt h₁ h₂
  have hθ' := σ.θ₁_le
  rw [abs_lt] at hsin hab
  constructor
  · by_contra hle
    push Not at hle
    have : Real.sin (σ.θ₁ - σ.foldPhiB) ≤ Real.sin (σ.θ₁ - discAngle (σ.discOne z)) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith)
        (by linarith)
    linarith
  · by_contra hle
    push Not at hle
    have : Real.sin (σ.θ₁ - σ.foldPhiB) ≤ Real.sin (discAngle (σ.discOne z) - σ.θ₁) :=
      Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (by linarith)
        (by linarith)
    have e : Real.sin (discAngle (σ.discOne z) - σ.θ₁) =
        -Real.sin (σ.θ₁ - discAngle (σ.discOne z)) := by
      rw [← Real.sin_neg]; ring_nf
    linarith

theorem horoX_lt_foldA₀ (hθ : σ.θ₂ = 0) {z : ℂ} (hz : 0 < z.im)
    (h0 : σ.foldH ≤ cuspZeroHeight z) (hs : σ.sinhN z < 1 / 10) : horoX z < σ.foldA₀ := by
  have hH := σ.foldH_pos
  have hc : 0 < cuspZeroHeight z := lt_of_lt_of_le hH h0
  rw [σ.sinhN_eq_horoX hθ hz] at hs
  unfold foldA₀
  have key : horoX z + 1 / 2 < 1 / 10 / (4 * σ.foldH) := by
    rcases lt_or_ge (horoX z + 1 / 2) 0 with hneg | hnn
    · have : 0 < 1 / 10 / (4 * σ.foldH) := by positivity
      linarith
    · rw [lt_div_iff₀ (by positivity)]
      nlinarith [mul_le_mul_of_nonneg_right h0 hnn]
  linarith

theorem foldB₀_lt_horoX (hθ : σ.θ₂ = 0) {z : ℂ} (hz : 0 < z.im)
    (h0 : cuspZeroHeight z ≤ σ.foldH) (hs : 7 / 50 < σ.sinhN z) : σ.foldB₀ < horoX z := by
  have hH := σ.foldH_pos
  have hc := cuspZeroHeight_pos hz
  rw [σ.sinhN_eq_horoX hθ hz] at hs
  unfold foldB₀
  have hpos : 0 < horoX z + 1 / 2 := by
    by_contra hle
    push Not at hle
    nlinarith
  have key : 7 / 50 / (4 * σ.foldH) < horoX z + 1 / 2 := by
    rw [div_lt_iff₀ (by positivity)]
    nlinarith [mul_le_mul_of_nonneg_right h0 hpos.le]
  linarith

end Params

/-! ### The core certificates for points of the triangle -/

theorem chart_neg_re {z : ℂ} (hz : 0 < z.im) :
    -(σ.fermiChart z).re = σ.sinhN z * (σ.fermiChart z).im := by
  have h := σ.neg_re_div_im_fermiChart hz
  have hY := σ.fermiChart_im_pos hz
  rw [sinhN, ← h]
  field_simp

theorem regionOne_mul {z : ℂ} (hz : 0 < z.im) :
    Real.sqrt σ.constK * σ.etaOne z * ConeLayout.regionOne σ.tOne (σ.fermiChart z) =
      (σ.fermiChart z).im * (σ.etaOne z - σ.foldH) *
        (σ.etaOne z - 21 / 20 * σ.tOne * Real.sqrt σ.constK) := by
  have hid := σ.sqrt_constK_mul_coneHeight_one hz
  have hv := σ.vertexOne_im_sq
  have hK : Real.sqrt σ.constK ^ 2 = σ.constK := Real.sq_sqrt σ.constK_pos.le
  rw [ConeLayout.regionOne, foldH]
  change Real.sqrt σ.constK * σ.etaOne z * (1 + σ.tOne * normSq (σ.fermiChart z)) =
    (σ.fermiChart z).im * (σ.etaOne z ^ 2 + σ.vertexOne.im ^ 2) at hid
  rw [hv] at hid
  linear_combination hid - (σ.fermiChart z).im * σ.tOne * hK

theorem etaOne_sub_pos (h₁ : Real.cos σ.θ₁ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₁)
    (h₂ : Real.cos σ.θ₂ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₂) {z : ℂ} (hz : 0 < z.im) :
    0 < σ.etaOne z - 21 / 20 * σ.tOne * Real.sqrt σ.constK := by
  have hw := (ConeLayout.window_before_wallOne σ h₁ h₂).1
  have hge : σ.vertexOne.im ≤ σ.etaOne z := coneHeight_ge σ.vertexOne_im_pos hz
  have hv := σ.vertexOne_im_sq
  have hv0 := σ.vertexOne_im_pos
  have ht := σ.tOne_pos
  have hs := σ.sqrt_constK_pos
  have hK : Real.sqrt σ.constK ^ 2 = σ.constK := Real.sq_sqrt σ.constK_pos.le
  have hlt : 21 / 20 * σ.tOne * Real.sqrt σ.constK < σ.vertexOne.im := by
    have hsq : (21 / 20 * σ.tOne * Real.sqrt σ.constK) ^ 2 < σ.vertexOne.im ^ 2 := by
      rw [hv]
      have e : (21 / 20 * σ.tOne * Real.sqrt σ.constK) ^ 2 =
          (21 / 20) ^ 2 * σ.tOne * (σ.tOne * σ.constK) := by rw [mul_pow, mul_pow, hK]; ring
      rw [e]
      have := σ.constK_pos
      nlinarith [mul_pos (by linarith : (0 : ℝ) < 1 - (21 / 20) ^ 2 * σ.tOne) (mul_pos ht this)]
    exact lt_of_pow_lt_pow_left₀ 2 hv0.le hsq
  linarith

theorem regionOne_nonneg_iff (h₁ : Real.cos σ.θ₁ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₁)
    (h₂ : Real.cos σ.θ₂ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₂) {z : ℂ} (hz : 0 < z.im) :
    0 ≤ ConeLayout.regionOne σ.tOne (σ.fermiChart z) ↔ σ.foldH ≤ σ.etaOne z := by
  have h := σ.regionOne_mul hz
  have hp := σ.etaOne_sub_pos h₁ h₂ hz
  have hY := σ.fermiChart_im_pos hz
  have hE := σ.etaOne_pos hz
  have hs := σ.sqrt_constK_pos
  have hsE : 0 < Real.sqrt σ.constK * σ.etaOne z := mul_pos hs hE
  constructor
  · intro hR
    by_contra hlt
    push Not at hlt
    have : (σ.fermiChart z).im * (σ.etaOne z - σ.foldH) *
        (σ.etaOne z - 21 / 20 * σ.tOne * Real.sqrt σ.constK) < 0 :=
      mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hY (by linarith)) hp
    nlinarith
  · intro hle
    have : 0 ≤ (σ.fermiChart z).im * (σ.etaOne z - σ.foldH) *
        (σ.etaOne z - 21 / 20 * σ.tOne * Real.sqrt σ.constK) :=
      mul_nonneg (mul_nonneg hY.le (by linarith)) hp.le
    rw [← h, mul_comm] at this
    exact nonneg_of_mul_nonneg_left this hsE

theorem regionOne_eq_zero_of {z : ℂ} (hz : 0 < z.im)
    (he : σ.etaOne z = σ.foldH) : ConeLayout.regionOne σ.tOne (σ.fermiChart z) = 0 := by
  have h := σ.regionOne_mul hz
  rw [he, sub_self, mul_zero, zero_mul] at h
  have hsE : 0 < Real.sqrt σ.constK * σ.foldH := mul_pos σ.sqrt_constK_pos σ.foldH_pos
  rcases mul_eq_zero.1 h with h' | h'
  · linarith
  · exact h'

theorem tTwo_eq_zero (hθ : σ.θ₂ = 0) : σ.tTwo = 0 := by simp [tTwo, hθ]

theorem regionTwo_mul (hθ : σ.θ₂ = 0) {z : ℂ} (hz : 0 < z.im) :
    Real.sqrt σ.constK * ConeLayout.regionTwo σ.tTwo (σ.fermiChart z) =
      (σ.fermiChart z).im * (cuspZeroHeight z - σ.foldH) := by
  have hid := σ.sqrt_constK_mul_normSq_fermiChart hθ hz
  rw [ConeLayout.regionTwo, σ.tTwo_eq_zero hθ, foldH]
  linear_combination hid

theorem regionTwo_nonneg_iff (hθ : σ.θ₂ = 0) {z : ℂ} (hz : 0 < z.im) :
    0 ≤ ConeLayout.regionTwo σ.tTwo (σ.fermiChart z) ↔ σ.foldH ≤ cuspZeroHeight z := by
  have h := σ.regionTwo_mul hθ hz
  have hY := σ.fermiChart_im_pos hz
  have hs := σ.sqrt_constK_pos
  constructor
  · intro hR
    have h3 : 0 ≤ (σ.fermiChart z).im * (cuspZeroHeight z - σ.foldH) := by rw [← h]; positivity
    rw [mul_comm] at h3
    have := nonneg_of_mul_nonneg_left h3 hY
    linarith
  · intro hle
    have h3 : 0 ≤ Real.sqrt σ.constK * ConeLayout.regionTwo σ.tTwo (σ.fermiChart z) := by
      rw [h]; exact mul_nonneg hY.le (by linarith)
    rw [mul_comm] at h3
    exact nonneg_of_mul_nonneg_left h3 hs

theorem regionTwo_eq_zero_of (hθ : σ.θ₂ = 0) {z : ℂ} (hz : 0 < z.im)
    (he : cuspZeroHeight z = σ.foldH) : ConeLayout.regionTwo σ.tTwo (σ.fermiChart z) = 0 := by
  have h := σ.regionTwo_mul hθ hz
  rw [he, sub_self, mul_zero] at h
  rcases mul_eq_zero.1 h with h' | h'
  · linarith [σ.sqrt_constK_pos]
  · exact h'

theorem inner_core_of_lens (hθ : σ.θ₂ = 0) (h₁ : Real.cos σ.θ₁ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₁)
    {z : ℂ} (hz : z ∈ σ.triangle) (h0 : σ.foldH ≤ cuspZeroHeight z)
    (h1 : σ.foldH ≤ σ.etaOne z) (hL : σ.sinhN z = 1 / 10) :
    normSq (σ.fermiChart z - ConeLayout.coreCentre) < ConeLayout.coreInner ^ 2 := by
  have h₂ : Real.cos σ.θ₂ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₂ :=
    Or.inr (by rw [hθ, Real.cos_zero]; norm_num)
  refine ConeLayout.lens_mem_core σ.tOne_pos.le (σ.tOne_le h₁ h₂)
    (by rw [σ.tTwo_eq_zero hθ]; norm_num) (σ.fermiChart_im_pos hz.1) ?_
    (σ.tOne_mul_normSq_fermiChart_le hz) (σ.tTwo_le_normSq_fermiChart hz)
    ((σ.regionOne_nonneg_iff h₁ h₂ hz.1).2 h1) ((σ.regionTwo_nonneg_iff hθ hz.1).2 h0)
  rw [σ.chart_neg_re hz.1, hL, ConeLayout.lensWidth]

theorem inner_core_of_windowOne (h₁ : Real.cos σ.θ₁ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₁)
    (h₂ : Real.cos σ.θ₂ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₂) {z : ℂ} (hz : z ∈ σ.triangle)
    (he : σ.etaOne z = σ.foldH) (hw1 : 1 / 10 ≤ σ.sinhN z) (hw2 : σ.sinhN z ≤ 7 / 50) :
    normSq (σ.fermiChart z - ConeLayout.coreCentre) < ConeLayout.coreInner ^ 2 := by
  have hY := σ.fermiChart_im_pos hz.1
  refine ConeLayout.windowOne_mem_core σ.tOne_pos.le (σ.tOne_le h₁ h₂) hY ?_ ?_
    (σ.regionOne_eq_zero_of hz.1 he) (σ.tOne_mul_normSq_fermiChart_le hz)
  · rw [σ.chart_neg_re hz.1, ConeLayout.lensWidth]
    exact mul_le_mul_of_nonneg_right hw1 hY.le
  · rw [σ.chart_neg_re hz.1, ConeLayout.windowEnd]
    exact mul_le_mul_of_nonneg_right hw2 hY.le

theorem inner_core_of_windowTwo (hθ : σ.θ₂ = 0) {z : ℂ} (hz : z ∈ σ.triangle)
    (he : cuspZeroHeight z = σ.foldH) (hw1 : 1 / 10 ≤ σ.sinhN z) (hw2 : σ.sinhN z ≤ 7 / 50) :
    normSq (σ.fermiChart z - ConeLayout.coreCentre) < ConeLayout.coreInner ^ 2 := by
  have hY := σ.fermiChart_im_pos hz.1
  refine ConeLayout.windowTwo_mem_core (by rw [σ.tTwo_eq_zero hθ]; norm_num) hY ?_ ?_
    (σ.regionTwo_eq_zero_of hθ hz.1 he) (σ.tTwo_le_normSq_fermiChart hz)
  · rw [σ.chart_neg_re hz.1, ConeLayout.lensWidth]
    exact mul_le_mul_of_nonneg_right hw1 hY.le
  · rw [σ.chart_neg_re hz.1, ConeLayout.windowEnd]
    exact mul_le_mul_of_nonneg_right hw2 hY.le

theorem wallSide_pos_of_outer_core (h₁ : Real.cos σ.θ₁ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₁)
    (h₂ : Real.cos σ.θ₂ = 0 ∨ 1 / 2 ≤ Real.cos σ.θ₂) {z : ℂ} (hz : 0 < z.im)
    (h : normSq (σ.fermiChart z - ConeLayout.coreCentre) ≤ ConeLayout.coreOuter ^ 2) :
    0 < σ.wallSide 0 z ∧ 0 < σ.wallSide 1 z ∧ 1 / 80 < σ.sinhN z := by
  have hE := σ.normSq_sub_rightFoot_pos hz
  have hk := σ.chartScale_pos
  have hY := σ.fermiChart_im_pos hz
  refine ⟨?_, ?_, ?_⟩
  · have := ConeLayout.core_wallZero_pos σ h₁ h₂ h
    rw [σ.wallZeroChart_fermiChart hz] at this
    have h2 : 0 < σ.chartScale ^ 2 * σ.wallSide 0 z := by
      have := mul_pos this hE
      rwa [div_mul_cancel₀ _ hE.ne'] at this
    exact pos_of_mul_pos_right h2 (by positivity)
  · have := ConeLayout.core_wallOne_pos σ h₁ h₂ h
    rw [σ.wallOneChart_fermiChart hz] at this
    have h2 : 0 < σ.chartScale ^ 2 * σ.wallSide 1 z := by
      have := mul_pos this hE
      rwa [div_mul_cancel₀ _ hE.ne'] at this
    exact pos_of_mul_pos_right h2 (by positivity)
  · have := ConeLayout.core_band h
    rw [σ.chart_neg_re hz, ConeLayout.lensWidth] at this
    have h3 : (1 / 10 / 8) * (σ.fermiChart z).im < σ.sinhN z * (σ.fermiChart z).im := this
    have := lt_of_mul_lt_mul_right h3 hY.le
    linarith

end ConeShape

end GC.Seifert
