import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveSplitCappedSide

/-!
# Ports and sides of the split sphere

Lane N2d, side model, step 1. In the host chart `w` of the circle `l` of the round pants
(`hostChart l`, inverse `hostInv l`), the level of a point is the second strip coordinate
`stripLevel l w = (stripCenter l · stripBump (Im w) - Re w) / (tubeSlope · stripWidth (Im w))`;
on the band of the split tube it is the tube height. The two circles of the pants other than `l`
lie on the two sides of the split sphere: `sidePort l t` is the circle on the side of sign
`sgnR t` (`0 ↦ (1, 2)`, `1 ↦ (0, 2)`, `2 ↦ (1, 0)` for `t = false, true`). On the closed
outer region of `sidePort l t` of collar depth `1/8` (the hole or the exterior of the outer
circle together with its collar of width `1/2`), the signed level `sgnR t · stripLevel` exceeds
`3`, the height of the tube (`lt_sgnR_mul_stripLevel`): the remaining ports and their collars
avoid the tube, on the correct sides.
-/

set_option autoImplicit false

noncomputable section
open Set Function Metric
open DifferentialGeometry DifferentialGeometry.Topology
open scoped Manifold ContDiff Topology

namespace GC.Seifert.SplitTube

def hostInv (l : Fin 3) (z : ℂ) : ℂ := if l.val = 0 then z else (z - planarCenter 3 l)⁻¹

theorem hostInv_of_zero {l : Fin 3} (hl : l.val = 0) (z : ℂ) : hostInv l z = z := by
  simp [hostInv, hl]

theorem hostInv_of_ne {l : Fin 3} (hl : l.val ≠ 0) (z : ℂ) :
    hostInv l z = (z - planarCenter 3 l)⁻¹ := by
  simp [hostInv, hl]

theorem hostChart_hostInv (l : Fin 3) (z : ℂ) : hostChart l (hostInv l z) = z := by
  by_cases hl : l.val = 0
  · simp [hostChart, hostInv, hl]
  · simp [hostChart, hostInv, hl]

theorem hostInv_hostChart (l : Fin 3) (w : ℂ) : hostInv l (hostChart l w) = w := by
  by_cases hl : l.val = 0
  · simp [hostChart, hostInv, hl]
  · simp [hostChart, hostInv, hl]

def stripLevel (l : Fin 3) (w : ℂ) : ℝ := (stripInv l w).2

theorem stripLevel_eq (l : Fin 3) (w : ℂ) : stripLevel l w =
    (stripCenter l * stripBump w.im - w.re) / (tubeSlope * stripWidth w.im) :=
  rfl

theorem stripLevel_strip (l : Fin 3) (q : ℝ × ℝ) : stripLevel l (strip l q) = q.2 := by
  change ((stripDiffeo l).symm ((stripDiffeo l) q)).2 = q.2
  rw [Diffeomorph.symm_apply_apply]

theorem contDiff_stripLevel (l : Fin 3) : ContDiff ℝ ∞ (stripLevel l) := by
  have him : ContDiff ℝ ∞ (fun w : ℂ => w.im) := Complex.imCLM.contDiff
  have hre : ContDiff ℝ ∞ (fun w : ℂ => w.re) := Complex.reCLM.contDiff
  exact ((contDiff_const.mul (contDiff_stripBump.comp him)).sub hre).div
    (contDiff_const.mul (contDiff_stripWidth.comp him))
    fun w => tubeSlope_mul_stripWidth_ne w.im

def sidePort (l : Fin 3) (t : Bool) : Fin 3 :=
  if l.val = 0 then (if t then 2 else 1) else if l.val = 1 then (if t then 2 else 0)
  else (if t then 0 else 1)

theorem sidePort_ne (l : Fin 3) (t : Bool) : sidePort l t ≠ l := by
  fin_cases l <;> cases t <;> simp [sidePort]

theorem sidePort_false_ne_true (l : Fin 3) : sidePort l false ≠ sidePort l true := by
  fin_cases l <;> simp [sidePort]

def outerCollarRegion (p : Fin 3) : Set ℂ :=
  {z | planarSign p * (‖z - planarCenter 3 p‖ - planarRadius p) ≤ 1 / 8}

theorem planarCollarFormula_mem_outerCollarRegion (p : Fin 3) (θ : Circle) {s : ℝ}
    (hs0 : 0 ≤ s) (hs : s ≤ 1 / 2) :
    planarCollarFormula 3 p ((θ : ℂ), s) ∈ outerCollarRegion p := by
  change planarSign p * (‖planarCollarFormula 3 p ((θ : ℂ), s) - planarCenter 3 p‖ -
    planarRadius p) ≤ 1 / 8
  rw [planarSign_mul_collar p θ hs0 (by linarith)]
  linarith

theorem abs_le_of_mul_self_le {x r : ℝ} (hr : 0 ≤ r) (h : x * x ≤ r * r) : |x| ≤ r := by
  rw [abs_le]
  constructor <;> nlinarith

theorem three_lt_stripLevel_of_margin (l : Fin 3) (w : ℂ) {σ : ℝ} (hW : |w.im| ≤ 1)
    (hm : 1 / 100 ≤ σ * (stripCenter l * stripBump w.im - w.re)) :
    3 < σ * stripLevel l w := by
  have hW0 := stripWidth_pos w.im
  have hW2 : stripWidth w.im ≤ 2 := by linarith [stripWidth_le w.im]
  have hα : (0 : ℝ) < tubeSlope := by norm_num [tubeSlope]
  rw [stripLevel_eq, mul_div_assoc', lt_div_iff₀ (mul_pos hα hW0)]
  have h1 : tubeSlope * stripWidth w.im ≤ 2 / 1000 := by
    rw [tubeSlope]
    linarith
  nlinarith

theorem inv_re_im_bound {u : ℂ} (hu : u ≠ 0) {C R : ℝ} (hR : 0 ≤ R)
    (h : 1 - 2 * C * u.re ≤ (R ^ 2 - C ^ 2) * Complex.normSq u) :
    |(u⁻¹).re - C| ≤ R ∧ |(u⁻¹).im| ≤ R := by
  have hn : 0 < Complex.normSq u := Complex.normSq_pos.mpr hu
  have hre : (u⁻¹).re = u.re / Complex.normSq u := Complex.inv_re u
  have him : (u⁻¹).im = -u.im / Complex.normSq u := Complex.inv_im u
  have hnu : Complex.normSq u = u.re * u.re + u.im * u.im := Complex.normSq_apply u
  have key : ((u⁻¹).re - C) ^ 2 + (u⁻¹).im ^ 2 ≤ R ^ 2 := by
    rw [hre, him]
    have e : (u.re / Complex.normSq u - C) ^ 2 + (-u.im / Complex.normSq u) ^ 2 =
        (1 - 2 * C * u.re + C ^ 2 * Complex.normSq u) / Complex.normSq u := by
      field_simp
      rw [hnu]
      ring
    rw [e, div_le_iff₀ hn]
    linarith
  constructor
  · rw [abs_le]
    constructor <;> nlinarith [sq_nonneg ((u⁻¹).im), sq_nonneg ((u⁻¹).re - C + R),
      sq_nonneg ((u⁻¹).re - C - R)]
  · rw [abs_le]
    constructor <;> nlinarith [sq_nonneg ((u⁻¹).re - C), sq_nonneg ((u⁻¹).im + R),
      sq_nonneg ((u⁻¹).im - R)]

theorem three_lt_of_inv_bound (l : Fin 3) (w : ℂ) {C R σ : ℝ} (hσ : σ = 1 ∨ σ = -1)
    (h1 : |w.re - C| ≤ R) (h2 : |w.im| ≤ R) (hR : R ≤ 1 / 2)
    (hm : 1 / 100 + R ≤ σ * (stripCenter l - C)) : 3 < σ * stripLevel l w := by
  have hB : stripBump w.im = 1 := stripBump_of_le_half (h2.trans hR)
  refine three_lt_stripLevel_of_margin l w (by linarith) ?_
  rw [hB, mul_one]
  have h1' := abs_le.mp h1
  rcases hσ with rfl | rfl <;> linarith [h1'.1, h1'.2]

theorem normSq_sub_real (z : ℂ) (c : ℝ) :
    Complex.normSq (z - c) = (z.re - c) * (z.re - c) + z.im * z.im := by
  rw [Complex.normSq_apply]
  simp

theorem norm_sq_eq_normSq (z : ℂ) : ‖z‖ ^ 2 = Complex.normSq z := Complex.sq_norm z

theorem lt_sgnR_mul_stripLevel (l : Fin 3) (t : Bool) {z : ℂ}
    (hz : z ∈ outerCollarRegion (sidePort l t)) :
    (l.val ≠ 0 → z ≠ planarCenter 3 l) ∧ 3 < sgnR t * stripLevel l (hostInv l z) := by
  have hz' : planarSign (sidePort l t) *
      (‖z - planarCenter 3 (sidePort l t)‖ - planarRadius (sidePort l t)) ≤ 1 / 8 := hz
  have hsq : ∀ a : ℂ, ∀ r : ℝ, 0 ≤ r → ‖a‖ ≤ r → Complex.normSq a ≤ r ^ 2 := by
    intro a r hr ha
    rw [← norm_sq_eq_normSq]
    exact pow_le_pow_left₀ (norm_nonneg a) ha 2
  have hsq' : ∀ a : ℂ, ∀ r : ℝ, 0 ≤ r → r ≤ ‖a‖ → r ^ 2 ≤ Complex.normSq a := by
    intro a r hr ha
    rw [← norm_sq_eq_normSq]
    exact pow_le_pow_left₀ hr ha 2
  fin_cases l <;> cases t
  · simp only [sidePort, planarSign, planarRadius, planarCenter] at hz'
    norm_num at hz'
    have hn := hsq _ _ (by norm_num) (show ‖z - ((3 / 2 : ℝ) : ℂ)‖ ≤ 5 / 8 by push_cast; linarith)
    rw [normSq_sub_real] at hn
    have him : z.im * z.im ≤ (5 / 8) * (5 / 8) := by nlinarith [mul_self_nonneg (z.re - 3 / 2)]
    have hre : (z.re - 3 / 2) * (z.re - 3 / 2) ≤ (5 / 8) * (5 / 8) := by
      nlinarith [mul_self_nonneg z.im]
    have hre' := abs_le.mp (abs_le_of_mul_self_le (by norm_num) hre)
    refine ⟨by simp, ?_⟩
    rw [hostInv_of_zero (by simp)]
    refine three_lt_stripLevel_of_margin _ z ?_ ?_
    · linarith [abs_le_of_mul_self_le (by norm_num) him]
    · simp only [stripCenter, sgnR]
      norm_num
      linarith [hre'.1]
  · simp only [sidePort, planarSign, planarRadius, planarCenter] at hz'
    norm_num at hz'
    have hn := hsq _ _ (by norm_num) (show ‖z - ((-(3 / 2) : ℝ) : ℂ)‖ ≤ 5 / 8 by
      convert hz' using 2; push_cast; ring)
    rw [normSq_sub_real] at hn
    have him : z.im * z.im ≤ (5 / 8) * (5 / 8) := by nlinarith [mul_self_nonneg (z.re + 3 / 2)]
    have hre : (z.re + 3 / 2) * (z.re + 3 / 2) ≤ (5 / 8) * (5 / 8) := by
      nlinarith [mul_self_nonneg z.im]
    have hre' := abs_le.mp (abs_le_of_mul_self_le (by norm_num) hre)
    refine ⟨by simp, ?_⟩
    rw [hostInv_of_zero (by simp)]
    refine three_lt_stripLevel_of_margin _ z ?_ ?_
    · linarith [abs_le_of_mul_self_le (by norm_num) him]
    · simp only [stripCenter, sgnR]
      norm_num
      linarith [hre'.2]
  · simp only [sidePort, planarSign, planarRadius, planarCenter] at hz'
    norm_num at hz'
    have hn := hsq' z (23 / 8) (by norm_num) (by linarith)
    rw [Complex.normSq_apply] at hn
    have hc : planarCenter 3 (⟨1, by norm_num⟩ : Fin 3) = 3 / 2 := by simp [planarCenter]
    have hu : z - ((3 / 2 : ℝ) : ℂ) ≠ 0 := by
      intro h0
      have : z = ((3 / 2 : ℝ) : ℂ) := sub_eq_zero.mp h0
      rw [this] at hn
      simp at hn
      norm_num at hn
    have hb := inv_re_im_bound hu (C := 96 / 385) (R := 184 / 385) (by norm_num) (by
      rw [normSq_sub_real]
      simp only [Complex.sub_re, Complex.ofReal_re]
      nlinarith)
    dsimp only
    refine ⟨fun _ h => hu (by rw [h, hc]; simp), ?_⟩
    rw [hostInv_of_ne (by simp), hc]
    exact three_lt_of_inv_bound _ _ (Or.inr rfl) hb.1 hb.2 (by norm_num)
      (by simp [stripCenter, sgnR]; norm_num)
  · simp only [sidePort, planarSign, planarRadius, planarCenter] at hz'
    norm_num at hz'
    have hn := hsq _ _ (by norm_num) (show ‖z - ((-(3 / 2) : ℝ) : ℂ)‖ ≤ 5 / 8 by
      convert hz' using 2; push_cast; ring)
    rw [normSq_sub_real] at hn
    have hc : planarCenter 3 (⟨1, by norm_num⟩ : Fin 3) = 3 / 2 := by simp [planarCenter]
    have hu : z - ((3 / 2 : ℝ) : ℂ) ≠ 0 := by
      intro h0
      have : z = ((3 / 2 : ℝ) : ℂ) := sub_eq_zero.mp h0
      rw [this] at hn
      simp at hn
      norm_num at hn
    have hb := inv_re_im_bound hu (C := -(192 / 551)) (R := 40 / 551) (by norm_num) (by
      rw [normSq_sub_real]
      simp only [Complex.sub_re, Complex.ofReal_re]
      nlinarith)
    dsimp only
    refine ⟨fun _ h => hu (by rw [h, hc]; simp), ?_⟩
    rw [hostInv_of_ne (by simp), hc]
    exact three_lt_of_inv_bound _ _ (Or.inl rfl) hb.1 hb.2 (by norm_num)
      (by simp [stripCenter, sgnR]; norm_num)
  · simp only [sidePort, planarSign, planarRadius, planarCenter] at hz'
    norm_num at hz'
    have hn := hsq _ _ (by norm_num) (show ‖z - ((3 / 2 : ℝ) : ℂ)‖ ≤ 5 / 8 by
      push_cast; linarith)
    rw [normSq_sub_real] at hn
    have hc : planarCenter 3 (⟨2, by norm_num⟩ : Fin 3) = -(3 / 2) := by simp [planarCenter]
    have hu : z - ((-(3 / 2) : ℝ) : ℂ) ≠ 0 := by
      intro h0
      have : z = ((-(3 / 2) : ℝ) : ℂ) := sub_eq_zero.mp h0
      rw [this] at hn
      simp at hn
      norm_num at hn
    have hb := inv_re_im_bound hu (C := 192 / 551) (R := 40 / 551) (by norm_num) (by
      rw [normSq_sub_real]
      simp only [Complex.sub_re, Complex.ofReal_re]
      nlinarith)
    dsimp only
    refine ⟨fun _ h => hu (by rw [h, hc]; simp), ?_⟩
    rw [hostInv_of_ne (by simp), hc]
    exact three_lt_of_inv_bound _ _ (Or.inr rfl) hb.1 hb.2 (by norm_num)
      (by simp [stripCenter, sgnR]; norm_num)
  · simp only [sidePort, planarSign, planarRadius, planarCenter] at hz'
    norm_num at hz'
    have hn := hsq' z (23 / 8) (by norm_num) (by linarith)
    rw [Complex.normSq_apply] at hn
    have hc : planarCenter 3 (⟨2, by norm_num⟩ : Fin 3) = -(3 / 2) := by simp [planarCenter]
    have hu : z - ((-(3 / 2) : ℝ) : ℂ) ≠ 0 := by
      intro h0
      have : z = ((-(3 / 2) : ℝ) : ℂ) := sub_eq_zero.mp h0
      rw [this] at hn
      simp at hn
      norm_num at hn
    have hb := inv_re_im_bound hu (C := -(96 / 385)) (R := 184 / 385) (by norm_num) (by
      rw [normSq_sub_real]
      simp only [Complex.sub_re, Complex.ofReal_re]
      nlinarith)
    dsimp only
    refine ⟨fun _ h => hu (by rw [h, hc]; simp), ?_⟩
    rw [hostInv_of_ne (by simp), hc]
    exact three_lt_of_inv_bound _ _ (Or.inl rfl) hb.1 hb.2 (by norm_num)
      (by simp [stripCenter, sgnR]; norm_num)

end GC.Seifert.SplitTube
