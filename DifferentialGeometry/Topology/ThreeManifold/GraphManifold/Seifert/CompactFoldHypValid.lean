import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldHypCompact

/-!
# Bridge Jacobians and validity of the formulas on the hyperbolic triangle

Lane CF-H, tier 3 (design
`docs/geometrization/handoffs/20261004-design-cf-compact-triangle-fold.md`, §4–§5, curvature
`-1`). The positivity conditions of the bridge angles hold on the whole domains, by the moduli
bounds alone: `Re bridgeOne > 3/2 > |Re bridgeTwo|`, `Re bridgeZero < -3/2`
(`hpos_two_at_one`, `hpos_one_at_one`, …). Each bridge is a polar map about one centre with a
radius depending on the distance to one vertex (`bridgeTwo_polar` about `3/2` with `modOne`,
`bridgeOne_polar` and `bridgeZero_polar` about `0` with `modThree`), so A4's polar formula along
the hyperbolic circles gives positive Jacobians (`det_fderiv_bridgeTwo_pos`,
`det_fderiv_bridgeOne_pos`, `det_fderiv_bridgeZero_pos`).

On the triangle the rotated coordinates lie in their closed sectors, so every validity condition
of the corner Jacobians holds at each point other than the three vertices (`valid_one`,
`valid_two`, `valid_three`, the sector conditions of the lens switch and the outer blend, the
angle orders): the three corners have positive Jacobian on the whole triangle minus the vertices
for every choice of the blend parameters (`det_fderiv_cornerOne_pos_of_mem`, …).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace HypFold

theorem hasDerivAt_canonForm_comp {ρ : ℂ → ℝ} {z N : ℂ} {τ b : ℝ}
    (hρ : HasDerivAt (fun t : ℝ => ρ (z + t * N)) b 0) (hD : 1 - ρ z * τ ≠ 0) :
    HasDerivAt (fun t : ℝ => canonForm τ (ρ (z + t * N)))
      ((1 - τ ^ 2) / (1 - ρ z * τ) ^ 2 * b) 0 := by
  have h0 : ρ (z + ((0 : ℝ) : ℂ) * N) = ρ z := by simp
  have hc := hasDerivAt_canonForm' (τ := τ) (ϖ := ρ z) hD
  rw [← h0] at hc
  have := hc.comp (0 : ℝ) hρ
  rw [h0] at this
  exact this

theorem norm_add_re_pos_of_re {w : ℂ} (hw : w ≠ 0) (hre : 0 ≤ w.re) : 0 < ‖w‖ + w.re := by
  have := norm_pos_iff.2 hw
  linarith

theorem re_rot_nonneg {θ : ℝ} (hθ : 0 < θ) (hθ' : θ ≤ Real.pi / 2) {w : ℂ} (h1 : 0 ≤ w.im)
    (h2 : (exp (-((θ : ℂ) * I)) * w).im ≤ 0) : 0 ≤ (exp (-((θ : ℂ) * I)) * w).re := by
  rw [exp_neg_ofReal_mul_I_eq] at h2 ⊢
  simp only [mul_im, mul_re, sub_re, sub_im, ofReal_re, ofReal_im, I_re, I_im] at h2 ⊢
  have hs := sin_pos_of_le hθ hθ'
  have hc := cos_nonneg_of_le hθ hθ'
  have hx : 0 ≤ w.re := by nlinarith
  nlinarith

variable {σ : CompactShape}

section Hyp

variable (h : σ.curv = .hyperbolic)
include h

theorem modOne_polar {z : ℂ} (hz : z ∈ domOneTwo σ)
    (hpos2 : 0 < modOne σ z - ((bridgeTwo σ z).re - 3 / 2)) :
    bridgeTwo σ z = ((3 / 2 : ℝ) : ℂ) + (modOne σ z : ℂ) *
      exp ((angleTwoAtOne σ z : ℂ) * I) := by
  have hz1 := norm_lt_one_of_domOneTwo hz
  have hS : 0 < modOne σ z := by linarith [(modOne_mem h hz1).1]
  have hn : ‖bridgeTwo σ z - ((3 / 2 : ℝ) : ℂ)‖ = modOne σ z := by
    rw [show ((3 / 2 : ℝ) : ℂ) = 3 / 2 by push_cast; ring]
    exact (norm_bridgeTwo h hz).1
  exact polar_of_norm_sub_neg' hS hn hpos2

theorem hpos_two_at_one {z : ℂ} (hz : z ∈ domOneTwo σ) :
    0 < modOne σ z - ((bridgeTwo σ z).re - 3 / 2) := by
  have hz1 := norm_lt_one_of_domOneTwo hz
  have := abs_lt.1 (abs_re_bridgeTwo_lt h hz)
  linarith [(modOne_mem h hz1).1]

theorem hpos_two_at_two {z : ℂ} (hz : z ∈ domOneTwo σ) :
    0 < modTwo σ z + ((bridgeTwo σ z).re + 3 / 2) := by
  have hz1 := norm_lt_one_of_domOneTwo hz
  have := abs_lt.1 (abs_re_bridgeTwo_lt h hz)
  linarith [(modTwo_mem h hz1).1]

theorem hpos_one_at_one {z : ℂ} (hz : ‖z‖ < 1) :
    0 < modOne σ z + ((bridgeOne σ z).re - 3 / 2) := by
  have := three_halves_lt_re_bridgeOne h hz
  linarith [(modOne_mem h hz).1]

theorem hpos_zero_at_two {z : ℂ} (hz : ‖z‖ < 1) :
    0 < modTwo σ z - ((bridgeZero σ z).re + 3 / 2) := by
  have := re_bridgeZero_lt h hz
  linarith [(modTwo_mem h hz).1]

theorem hpos_one_at_three {z : ℂ} (hz : ‖z‖ < 1) :
    0 < modThree σ z + (bridgeOne σ z).re := by
  have := re_bridgeOne_pos h hz
  linarith [(modThree_mem h hz).1]

theorem hpos_zero_at_three {z : ℂ} (hz : ‖z‖ < 1) :
    0 < modThree σ z - (bridgeZero σ z).re := by
  have := re_bridgeZero_neg h hz
  linarith [(modThree_mem h hz).1]

theorem det_fderiv_bridgeTwo_pos {z : ℂ} (hz : z ∈ domOneTwo σ)
    (hψ' : 0 < ‖exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z‖ +
      (exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z).re) :
    0 < (fderiv ℝ (bridgeTwo σ) z).det := by
  have hz1 := norm_lt_one_of_domOneTwo hz
  have hv1 := norm_vertexOne_lt_one h
  have hne := (hd_ne_zero_of_domOneTwo h hz).2
  have hd0 : 0 < hd σ 0 z := lt_of_le_of_ne (hd_nonneg 0 z) (Ne.symm hne)
  have hd1 := hd_lt_one h 0 hz1
  have t0 := tauOne_pos h
  have t1 := tauOne_lt_one (σ := σ)
  have hD : 1 - hd σ 0 z * tauOne σ ≠ 0 := by nlinarith
  have hev : bridgeTwo σ =ᶠ[𝓝 z] fun u => ((3 / 2 : ℝ) : ℂ) +
      ((fun ϖ => 3 / 2 + compactProfileSlope * canonForm (tauOne σ) ϖ) (hd σ 0 u) : ℂ) *
        exp ((angleTwoAtOne σ u : ℂ) * I) := by
    filter_upwards [(isOpen_domOneTwo h).mem_nhds hz] with u hu
    exact modOne_polar h hu (hpos_two_at_one h hu)
  rw [hev.fderiv_eq]
  have hS : HasDerivAt (fun ϖ => 3 / 2 + compactProfileSlope * canonForm (tauOne σ) ϖ)
      (compactProfileSlope * ((1 - tauOne σ ^ 2) / (1 - hd σ 0 z * tauOne σ) ^ 2))
      (hd σ 0 z) :=
    ((hasDerivAt_canonForm' hD).const_mul _).const_add _
  obtain ⟨D, hD0, hΘγ⟩ := exists_hasDerivAt_angleTwoAtOne h hz (hpos_two_at_one h hz) hψ'
  have hρ : DifferentiableAt ℝ (hd σ 0) z :=
    (contDiffAt_hd h 0 hz1 hne).differentiableAt (by simp)
  have hΘd : DifferentiableAt ℝ (angleTwoAtOne σ) z :=
    (contDiffAt_angleTwoAtOne h hz (hpos_two_at_one h hz)).differentiableAt (by simp)
  have hργ : ∀ᶠ t in 𝓝 (0 : ℝ), hd σ 0 (hcirc σ.vertexOne z t) = hd σ 0 z :=
    Eventually.of_forall fun t => hd_hcirc h 0 hz1 t
  have hm0 : mob σ.vertexOne z ≠ 0 := norm_ne_zero_iff.1 hne
  have hρN : HasDerivAt (fun t : ℝ => hd σ 0 (z + t * hrad σ.vertexOne z)) (hd σ 0 z) 0 :=
    hasDerivAt_norm_mob_hrad hv1 hz1 hm0
  have key := det_fderiv_polar (c := ((3 / 2 : ℝ) : ℂ)) hS hρ hΘd
    (hasDerivAt_hcirc hv1 hz1) (hcirc_zero hv1 hz1) hργ hΘγ hρN (hasDerivAt_comp_ray' hΘd)
  rw [cross_I_mul] at key
  have hN : 0 < ‖hrad σ.vertexOne z‖ ^ 2 := by
    have := norm_pos_iff.2 (hrad_ne_zero hv1 hz1 hm0)
    positivity
  have hS0 : 0 < 3 / 2 + compactProfileSlope * canonForm (tauOne σ) (hd σ 0 z) := by
    have := modOne_mem h hz1
    rw [modOne_eq_radial] at this
    linarith [this.1]
  have hS' : 0 < compactProfileSlope * ((1 - tauOne σ ^ 2) / (1 - hd σ 0 z * tauOne σ) ^ 2) := by
    have : 0 < 1 - tauOne σ ^ 2 := by nlinarith
    unfold compactProfileSlope
    positivity
  exact det_pos_of_polar' hN key (by positivity)

theorem bridgeOne_polar {z : ℂ} (hz : z ∈ domOneThree σ) :
    bridgeOne σ z = ((0 : ℝ) : ℂ) + (modThree σ z : ℂ) * exp ((angleOneAtThree σ z : ℂ) * I) := by
  have hz1 := norm_lt_one_of_domOneThree hz
  have hS : 0 < modThree σ z := by linarith [(modThree_mem h hz1).1]
  have hn : ‖bridgeOne σ z - ((0 : ℝ) : ℂ)‖ = modThree σ z := by
    rw [ofReal_zero, sub_zero]
    exact (norm_bridgeOne h hz).1
  have e := polar_of_norm_sub' hS hn (by rw [sub_zero]; exact hpos_one_at_three h hz1)
  rw [sub_zero] at e
  exact e

theorem det_fderiv_bridgeOne_pos {z : ℂ} (hz : z ∈ domOneThree σ) :
    0 < (fderiv ℝ (bridgeOne σ) z).det := by
  have hz1 := norm_lt_one_of_domOneThree hz
  have h00 : ‖(0 : ℂ)‖ < 1 := by simp
  have hz0 : z ≠ 0 := norm_ne_zero_iff.1 (hd_ne_zero_of_domOneThree h hz).1
  have hd0 : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have t0 := tauThree_pos h
  have t1 := tauThree_lt_one (σ := σ)
  have hD : 1 - ‖z‖ * tauThree σ ≠ 0 := by nlinarith
  have hev : bridgeOne σ =ᶠ[𝓝 z] fun u => ((0 : ℝ) : ℂ) +
      ((fun ϖ => 3 - compactProfileSlope * canonForm (tauThree σ) ϖ) ((fun v : ℂ => ‖v‖) u) : ℂ) *
        exp ((angleOneAtThree σ u : ℂ) * I) := by
    filter_upwards [(isOpen_domOneThree h).mem_nhds hz] with u hu
    exact bridgeOne_polar h hu
  rw [hev.fderiv_eq]
  have hS : HasDerivAt (fun ϖ => 3 - compactProfileSlope * canonForm (tauThree σ) ϖ)
      (-(compactProfileSlope * ((1 - tauThree σ ^ 2) / (1 - ‖z‖ * tauThree σ) ^ 2))) ‖z‖ :=
    ((hasDerivAt_canonForm' hD).const_mul _).const_sub _
  obtain ⟨D, hD0, hΘγ⟩ := exists_hasDerivAt_angleOneAtThree h hz (hpos_one_at_three h hz1)
  have hnc : ContDiffAt ℝ ∞ (fun u : ℂ => ‖u‖) z := contDiffAt_norm ℝ hz0
  have hρ : DifferentiableAt ℝ (fun u : ℂ => ‖u‖) z := hnc.differentiableAt (by simp)
  have hΘd : DifferentiableAt ℝ (angleOneAtThree σ) z :=
    (contDiffAt_angleOneAtThree h hz (hpos_one_at_three h hz1)).differentiableAt (by simp)
  have hργ : ∀ᶠ t in 𝓝 (0 : ℝ), ‖hcirc 0 z t‖ = ‖z‖ :=
    Eventually.of_forall fun t => by rw [hcirc_zero_left, norm_mul_exp]
  have hm0 : mob 0 z ≠ 0 := by rwa [mob_zero_left]
  have hρN : HasDerivAt (fun t : ℝ => ‖z + t * hrad 0 z‖) ‖z‖ 0 := by
    have := hasDerivAt_norm_mob_hrad h00 hz1 hm0
    simp only [mob_zero_left] at this
    exact this
  have key := det_fderiv_polar (c := ((0 : ℝ) : ℂ)) hS hρ hΘd
    (hasDerivAt_hcirc h00 hz1) (hcirc_zero h00 hz1) hργ hΘγ hρN (hasDerivAt_comp_ray' hΘd)
  rw [cross_I_mul] at key
  have hN : 0 < ‖hrad 0 z‖ ^ 2 := by
    have := norm_pos_iff.2 (hrad_ne_zero h00 hz1 hm0)
    positivity
  have hS0 : 0 < 3 - compactProfileSlope * canonForm (tauThree σ) ‖z‖ := by
    have := modThree_mem h hz1
    rw [modThree_eq_radial] at this
    linarith [this.1]
  have hS' : 0 < compactProfileSlope * ((1 - tauThree σ ^ 2) / (1 - ‖z‖ * tauThree σ) ^ 2) := by
    have : 0 < 1 - tauThree σ ^ 2 := by nlinarith
    unfold compactProfileSlope
    positivity
  have hpos : 0 < (3 - compactProfileSlope * canonForm (tauThree σ) ‖z‖) *
      -(compactProfileSlope * ((1 - tauThree σ ^ 2) / (1 - ‖z‖ * tauThree σ) ^ 2)) * D * ‖z‖ := by
    have := mul_pos_of_neg_of_neg (neg_neg_of_pos hS') hD0
    have := mul_pos hS0 this
    nlinarith
  exact det_pos_of_polar' hN key hpos

theorem bridgeZero_polar {z : ℂ} (hz : z ∈ domZeroThree σ) :
    bridgeZero σ z = ((0 : ℝ) : ℂ) + (modThree σ z : ℂ) * exp ((angleZeroAtThree σ z : ℂ) * I) := by
  have hz1 := norm_lt_one_of_domZeroThree hz
  have hS : 0 < modThree σ z := by linarith [(modThree_mem h hz1).1]
  have hn : ‖bridgeZero σ z - ((0 : ℝ) : ℂ)‖ = modThree σ z := by
    rw [ofReal_zero, sub_zero]
    exact (norm_bridgeZero h hz).1
  have e := polar_of_norm_sub_neg' hS hn (by rw [sub_zero]; exact hpos_zero_at_three h hz1)
  rw [sub_zero] at e
  exact e

theorem det_fderiv_bridgeZero_pos {z : ℂ} (hz : z ∈ domZeroThree σ) :
    0 < (fderiv ℝ (bridgeZero σ) z).det := by
  have hz1 := norm_lt_one_of_domZeroThree hz
  have h00 : ‖(0 : ℂ)‖ < 1 := by simp
  have hz0 : z ≠ 0 := norm_ne_zero_iff.1 (hd_ne_zero_of_domZeroThree h hz).1
  have hd0 : 0 < ‖z‖ := norm_pos_iff.2 hz0
  have t0 := tauThree_pos h
  have t1 := tauThree_lt_one (σ := σ)
  have hD : 1 - ‖z‖ * tauThree σ ≠ 0 := by nlinarith
  have hev : bridgeZero σ =ᶠ[𝓝 z] fun u => ((0 : ℝ) : ℂ) +
      ((fun ϖ => 3 - compactProfileSlope * canonForm (tauThree σ) ϖ) ((fun v : ℂ => ‖v‖) u) : ℂ) *
        exp ((angleZeroAtThree σ u : ℂ) * I) := by
    filter_upwards [(isOpen_domZeroThree h).mem_nhds hz] with u hu
    exact bridgeZero_polar h hu
  rw [hev.fderiv_eq]
  have hS : HasDerivAt (fun ϖ => 3 - compactProfileSlope * canonForm (tauThree σ) ϖ)
      (-(compactProfileSlope * ((1 - tauThree σ ^ 2) / (1 - ‖z‖ * tauThree σ) ^ 2))) ‖z‖ :=
    ((hasDerivAt_canonForm' hD).const_mul _).const_sub _
  obtain ⟨D, hD0, hΘγ⟩ := exists_hasDerivAt_angleZeroAtThree h hz (hpos_zero_at_three h hz1)
  have hnc : ContDiffAt ℝ ∞ (fun u : ℂ => ‖u‖) z := contDiffAt_norm ℝ hz0
  have hρ : DifferentiableAt ℝ (fun u : ℂ => ‖u‖) z := hnc.differentiableAt (by simp)
  have hΘd : DifferentiableAt ℝ (angleZeroAtThree σ) z :=
    (contDiffAt_angleZeroAtThree h hz (hpos_zero_at_three h hz1)).differentiableAt (by simp)
  have hργ : ∀ᶠ t in 𝓝 (0 : ℝ), ‖hcirc 0 z t‖ = ‖z‖ :=
    Eventually.of_forall fun t => by rw [hcirc_zero_left, norm_mul_exp]
  have hm0 : mob 0 z ≠ 0 := by rwa [mob_zero_left]
  have hρN : HasDerivAt (fun t : ℝ => ‖z + t * hrad 0 z‖) ‖z‖ 0 := by
    have := hasDerivAt_norm_mob_hrad h00 hz1 hm0
    simp only [mob_zero_left] at this
    exact this
  have key := det_fderiv_polar (c := ((0 : ℝ) : ℂ)) hS hρ hΘd
    (hasDerivAt_hcirc h00 hz1) (hcirc_zero h00 hz1) hργ hΘγ hρN (hasDerivAt_comp_ray' hΘd)
  rw [cross_I_mul] at key
  have hN : 0 < ‖hrad 0 z‖ ^ 2 := by
    have := norm_pos_iff.2 (hrad_ne_zero h00 hz1 hm0)
    positivity
  have hS0 : 0 < 3 - compactProfileSlope * canonForm (tauThree σ) ‖z‖ := by
    have := modThree_mem h hz1
    rw [modThree_eq_radial] at this
    linarith [this.1]
  have hS' : 0 < compactProfileSlope * ((1 - tauThree σ ^ 2) / (1 - ‖z‖ * tauThree σ) ^ 2) := by
    have : 0 < 1 - tauThree σ ^ 2 := by nlinarith
    unfold compactProfileSlope
    positivity
  have hpos : 0 < (3 - compactProfileSlope * canonForm (tauThree σ) ‖z‖) *
      -(compactProfileSlope * ((1 - tauThree σ ^ 2) / (1 - ‖z‖ * tauThree σ) ^ 2)) * D * ‖z‖ := by
    have := mul_pos_of_neg_of_neg (neg_neg_of_pos hS') hD0
    have := mul_pos hS0 this
    nlinarith
  exact det_pos_of_polar' hN key hpos

theorem rotOne_ne_zero {z : ℂ} (hz : ‖z‖ < 1) (h1 : z ≠ σ.vertexOne) : σ.rotOne z ≠ 0 := by
  intro h0
  apply h1
  rw [rotOne_eq_mul_mob h] at h0
  have hm := (mul_eq_zero.1 h0).resolve_left (neg_ne_zero.2 (Complex.exp_ne_zero _))
  rw [← mobInv_mob (normSq_vertexOne_ne_one h)
    (one_sub_conj_mul_ne_zero (norm_vertexOne_lt_one h) hz), hm]
  simp [mobInv]

theorem valid_one {z : ℂ} (hz : z ∈ σ.triangle) (h1 : z ≠ σ.vertexOne) :
    0 < ‖σ.rotOne z‖ + (σ.rotOne z).re ∧
      0 < ‖exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z‖ + (exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z).re ∧
      0 ≤ (exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z).re := by
  have hz1 := norm_lt_one_of_mem h hz
  have hs := sector_one h hz
  have hne := rotOne_ne_zero h hz1 h1
  have hr := re_nonneg_of_sector (θ₁_pos σ) (θ₁_le σ) hs.1 hs.2
  have hr' := re_rot_nonneg (θ₁_pos σ) (θ₁_le σ) hs.1 hs.2
  refine ⟨norm_add_re_pos_of_re hne hr, norm_add_re_pos_of_re ?_ hr', hr'⟩
  exact mul_ne_zero (Complex.exp_ne_zero _) hne

theorem valid_two {z : ℂ} (hz : z ∈ σ.triangle) (h2 : z ≠ σ.vertexTwo) :
    0 < ‖σ.rotTwo z‖ + (σ.rotTwo z).re ∧
      0 < ‖exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z‖ + (exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z).re ∧
      0 ≤ (σ.rotTwo z).re := by
  have hz1 := norm_lt_one_of_mem h hz
  have hs := sector_two h hz
  have hne : σ.rotTwo z ≠ 0 := by
    intro h0
    exact h2 (rotTwo_injOn h hz1 (norm_vertexTwo_lt_one h) (by rw [h0, rotTwo_vertexTwo h]))
  have hr := re_nonneg_of_sector (θ₂_pos σ) (θ₂_le σ) hs.1 hs.2
  have hr' := re_rot_nonneg (θ₂_pos σ) (θ₂_le σ) hs.1 hs.2
  refine ⟨norm_add_re_pos_of_re hne hr, norm_add_re_pos_of_re ?_ hr', hr⟩
  exact mul_ne_zero (Complex.exp_ne_zero _) hne

omit h in
theorem valid_three {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) : 0 < ‖z‖ + z.re :=
  norm_add_re_pos_of_re h0 (re_nonneg_of_mem hz)

theorem det_fderiv_cornerOne_pos_of_mem {a b β β' : ℝ} (hab : a < b) (hβ : β < β') {z : ℂ}
    (hz : z ∈ σ.triangle) (h0 : z ≠ 0) (h1 : z ≠ σ.vertexOne) (h2 : z ≠ σ.vertexTwo) :
    0 < (fderiv ℝ (cornerOne σ a b β β') z).det := by
  have hz1 := norm_lt_one_of_mem h hz
  have d13 := mem_domOneThree h hz h0 h1
  have d12 := mem_domOneTwo h hz h1 h2
  obtain ⟨v1, v2, v3⟩ := valid_one h hz h1
  exact det_fderiv_cornerOne_pos h hab hβ d13 d12 v1 v2 (hpos_one_at_one h hz1)
    (hpos_two_at_one h d12) (angleOneAtOne_le_angleTwoAtOne h d13 d12 (hpos_one_at_one h hz1)
      (hpos_two_at_one h d12) (hz.2 1) (sector_two h hz).1) (Or.inl v3)

theorem det_fderiv_cornerTwo_pos_of_mem {a b β β' : ℝ} (hab : a < b) (hβ : β < β') {z : ℂ}
    (hz : z ∈ σ.triangle) (h0 : z ≠ 0) (h1 : z ≠ σ.vertexOne) (h2 : z ≠ σ.vertexTwo) :
    0 < (fderiv ℝ (cornerTwo σ a b β β') z).det := by
  have hz1 := norm_lt_one_of_mem h hz
  have d03 := mem_domZeroThree h hz h0 h2
  have d12 := mem_domOneTwo h hz h1 h2
  obtain ⟨v1, v2, v3⟩ := valid_two h hz h2
  exact det_fderiv_cornerTwo_pos h hab hβ d12 d03 v2 (hpos_two_at_two h d12)
    (hpos_zero_at_two h hz1) (angleTwoAtTwo_le_angleZeroAtTwo h d12 d03
      (hpos_two_at_two h d12) (hpos_zero_at_two h hz1) (sector_two h hz).1 (hz.2 0)) (Or.inl v3)

theorem det_fderiv_cornerThree_pos_of_mem {a b w δ : ℝ} (hab : a < b) (hb : b ≤ 1 / 5)
    (hw : 0 < w) (hδ : 0 < δ) {z : ℂ}
    (hz : z ∈ σ.triangle) (h0 : z ≠ 0) (h1 : z ≠ σ.vertexOne) (h2 : z ≠ σ.vertexTwo) :
    0 < (fderiv ℝ (cornerThree σ a b w δ) z).det := by
  have hz1 := norm_lt_one_of_mem h hz
  have d13 := mem_domOneThree h hz h0 h1
  have d03 := mem_domZeroThree h hz h0 h2
  exact det_fderiv_cornerThree_pos h hab hb hw hδ d13 d03 (valid_three hz h0)
    (hpos_one_at_three h hz1) (hpos_zero_at_three h hz1)
    (angleOneAtThree_le_angleZeroAtThree h d13 d03 (hpos_one_at_three h hz1)
      (hpos_zero_at_three h hz1) (hz.2 1) (hz.2 0)) (Or.inl ⟨hz.2 0, hz.2 1⟩)

end Hyp

end HypFold

end GC.Seifert
