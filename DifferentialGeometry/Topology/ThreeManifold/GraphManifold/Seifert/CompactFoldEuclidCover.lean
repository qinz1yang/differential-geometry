import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldEuclidPieces

/-!
# The pieces of the flat compact fold cover the triangle outside the core

Lane CF, tier 3, curvature `0` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §5, with review 23 §6.1). Every point of the
triangle other than `v₃ = 0` and outside the inner core disc `‖z - incenter‖ < coreRadius -
coreMargin` lies in one of the nine pieces of `CompactFoldEuclidPieces` (`mem_goodSet`).

The validity conditions of the pieces hold pointwise on the triangle:
* the angles `discAngle z`, `psiOne z`, `psiTwo z` lie in the sectors `[0, θ₃]`, `[0, θ₁]`,
  `[0, θ₂]`, with the end values exactly on the walls (`discAngle_sector`);
* the signs of the real parts of the bridges follow from the moduli bounds of
  `CompactFoldEuclidBridges` (`three_halves_lt_re_bridgeOne`, …);
* the lens-switch condition of the corners at `v₁`, `v₂` holds because the tangential coordinate
  along wall 2 is positive off the vertex, or zero only when the point lies at height `d₁`
  above wall 2 (`hlam_one`, `hlam_two`, from `wallSide_one_eq_proj`, `wallSide_zero_eq_proj`);
* the outer blend saturates on the walls `0`, `1` by the strict triangle inequalities
  `|v₁ - x| > |v₁| - x` (`foldBlend_lt_of_wallZero`, `foldBlend_gt_of_wallOne`) and on the
  boundary circles of the corner discs (`foldBlend_gt_of_cornerOne`, `foldBlend_lt_of_cornerTwo`).
The lens arc and the switch windows lie in the core (`lensArc_mem_core`,
`switchWindow_mem_core`), so outside the core the wall-2 coordinate is below `lensWidth` or above
`switchTop`.
-/

set_option autoImplicit false

noncomputable section

open Complex Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

theorem discAngle_sector {w : ℂ} {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ Real.pi / 2)
    (hpos : 0 < ‖w‖ + w.re) (h1 : 0 ≤ w.im) (h2 : 0 ≤ -(exp (-((θ : ℂ) * I)) * w).im) :
    0 ≤ discAngle w ∧ discAngle w ≤ θ ∧ (0 < w.im → 0 < discAngle w) ∧
      (0 < -(exp (-((θ : ℂ) * I)) * w).im → discAngle w < θ) ∧
      (w.im = 0 → discAngle w = 0) ∧
      (-(exp (-((θ : ℂ) * I)) * w).im = 0 → discAngle w = θ) := by
  have hw0 := EuclidShape.ne_zero_of_norm_add_re_pos hpos
  have hS : 0 < ‖w‖ := norm_pos_iff.2 hw0
  have hm : discAngle w ∈ Set.Ioo (-Real.pi) Real.pi := halfArg_mem _ _ _
  have hp := halfArg_polar_self hw0 hpos
  set φ := discAngle w with hφ
  have him : w.im = ‖w‖ * Real.sin φ := by
    conv_lhs => rw [hp]
    rw [im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  have him2 : -(exp (-((θ : ℂ) * I)) * w).im = ‖w‖ * Real.sin (θ - φ) := by
    conv_lhs => rw [hp]
    rw [show exp (-((θ : ℂ) * I)) * ((‖w‖ : ℂ) * exp ((φ : ℂ) * I)) =
        (‖w‖ : ℂ) * exp (((φ - θ : ℝ) : ℂ) * I) by
      rw [mul_left_comm, ← Complex.exp_add]
      push_cast
      ring_nf, im_ofReal_mul, Complex.exp_ofReal_mul_I_im,
      show θ - φ = -(φ - θ) by ring, Real.sin_neg]
    ring
  have hpi := Real.pi_pos
  have hφ0 : 0 ≤ φ := by
    by_contra h
    have := Real.sin_neg_of_neg_of_neg_pi_lt (not_le.1 h) hm.1
    nlinarith
  have hφθ : φ ≤ θ := by
    by_contra h
    have := Real.sin_neg_of_neg_of_neg_pi_lt (by linarith [not_le.1 h] : θ - φ < 0)
      (by linarith [hm.2])
    nlinarith
  refine ⟨hφ0, hφθ, fun h => ?_, fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rcases hφ0.lt_or_eq with h' | h'
    · exact h'
    · rw [him, ← h', Real.sin_zero, mul_zero] at h
      exact absurd h (lt_irrefl 0)
  · rcases hφθ.lt_or_eq with h' | h'
    · exact h'
    · rw [him2, h', sub_self, Real.sin_zero, mul_zero] at h
      exact absurd h (lt_irrefl 0)
  · by_contra hne
    have hlt : 0 < φ := lt_of_le_of_ne hφ0 (Ne.symm hne)
    have := Real.sin_pos_of_pos_of_lt_pi hlt (by linarith)
    rw [him] at h
    nlinarith
  · by_contra hne
    have hlt : 0 < θ - φ := by
      rcases hφθ.lt_or_eq with h' | h'
      · linarith
      · exact absurd h'.symm (Ne.symm hne)
    have := Real.sin_pos_of_pos_of_lt_pi hlt (by linarith)
    rw [him2] at h
    nlinarith

namespace EuclidShape

variable (σ : EuclidShape)

theorem wallSide_one_eq_proj (z : ℂ) :
    σ.wallSide 1 z = Real.sin σ.θ₁ * (Real.sin σ.θ₃ - (σ.rotTwo z).re) -
      Real.cos σ.θ₁ * σ.wallSide 2 z := by
  have h := σ.rotTwo_eq_rotOne z
  have e : σ.rotOne z = exp ((σ.θ₁ : ℂ) * I) * ((Real.sin σ.θ₃ : ℂ) - σ.rotTwo z) := by
    have e2 : (Real.sin σ.θ₃ : ℂ) - (-(exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z) +
        (Real.sin σ.θ₃ : ℂ)) = exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z := by ring
    rw [h, e2, ← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
  rw [wallSide_one_eq_im_rotOne, e]
  change _ = _ - _ * (σ.rotTwo z).im
  simp only [mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, sub_re, sub_im,
    ofReal_re, ofReal_im]
  ring

theorem wallSide_zero_eq_proj (z : ℂ) :
    σ.wallSide 0 z = Real.sin σ.θ₂ * (σ.rotTwo z).re - Real.cos σ.θ₂ * σ.wallSide 2 z := by
  rw [wallSide_zero_eq_rotTwo, show -((σ.θ₂ : ℂ) * I) = ((-σ.θ₂ : ℝ) : ℂ) * I by push_cast; ring]
  change _ = _ - _ * (σ.rotTwo z).im
  simp only [mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_neg,
    Real.sin_neg]
  ring

theorem norm_pos_add_re {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) : 0 < ‖z‖ + z.re := by
  have := (σ.re_mem hz).1
  have := norm_pos_iff.2 h0
  linarith

theorem discAngle_mem {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) :
    0 ≤ discAngle z ∧ discAngle z ≤ σ.θ₃ ∧ (0 < σ.wallSide 0 z → 0 < discAngle z) ∧
      (0 < σ.wallSide 1 z → discAngle z < σ.θ₃) ∧ (σ.wallSide 0 z = 0 → discAngle z = 0) ∧
      (σ.wallSide 1 z = 0 → discAngle z = σ.θ₃) := by
  have h1 := hz 1
  rw [wallSide_one_eq_rotThree] at h1 ⊢
  exact discAngle_sector σ.θ₃_pos σ.θ₃_le (σ.norm_pos_add_re hz h0) (hz 0) h1

theorem psiOne_mem {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) (h1 : z ≠ σ.vertexOne) :
    0 ≤ σ.psiOne z ∧ σ.psiOne z ≤ σ.θ₁ := by
  have hd := σ.psiOne_pos_of_domOne (σ.triangle_subset_domOne hz h0 h1)
  have a := hz 1
  have b := hz 2
  rw [wallSide_one_eq_im_rotOne] at a
  rw [wallSide_two_eq_rotOne] at b
  obtain ⟨c, d, -⟩ := discAngle_sector σ.θ₁_pos σ.θ₁_le hd a b
  exact ⟨c, d⟩

theorem psiTwo_mem {z : ℂ} (hz : z ∈ σ.triangle) (h1 : z ≠ σ.vertexOne)
    (h2 : z ≠ σ.vertexTwo) : 0 ≤ σ.psiTwo z ∧ σ.psiTwo z ≤ σ.θ₂ := by
  have hd := σ.psiTwo_pos_of_domTwo (σ.triangle_subset_domTwo hz h1 h2)
  have a := hz 2
  have b := hz 0
  rw [wallSide_zero_eq_rotTwo] at b
  obtain ⟨c, d, -⟩ := discAngle_sector σ.θ₂_pos σ.θ₂_le hd a b
  exact ⟨c, d⟩


theorem switchTop_pos : 0 < σ.switchTop := by
  unfold switchTop
  linarith [σ.inradius_pos]

theorem hlam_one {z : ℂ} (hz : z ∈ σ.triangle) (hd : σ.switchTop < ‖z - σ.vertexOne‖) :
    (σ.rotTwo z).re - Real.sin σ.θ₃ < 0 ∨ σ.switchTop < σ.wallSide 2 z ∨
      σ.wallSide 2 z < σ.lensWidth := by
  have h1 := hz 1
  have h2 := hz 2
  rw [σ.wallSide_one_eq_proj] at h1
  have hs := σ.sin_θ₁_pos
  have hc := σ.cos_θ₁_nonneg
  have hP : 0 ≤ Real.sin σ.θ₃ - (σ.rotTwo z).re := by
    by_contra hneg
    have := mul_neg_of_pos_of_neg hs (not_le.1 hneg)
    nlinarith [mul_nonneg hc h2]
  rcases hP.lt_or_eq with hP | hP
  · left
    linarith
  · right
    left
    have hn := σ.norm_sq_sub_vertexOne z
    rw [← hP] at hn
    have hst := σ.switchTop_pos
    nlinarith [norm_nonneg (z - σ.vertexOne)]

theorem hlam_two {z : ℂ} (hz : z ∈ σ.triangle) (hd : σ.switchTop < ‖z - σ.vertexTwo‖) :
    0 < (σ.rotTwo z).re ∨ σ.switchTop < σ.wallSide 2 z ∨ σ.wallSide 2 z < σ.lensWidth := by
  have h0 := hz 0
  have h2 := hz 2
  rw [σ.wallSide_zero_eq_proj] at h0
  have hs := σ.sin_θ₂_pos
  have hc := σ.cos_θ₂_nonneg
  have hP : 0 ≤ (σ.rotTwo z).re := by
    by_contra hneg
    have := mul_neg_of_pos_of_neg hs (not_le.1 hneg)
    nlinarith [mul_nonneg hc h2]
  rcases hP.lt_or_eq with hP | hP
  · exact Or.inl hP
  · right
    left
    have hn := σ.norm_sq_sub_vertexTwo z
    rw [← hP] at hn
    have hst := σ.switchTop_pos
    nlinarith [norm_nonneg (z - σ.vertexTwo)]

theorem modOne_le_of {z : ℂ} (h : ‖z - σ.vertexOne‖ ≤ σ.radOne) : σ.modOne z ≤ 3 / 2 := by
  rw [modOne_eq]
  unfold profileSlope
  linarith

theorem modTwo_le_of {z : ℂ} (h : ‖z - σ.vertexTwo‖ ≤ σ.radTwo) : σ.modTwo z ≤ 3 / 2 := by
  rw [modTwo_eq]
  unfold profileSlope
  linarith

theorem three_halves_lt_re_bridgeOne {z : ℂ} (hz : z ∈ σ.triangle)
    (h : ‖z - σ.vertexOne‖ ≤ σ.radOne) : 3 / 2 < (σ.bridgeOne z).re := by
  have hA := σ.modThree_mem hz
  have hB := σ.modOne_mem hz
  have hle := σ.modOne_le_of h
  rw [bridgeOne, twoCircle_re]
  have e : (0 : ℝ) + (σ.modThree z ^ 2 - σ.modOne z ^ 2 + (3 / 2 - 0) ^ 2) / (2 * (3 / 2 - 0)) =
      (σ.modThree z ^ 2 - σ.modOne z ^ 2 + 9 / 4) / 3 := by ring
  rw [e, lt_div_iff₀ (by norm_num)]
  nlinarith

theorem re_bridgeZero_lt {z : ℂ} (hz : z ∈ σ.triangle)
    (h : ‖z - σ.vertexTwo‖ ≤ σ.radTwo) : (σ.bridgeZero z).re < -(3 / 2) := by
  have hA := σ.modThree_mem hz
  have hB := σ.modTwo_mem hz
  have hle := σ.modTwo_le_of h
  rw [bridgeZero, twoCircle_re]
  have e : (0 : ℝ) + (σ.modThree z ^ 2 - σ.modTwo z ^ 2 + (-(3 / 2) - 0) ^ 2) /
      (2 * (-(3 / 2) - 0)) = -((σ.modThree z ^ 2 - σ.modTwo z ^ 2 + 9 / 4) / 3) := by ring
  rw [e, neg_lt_neg_iff, lt_div_iff₀ (by norm_num)]
  nlinarith

theorem re_bridgeTwo_mem {z : ℂ} (hz : z ∈ σ.triangle) :
    -(3 / 2) < (σ.bridgeTwo z).re ∧ (σ.bridgeTwo z).re < 3 / 2 := by
  have hA := σ.modOne_mem hz
  have hB := σ.modTwo_mem hz
  rw [bridgeTwo, twoCircle_re]
  have e : (3 / 2 : ℝ) + (σ.modOne z ^ 2 - σ.modTwo z ^ 2 + (-(3 / 2) - 3 / 2) ^ 2) /
      (2 * (-(3 / 2) - 3 / 2)) = (σ.modTwo z ^ 2 - σ.modOne z ^ 2) / 6 := by ring
  rw [e]
  constructor
  · rw [lt_div_iff₀ (by norm_num)]
    nlinarith
  · rw [div_lt_iff₀ (by norm_num)]
    nlinarith

theorem cornerShrink_pos : 0 < σ.cornerShrink := by
  unfold cornerShrink
  linarith [σ.inradius_pos]

theorem cornerShrink_lt_inradius : σ.cornerShrink < σ.inradius := by
  unfold cornerShrink
  linarith [σ.inradius_pos]

theorem im_pos_of_cornerOne {z : ℂ} (hz : z ∈ σ.triangle)
    (h : ‖z - σ.vertexOne‖ ≤ σ.radOne) : 0 < z.im := by
  rcases (hz 0).lt_or_eq with h0 | h0
  · exact h0
  · exfalso
    have hi := Complex.abs_im_le_norm (z - σ.vertexOne)
    rw [sub_im, vertexOne_im', ← wallSide_zero_apply, ← h0, zero_sub, abs_neg,
      abs_of_pos (mul_pos σ.sin_θ₂_pos σ.sin_θ₃_pos)] at hi
    linarith [σ.radOne_lt_altitude]

theorem wallSide_one_vertexTwo' : σ.wallSide 1 σ.vertexTwo = Real.sin σ.θ₁ * Real.sin σ.θ₃ := by
  rw [wallSide_one_apply, vertexTwo_re', vertexTwo_im']
  ring

theorem abs_wallSide_one_sub_le (z w : ℂ) : |σ.wallSide 1 z - σ.wallSide 1 w| ≤ ‖z - w‖ := by
  change |(exp ((σ.θ₃ : ℂ) * I) * conj z).im - (exp ((σ.θ₃ : ℂ) * I) * conj w).im| ≤ _
  rw [← sub_im, ← mul_sub, ← map_sub]
  refine le_trans (Complex.abs_im_le_norm _) ?_
  rw [norm_mul, norm_exp_mul_I, one_mul, Complex.norm_conj]

theorem wallSide_one_pos_of_cornerTwo {z : ℂ} (hz : z ∈ σ.triangle)
    (h : ‖z - σ.vertexTwo‖ ≤ σ.radTwo) : 0 < σ.wallSide 1 z := by
  rcases (hz 1).lt_or_eq with h0 | h0
  · exact h0
  · exfalso
    have hi := σ.abs_wallSide_one_sub_le z σ.vertexTwo
    rw [← h0, zero_sub, abs_neg, σ.wallSide_one_vertexTwo',
      abs_of_pos (mul_pos σ.sin_θ₁_pos σ.sin_θ₃_pos)] at hi
    linarith [σ.radTwo_lt_altitude]

theorem foldBlend_eq (z : ℂ) : σ.foldBlend z = (2 * discAngle z / σ.θ₃ - 1) +
    (σ.canon 1 z - σ.canon 0 z) / σ.cornerShrink := by
  unfold foldBlend blendThree
  ring

theorem foldBlend_gt_of_cornerOne {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (hd : ‖z - σ.vertexOne‖ = σ.radOne - σ.cornerShrink) : 1 < σ.foldBlend z := by
  have hδ := σ.cornerShrink_pos
  have him := σ.im_pos_of_cornerOne hz (by linarith)
  have hψ := (σ.discAngle_mem hz h0).2.2.1 him
  have hθ := σ.θ₃_pos
  have ht := σ.triangle_vertexOne_vertexTwo z
  have hs := σ.radOne_add_radTwo
  have hq : 2 ≤ (σ.canon 1 z - σ.canon 0 z) / σ.cornerShrink := by
    rw [le_div_iff₀ hδ]
    simp only [canon]
    linarith
  have : 0 < 2 * discAngle z / σ.θ₃ := by positivity
  rw [foldBlend_eq]
  linarith

theorem foldBlend_lt_of_cornerTwo {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (hd : ‖z - σ.vertexTwo‖ = σ.radTwo - σ.cornerShrink) : σ.foldBlend z < -1 := by
  have hδ := σ.cornerShrink_pos
  have hw := σ.wallSide_one_pos_of_cornerTwo hz (by linarith)
  have hψ := (σ.discAngle_mem hz h0).2.2.2.1 hw
  have hθ := σ.θ₃_pos
  have ht := σ.triangle_vertexOne_vertexTwo z
  have hs := σ.radOne_add_radTwo
  have hq : (σ.canon 1 z - σ.canon 0 z) / σ.cornerShrink ≤ -2 := by
    rw [div_le_iff₀ hδ]
    simp only [canon]
    linarith
  have : 2 * discAngle z / σ.θ₃ < 2 := by
    rw [div_lt_iff₀ hθ]
    linarith
  rw [foldBlend_eq]
  linarith

theorem cos_θ₃_lt_one : Real.cos σ.θ₃ < 1 := cos_lt_one_aux σ.θ₃_pos σ.θ₃_le

theorem foldBlend_lt_of_wallZero {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (hw : σ.wallSide 0 z = 0) : σ.foldBlend z < -1 := by
  have hδ := σ.cornerShrink_pos
  have hψ := (σ.discAngle_mem hz h0).2.2.2.2.1 hw
  have hy : z.im = 0 := hw
  obtain ⟨hx0, hx1⟩ := σ.re_mem hz
  have hx : 0 < z.re := by
    rcases hx0.lt_or_eq with h | h
    · exact h
    · exact absurd (Complex.ext h.symm hy) h0
  have hc := σ.cos_θ₃_lt_one
  have hs2 := σ.sin_θ₂_pos
  have hcs := Real.sin_sq_add_cos_sq σ.θ₃
  have h2 : ‖z - σ.vertexTwo‖ = Real.sin σ.θ₁ - z.re := by
    rw [← pow_left_inj₀ (norm_nonneg _) (by linarith) two_ne_zero,
      EuclidShape.normSq_eq_sq_norm, sub_re, sub_im, vertexTwo_re', vertexTwo_im', hy]
    ring
  have h1 : ‖z - σ.vertexOne‖ ^ 2 - (Real.sin σ.θ₂ - z.re) ^ 2 =
      2 * z.re * Real.sin σ.θ₂ * (1 - Real.cos σ.θ₃) := by
    rw [EuclidShape.normSq_eq_sq_norm, sub_re, sub_im, vertexOne_re', vertexOne_im', hy]
    linear_combination Real.sin σ.θ₂ ^ 2 * hcs
  have hpos : 0 < 2 * z.re * Real.sin σ.θ₂ * (1 - Real.cos σ.θ₃) := by
    have : 0 < 1 - Real.cos σ.θ₃ := by linarith
    positivity
  have hd1 : Real.sin σ.θ₂ - z.re < ‖z - σ.vertexOne‖ := by
    nlinarith [norm_nonneg (z - σ.vertexOne)]
  have hr : σ.radOne - σ.radTwo = Real.sin σ.θ₂ - Real.sin σ.θ₁ := by
    unfold radOne radTwo
    ring
  have hq : (σ.canon 1 z - σ.canon 0 z) / σ.cornerShrink < 0 := by
    apply div_neg_of_neg_of_pos _ hδ
    simp only [canon]
    linarith
  rw [foldBlend_eq, hψ, mul_zero, zero_div]
  linarith

theorem foldBlend_gt_of_wallOne {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (hw : σ.wallSide 1 z = 0) : 1 < σ.foldBlend z := by
  have hδ := σ.cornerShrink_pos
  have hψ := (σ.discAngle_mem hz h0).2.2.2.2.2 hw
  have hθ := σ.θ₃_pos
  have hw' : Real.sin σ.θ₃ * z.re - Real.cos σ.θ₃ * z.im = 0 := by
    rw [← hw, wallSide_one_apply]
  set t := Real.cos σ.θ₃ * z.re + Real.sin σ.θ₃ * z.im with htdef
  have hcs := Real.sin_sq_add_cos_sq σ.θ₃
  have hxr : z.re = Real.cos σ.θ₃ * t := by
    rw [htdef]
    linear_combination Real.sin σ.θ₃ * hw' - z.re * hcs
  have hyr : z.im = Real.sin σ.θ₃ * t := by
    rw [htdef]
    linear_combination (-(Real.cos σ.θ₃)) * hw' - z.im * hcs
  have hte : (exp (-((σ.θ₃ : ℂ) * I)) * z).re = t := by
    rw [htdef, show -((σ.θ₃ : ℂ) * I) = ((-σ.θ₃ : ℝ) : ℂ) * I by push_cast; ring]
    simp only [mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, Real.cos_neg,
      Real.sin_neg]
    ring
  obtain ⟨ht0, ht1⟩ := σ.re_rotThree_mem hz
  rw [hte] at ht0 ht1
  have htp : 0 < t := by
    rcases ht0.lt_or_eq with h | h
    · exact h
    · exfalso
      apply h0
      apply Complex.ext
      · rw [hxr, ← h, mul_zero, zero_re]
      · rw [hyr, ← h, mul_zero, zero_im]
  have hc := σ.cos_θ₃_lt_one
  have hs1 := σ.sin_θ₁_pos
  have h1 : ‖z - σ.vertexOne‖ = Real.sin σ.θ₂ - t := by
    rw [← pow_left_inj₀ (norm_nonneg _) (by linarith) two_ne_zero,
      EuclidShape.normSq_eq_sq_norm, sub_re, sub_im, vertexOne_re', vertexOne_im', hxr, hyr]
    linear_combination (t - Real.sin σ.θ₂) ^ 2 * hcs
  have h2 : ‖z - σ.vertexTwo‖ ^ 2 - (Real.sin σ.θ₁ - t) ^ 2 =
      2 * t * Real.sin σ.θ₁ * (1 - Real.cos σ.θ₃) := by
    rw [EuclidShape.normSq_eq_sq_norm, sub_re, sub_im, vertexTwo_re', vertexTwo_im', hxr, hyr]
    linear_combination t ^ 2 * hcs
  have hpos : 0 < 2 * t * Real.sin σ.θ₁ * (1 - Real.cos σ.θ₃) := by
    have : 0 < 1 - Real.cos σ.θ₃ := by linarith
    positivity
  have hd2 : Real.sin σ.θ₁ - t < ‖z - σ.vertexTwo‖ := by
    nlinarith [norm_nonneg (z - σ.vertexTwo)]
  have hr : σ.radOne - σ.radTwo = Real.sin σ.θ₂ - Real.sin σ.θ₁ := by
    unfold radOne radTwo
    ring
  have hq : 0 < (σ.canon 1 z - σ.canon 0 z) / σ.cornerShrink := by
    apply div_pos _ hδ
    simp only [canon]
    linarith
  rw [foldBlend_eq, hψ, mul_div_assoc, div_self hθ.ne']
  linarith


theorem ne_of_norm_pos {z v : ℂ} {r : ℝ} (hr : 0 < r) (h : r ≤ ‖z - v‖) : z ≠ v := by
  rintro rfl
  rw [sub_self, norm_zero] at h
  linarith

theorem mem_goodSet {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (hc : σ.coreRadius - σ.coreMargin ≤ ‖z - σ.incenter‖) : z ∈ σ.goodSet := by
  obtain ⟨hρ, hgb, hbb, hb1, hb2, -, hog, -, -, -, hlt, hδ, hg, hor3, hβ⟩ := σ.params
  have hst : σ.switchTop < σ.germRadius := by
    unfold switchTop germRadius
    linarith
  have ht := σ.triangle_vertexOne_vertexTwo z
  have hs12 := σ.radOne_add_radTwo
  by_cases a1 : ‖z - σ.vertexOne‖ < σ.germRadius
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl a1)))))))
  by_cases a2 : ‖z - σ.vertexTwo‖ < σ.germRadius
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr a2)))))))
  by_cases o : ‖z‖ < σ.outerGermRadius
  · exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨norm_pos_iff.2 h0, o⟩))))))
  rw [not_lt] at a1 a2 o
  have h1 : z ≠ σ.vertexOne := ne_of_norm_pos hg a1
  have h2 : z ≠ σ.vertexTwo := ne_of_norm_pos hg a2
  have d1 := σ.triangle_subset_domOne hz h0 h1
  have d0 := σ.triangle_subset_domZero hz h0 h2
  have d2 := σ.triangle_subset_domTwo hz h1 h2
  have hB2 := σ.re_bridgeTwo_mem hz
  by_cases c1 : ‖z - σ.vertexOne‖ < σ.radOne - σ.cornerShrink
  · refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨by linarith, c1⟩, d1, d2,
      σ.three_halves_lt_re_bridgeOne hz (by linarith), hB2.2,
      σ.hlam_one hz (by linarith)⟩)))))
  by_cases c2 : ‖z - σ.vertexTwo‖ < σ.radTwo - σ.cornerShrink
  · refine Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨by linarith, c2⟩, d2, d0, hB2.1,
      σ.re_bridgeZero_lt hz (by linarith), σ.hlam_two hz (by linarith)⟩))))
  rw [not_lt] at c1 c2
  have hw2 := hz 2
  by_cases l : σ.wallSide 2 z < σ.lensWidth
  · refine Or.inl (Or.inl (Or.inl (Or.inr ⟨⟨by linarith, by linarith, ?_⟩, d2, hB2.1, hB2.2⟩)))
    rwa [abs_of_nonneg hw2]
  rw [not_lt] at l
  have hw : σ.switchTop < σ.wallSide 2 z := by
    by_contra hle
    have := σ.switchWindow_mem_core hz l (not_lt.1 hle) c1 c2
    linarith
  by_cases j1 : ‖z - σ.vertexOne‖ = σ.radOne - σ.cornerShrink
  · have hn := σ.norm_ge_of_vertexOne z
    have h13 := σ.radOne_add_radThree
    refine Or.inl (Or.inr ⟨⟨by linarith, by linarith, hw, by linarith,
      σ.foldBlend_gt_of_cornerOne hz h0 j1⟩, d1, σ.norm_pos_add_re hz h0,
      σ.three_halves_lt_re_bridgeOne hz (by linarith)⟩)
  by_cases j2 : ‖z - σ.vertexTwo‖ = σ.radTwo - σ.cornerShrink
  · have hn := σ.norm_ge_of_vertexTwo z
    have h23 := σ.radTwo_add_radThree
    refine Or.inr ⟨⟨by linarith, by linarith, hw, by linarith,
      σ.foldBlend_lt_of_cornerTwo hz h0 j2⟩, d0, σ.re_bridgeZero_lt hz (by linarith)⟩
  have e1 : σ.radOne - σ.cornerShrink < ‖z - σ.vertexOne‖ := lt_of_le_of_ne c1 (Ne.symm j1)
  have e2 : σ.radTwo - σ.cornerShrink < ‖z - σ.vertexTwo‖ := lt_of_le_of_ne c2 (Ne.symm j2)
  have hside : (0 < σ.wallSide 0 z ∧ 0 < σ.wallSide 1 z) ∨ 1 < σ.foldBlend z ∨
      σ.foldBlend z < -1 := by
    rcases (hz 0).lt_or_eq with p0 | p0
    · rcases (hz 1).lt_or_eq with p1 | p1
      · exact Or.inl ⟨p0, p1⟩
      · exact Or.inr (Or.inl (σ.foldBlend_gt_of_wallOne hz h0 p1.symm))
    · exact Or.inr (Or.inr (σ.foldBlend_lt_of_wallZero hz h0 p0.symm))
  refine Or.inl (Or.inl (Or.inr ⟨⟨e1, e2, ?_, by linarith⟩, d1, d0, σ.re_bridgeOne_pos hz,
    σ.re_bridgeZero_neg hz, hside⟩))
  rw [abs_of_nonneg hw2]
  linarith

end EuclidShape

end GC.Seifert
