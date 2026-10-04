import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldEuclidInjective

/-!
# Image bounds and wall neighbourhoods of the flat compact fold

Lane CF, tier 3, curvature `0` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §5–§7, with review 23 §6.1). On the triangle minus
`v₃ = 0` the map `preFold` has `Im ≥ 0` (`im_preFold_nonneg`), `Im > 0` at interior points
(`im_preFold_pos`) and modulus `< 7/2` (`norm_preFold_lt`): every branch is `c + S e^{iΘ}` with
`c` real, `S ≥ 0` and `Θ ∈ [0, π]`, strictly inside where all three side functions are positive.

Wall neighbourhoods (review 23 §6.1: reflection-stable open neighbourhoods): for each wall `i`
an open set `wallNbhd i = W ∩ (refl i)⁻¹ W` where `W` is cut out by strict inequalities that hold
on the whole wall minus `v₃` (`wall_mem_W*`) — a strip `|wᵢ| < δ` around the wall, membership in
`goodSet`, the saturation of the weights that are not reflection invariant (lens switch `= 1`
near walls 0, 1 off the germ discs, the outer weight `ν = 0` resp. `1` by the strict triangle
inequalities, the lens switch `= 0` in the strip of wall 2) and the angle ranges needed by the
corner reflection lemmas. On `wallNbhd i` both `z` and `refl i z` take the same branch of
`preFold`, whose formula is equivariant, so `preFold (refl i z) = conj (preFold z)`
(`preFold_refl_zero`, `preFold_refl_one`, `preFold_refl_two`).
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Set
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

theorem im_real_add_polar (c S Θ : ℝ) :
    (((c : ℝ) : ℂ) + (S : ℂ) * exp ((Θ : ℂ) * I)).im = S * Real.sin Θ := by
  rw [add_im, ofReal_im, zero_add, im_ofReal_mul, Complex.exp_ofReal_mul_I_im]

theorem angle_open_combo {τ x y : ℝ} (h0 : 0 ≤ τ) (h1 : τ ≤ 1) (hx : 0 < x ∧ x < Real.pi)
    (hy : 0 < y ∧ y < Real.pi) :
    0 < (1 - τ) * x + τ * y ∧ (1 - τ) * x + τ * y < Real.pi := by
  have a := mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 (min_le_left x y))
  have b := mul_nonneg h0 (sub_nonneg.2 (min_le_right x y))
  have c := mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 (le_max_left x y))
  have d := mul_nonneg h0 (sub_nonneg.2 (le_max_right x y))
  have hm := lt_min hx.1 hy.1
  have hM := max_lt hx.2 hy.2
  constructor <;> nlinarith

namespace EuclidShape

variable (σ : EuclidShape)

theorem ne_of_interior {z : ℂ} (hpos : ∀ i, 0 < σ.wallSide i z) :
    z ≠ 0 ∧ z ≠ σ.vertexOne ∧ z ≠ σ.vertexTwo := by
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl
  · have := hpos 0
    rw [σ.wallSide_zero_zero] at this
    exact lt_irrefl 0 this
  · have := hpos 2
    rw [σ.wallSide_two_vertexOne] at this
    exact lt_irrefl 0 this
  · have := hpos 2
    rw [σ.wallSide_two_vertexTwo] at this
    exact lt_irrefl 0 this

theorem angleCornerOne_mem_open {z : ℂ} (hz : z ∈ σ.triangle) (hpos : ∀ i, 0 < σ.wallSide i z)
    (hd : ‖z - σ.vertexOne‖ ≤ σ.radOne) :
    0 < σ.angleCornerOne σ.blendStart σ.blendEnd σ.lensWidth σ.switchTop z ∧
      σ.angleCornerOne σ.blendStart σ.blendEnd σ.lensWidth σ.switchTop z < Real.pi := by
  obtain ⟨h0, h1, h2⟩ := σ.ne_of_interior hpos
  obtain ⟨d1, d2, hψ, hp1, hp2, -⟩ := σ.validOne_of hz h0 h1 h2 hd
  have a1 := halfArg_mem_Ico hp1 (σ.im_bridgeOne_nonneg hz)
  have a1' := halfArg_pos hp1 (σ.im_bridgeOne_pos d1 (hpos 1))
  have a2 := negHalfArg_mem_Ioc hp2 (σ.im_bridgeTwo_nonneg hz)
  have a2' := negHalfArg_lt_pi hp2 (σ.im_bridgeTwo_pos d2 (hpos 2))
  have w1 := hpos 1
  have w2 := hpos 2
  rw [wallSide_one_eq_im_rotOne] at w1
  rw [wallSide_two_eq_rotOne] at w2
  obtain ⟨-, -, s1, s2, -⟩ := discAngle_sector σ.θ₁_pos σ.θ₁_le hψ w1.le w2.le
  have hψ0 := s1 w1
  have hψ1 := s2 w2
  have hp : (0 : ℝ) < σ.p₁ := by exact_mod_cast σ.one_le_p₁
  have hm : (σ.p₁ : ℝ) * σ.psiOne z < Real.pi := by
    rw [← σ.θ₁_mul, mul_comm σ.θ₁]
    exact mul_lt_mul_of_pos_left hψ1 hp
  have hs0 := coneStep_nonneg σ.lensWidth σ.switchTop (σ.wallSide 2 z)
  have hs1 := coneStep_le_one σ.lensWidth σ.switchTop (σ.wallSide 2 z)
  have hin : 0 < σ.lensSwitch σ.lensWidth σ.switchTop z * σ.angleOneAtOne z +
      (1 - σ.lensSwitch σ.lensWidth σ.switchTop z) * σ.angleTwoAtOne z ∧
      σ.lensSwitch σ.lensWidth σ.switchTop z * σ.angleOneAtOne z +
      (1 - σ.lensSwitch σ.lensWidth σ.switchTop z) * σ.angleTwoAtOne z < Real.pi := by
    have e := angle_open_combo (τ := 1 - σ.lensSwitch σ.lensWidth σ.switchTop z)
      (x := σ.angleOneAtOne z) (y := σ.angleTwoAtOne z) (by unfold lensSwitch; linarith)
      (by unfold lensSwitch; linarith) ⟨a1', a1.2⟩ ⟨a2.1, a2'⟩
    rw [sub_sub_cancel] at e
    exact e
  exact angle_open_combo (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _)
    ⟨mul_pos hp hψ0, hm⟩ hin

theorem angleCornerTwo_mem_open {z : ℂ} (hz : z ∈ σ.triangle) (hpos : ∀ i, 0 < σ.wallSide i z)
    (hd : ‖z - σ.vertexTwo‖ ≤ σ.radTwo) :
    0 < σ.angleCornerTwo σ.blendStart σ.blendEnd σ.lensWidth σ.switchTop z ∧
      σ.angleCornerTwo σ.blendStart σ.blendEnd σ.lensWidth σ.switchTop z < Real.pi := by
  obtain ⟨h0, h1, h2⟩ := σ.ne_of_interior hpos
  obtain ⟨d2, d0, hψ, hp2, hp0, -⟩ := σ.validTwo_of hz h0 h1 h2 hd
  have a2 := halfArg_mem_Ico hp2 (σ.im_bridgeTwo_nonneg hz)
  have a2' := halfArg_pos hp2 (σ.im_bridgeTwo_pos d2 (hpos 2))
  have a0 := negHalfArg_mem_Ioc hp0 (σ.im_bridgeZero_nonneg hz)
  have a0' := negHalfArg_lt_pi hp0 (σ.im_bridgeZero_pos d0 (hpos 0))
  have w2 := hpos 2
  have w0 := hpos 0
  rw [wallSide_zero_eq_rotTwo] at w0
  obtain ⟨-, -, s1, s2, -⟩ := discAngle_sector σ.θ₂_pos σ.θ₂_le hψ w2.le w0.le
  have hψ0 := s1 w2
  have hψ1 := s2 w0
  have hp : (0 : ℝ) < σ.p₂ := by exact_mod_cast σ.one_le_p₂
  have hm : (σ.p₂ : ℝ) * σ.psiTwo z < Real.pi := by
    rw [← σ.θ₂_mul, mul_comm σ.θ₂]
    exact mul_lt_mul_of_pos_left hψ1 hp
  exact angle_open_combo (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _)
    ⟨mul_pos hp hψ0, hm⟩ (angle_open_combo (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _)
      ⟨a2', a2.2⟩ ⟨a0.1, a0'⟩)

theorem angleCornerThree_mem_open {z : ℂ} (hz : z ∈ σ.triangle)
    (hpos : ∀ i, 0 < σ.wallSide i z) :
    0 < σ.angleCornerThree σ.outerBlendStart σ.outerBlendEnd 1 σ.cornerShrink z ∧
      σ.angleCornerThree σ.outerBlendStart σ.outerBlendEnd 1 σ.cornerShrink z < Real.pi := by
  obtain ⟨h0, h1, h2⟩ := σ.ne_of_interior hpos
  have d1 := σ.triangle_subset_domOne hz h0 h1
  have d0 := σ.triangle_subset_domZero hz h0 h2
  have hM := σ.modThree_pos d1.2.2
  have hp1 : 0 < σ.modThree z + (σ.bridgeOne z).re := by linarith [σ.re_bridgeOne_pos hz]
  have hp0 : 0 < σ.modThree z - (σ.bridgeZero z).re := by linarith [σ.re_bridgeZero_neg hz]
  have a1 := halfArg_mem_Ico hp1 (σ.im_bridgeOne_nonneg hz)
  have a1' := halfArg_pos hp1 (σ.im_bridgeOne_pos d1 (hpos 1))
  have a0 := negHalfArg_mem_Ioc hp0 (σ.im_bridgeZero_nonneg hz)
  have a0' := negHalfArg_lt_pi hp0 (σ.im_bridgeZero_pos d0 (hpos 0))
  have hψ := σ.discAngle_mem hz h0
  have hψ0 := hψ.2.2.1 (hpos 0)
  have hψ1 := hψ.2.2.2.1 (hpos 1)
  have hp : (0 : ℝ) < σ.p₃ := by exact_mod_cast σ.one_le_p₃
  have hm : (σ.p₃ : ℝ) * discAngle z < Real.pi := by
    rw [← σ.θ₃_mul, mul_comm σ.θ₃]
    exact mul_lt_mul_of_pos_left hψ1 hp
  exact angle_open_combo (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _)
    ⟨by linarith, by linarith [mul_pos hp hψ0]⟩
    (angle_open_combo (coneStep_nonneg _ _ _) (coneStep_le_one _ _ _) ⟨a0.1, a0'⟩ ⟨a1', a1.2⟩)

theorem im_preFold_pos {z : ℂ} (hz : z ∈ σ.triangle) (hpos : ∀ i, 0 < σ.wallSide i z) :
    0 < (σ.preFold z).im := by
  obtain ⟨h0, h1, h2⟩ := σ.ne_of_interior hpos
  rcases σ.mem_regions hz h0 with a | a | a | a
  · have hd : 0 < ‖z - σ.vertexOne‖ := norm_pos_iff.2 (sub_ne_zero.2 h1)
    rw [σ.preFold_regionOne a, foldCornerOne, cornerOne, im_real_add_polar]
    have hΘ := σ.angleCornerOne_mem_open hz hpos (by linarith [a.2, σ.cornerShrink_pos])
    exact mul_pos (innerRadial_pos σ.radOne_lt_one hd)
      (Real.sin_pos_of_pos_of_lt_pi hΘ.1 hΘ.2)
  · have hd : 0 < ‖z - σ.vertexTwo‖ := norm_pos_iff.2 (sub_ne_zero.2 h2)
    rw [σ.preFold_regionTwo a, foldCornerTwo, cornerTwo, im_real_add_polar]
    have hΘ := σ.angleCornerTwo_mem_open hz hpos (by linarith [a.2, σ.cornerShrink_pos])
    exact mul_pos (innerRadial_pos σ.radTwo_lt_one hd)
      (Real.sin_pos_of_pos_of_lt_pi hΘ.1 hΘ.2)
  · rw [σ.preFold_regionLens a]
    exact σ.im_bridgeTwo_pos (σ.triangle_subset_domTwo hz h1 h2) (hpos 2)
  · rw [σ.preFold_regionThree a, foldCornerThree, cornerThree, im_real_add_polar]
    have hΘ := σ.angleCornerThree_mem_open hz hpos
    exact mul_pos (by linarith [σ.outerRadial_gt hz]) (Real.sin_pos_of_pos_of_lt_pi hΘ.1 hΘ.2)

theorem im_preFold_nonneg {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) :
    0 ≤ (σ.preFold z).im := by
  rcases σ.mem_regions hz h0 with a | a | a | a
  · rw [σ.preFold_regionOne a, foldCornerOne, cornerOne, im_real_add_polar]
    by_cases h1 : z = σ.vertexOne
    · rw [h1, sub_self, norm_zero, innerRadial_zero σ.one_le_p₁ σ.blendStart_nonneg
        σ.params.2.2.1, zero_mul]
    have hΘ := σ.angleCornerOne_mem hz h0 h1 (σ.ne_vertexTwo_of_regionOne a)
      (by linarith [a.2, σ.cornerShrink_pos])
    exact mul_nonneg (σ.innerOne_nonneg (norm_nonneg _))
      (Real.sin_nonneg_of_nonneg_of_le_pi hΘ.1 hΘ.2)
  · rw [σ.preFold_regionTwo a, foldCornerTwo, cornerTwo, im_real_add_polar]
    by_cases h2 : z = σ.vertexTwo
    · rw [h2, sub_self, norm_zero, innerRadial_zero σ.one_le_p₂ σ.blendStart_nonneg
        σ.params.2.2.1, zero_mul]
    have hΘ := σ.angleCornerTwo_mem hz h0 (σ.ne_vertexOne_of_regionTwo a) h2
      (by linarith [a.2, σ.cornerShrink_pos])
    exact mul_nonneg (σ.innerTwo_nonneg (norm_nonneg _))
      (Real.sin_nonneg_of_nonneg_of_le_pi hΘ.1 hΘ.2)
  · rw [σ.preFold_regionLens a]
    exact σ.im_bridgeTwo_nonneg hz
  · obtain ⟨-, -, h1, h2⟩ := σ.facts_regionThree a
    rw [σ.preFold_regionThree a, foldCornerThree, cornerThree, im_real_add_polar]
    have hΘ := σ.angleCornerThree_mem hz h0 h1 h2
    exact mul_nonneg (by linarith [σ.outerRadial_gt hz])
      (Real.sin_nonneg_of_nonneg_of_le_pi hΘ.1 hΘ.2)

theorem outerRadial_lt {z : ℂ} (h0 : z ≠ 0) :
    outerRadial σ.p₃ σ.outerBlendStart σ.outerBlendEnd σ.radThree ‖z‖ < 7 / 2 := by
  have hd := norm_pos_iff.2 h0
  have hτ0 := coneStep_nonneg σ.outerBlendStart σ.outerBlendEnd ‖z‖
  have hτ1 := coneStep_le_one σ.outerBlendStart σ.outerBlendEnd ‖z‖
  have hA : 0 < ‖z‖ ^ σ.p₃ := by positivity
  have hB : 3 - profileSlope * (‖z‖ - σ.radThree) < 7 / 2 := by
    unfold profileSlope
    linarith [σ.radThree_lt_one]
  unfold outerRadial
  nlinarith [mul_nonneg hτ0 (by linarith : (0 : ℝ) ≤ 7 / 2 - (3 - profileSlope * (‖z‖ -
    σ.radThree))), mul_nonneg (by linarith : (0 : ℝ) ≤ 1 - coneStep σ.outerBlendStart
      σ.outerBlendEnd ‖z‖) hA.le]

theorem norm_preFold_lt {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0) :
    ‖σ.preFold z‖ < 7 / 2 := by
  have hk := σ.kappa_delta_pos
  have n32 : ‖(3 / 2 : ℂ)‖ = 3 / 2 := by
    rw [three_halves_cast, Complex.norm_real, Real.norm_eq_abs]
    norm_num
  rcases σ.mem_regions hz h0 with a | a | a | a
  · have := σ.image_regionOne a
    have t := norm_le_norm_sub_add (σ.preFold z) (3 / 2)
    rw [n32] at t
    linarith
  · have := σ.image_regionTwo a
    have t := norm_add_le (σ.preFold z + 3 / 2) (-(3 / 2))
    have e : σ.preFold z + 3 / 2 + -(3 / 2) = σ.preFold z := by ring
    rw [e, norm_neg, n32] at t
    linarith
  · linarith [(σ.image_regionLens a).2.2]
  · rw [σ.norm_preFold_regionThree a]
    exact σ.outerRadial_lt h0


theorem half_le_sin_aux {p : ℕ} (h2 : 2 ≤ p) (h6 : p ≤ 6) : 1 / 2 ≤ Real.sin (Real.pi / p) := by
  have hp : (0 : ℝ) < p := by have := p_pos_aux h2; linarith
  have h1 : Real.pi / 6 ≤ Real.pi / p :=
    div_le_div_of_nonneg_left Real.pi_pos.le hp (by exact_mod_cast h6)
  rw [← Real.sin_pi_div_six]
  exact Real.sin_le_sin_of_le_of_le_pi_div_two (by linarith [Real.pi_pos]) (θ_le_aux h2) h1

theorem p_le_six : σ.p₁ ≤ 6 ∧ σ.p₂ ≤ 6 ∧ σ.p₃ ≤ 6 := by
  have e := σ.orders_nat_eq
  have h1 := σ.two_le_p₁
  have h2 := σ.two_le_p₂
  have h3 := σ.two_le_p₃
  exact ⟨order_le_six h2 h3 e, order_le_six h1 h3 (by linarith [e]),
    order_le_six h1 h2 (by linarith [e])⟩

theorem half_le_sin_θ₁ : 1 / 2 ≤ Real.sin σ.θ₁ := half_le_sin_aux σ.two_le_p₁ σ.p_le_six.1

theorem half_le_sin_θ₂ : 1 / 2 ≤ Real.sin σ.θ₂ := half_le_sin_aux σ.two_le_p₂ σ.p_le_six.2.1

theorem wallSide_two_of_wallZero {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 0 z = 0) :
    σ.wallSide 2 z = Real.sin σ.θ₂ * ‖z - σ.vertexTwo‖ := by
  have h0 := σ.wallSide_zero_eq_proj z
  rw [hw] at h0
  have hn := σ.norm_sq_sub_vertexTwo z
  have hX := σ.proj_two_nonneg hz
  have hW := hz 2
  have hs := σ.sin_θ₂_pos
  have hcs := Real.sin_sq_add_cos_sq σ.θ₂
  have key : σ.wallSide 2 z ^ 2 = (Real.sin σ.θ₂ * ‖z - σ.vertexTwo‖) ^ 2 := by
    have e : Real.sin σ.θ₂ * (σ.rotTwo z).re = Real.cos σ.θ₂ * σ.wallSide 2 z := by linarith
    have e2 : Real.sin σ.θ₂ ^ 2 * (σ.rotTwo z).re ^ 2 =
        Real.cos σ.θ₂ ^ 2 * σ.wallSide 2 z ^ 2 := by
      rw [← mul_pow, ← mul_pow, e]
    rw [mul_pow, hn]
    linear_combination (-1 : ℝ) * e2 - σ.wallSide 2 z ^ 2 * hcs
  exact (pow_left_inj₀ hW (by positivity) two_ne_zero).1 key

theorem wallSide_two_of_wallOne {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 1 z = 0) :
    σ.wallSide 2 z = Real.sin σ.θ₁ * ‖z - σ.vertexOne‖ := by
  have h1 := σ.wallSide_one_eq_proj z
  rw [hw] at h1
  have hn := σ.norm_sq_sub_vertexOne z
  have hW := hz 2
  have hs := σ.sin_θ₁_pos
  have hcs := Real.sin_sq_add_cos_sq σ.θ₁
  have key : σ.wallSide 2 z ^ 2 = (Real.sin σ.θ₁ * ‖z - σ.vertexOne‖) ^ 2 := by
    have e : Real.sin σ.θ₁ * (Real.sin σ.θ₃ - (σ.rotTwo z).re) =
        Real.cos σ.θ₁ * σ.wallSide 2 z := by linarith
    have e2 : Real.sin σ.θ₁ ^ 2 * (Real.sin σ.θ₃ - (σ.rotTwo z).re) ^ 2 =
        Real.cos σ.θ₁ ^ 2 * σ.wallSide 2 z ^ 2 := by
      rw [← mul_pow, ← mul_pow, e]
    rw [mul_pow, hn]
    linear_combination (-1 : ℝ) * e2 - σ.wallSide 2 z ^ 2 * hcs
  exact (pow_left_inj₀ hW (by positivity) two_ne_zero).1 key

theorem dist_one_of_strip_zero {z : ℂ} (h : |z.im| < σ.cornerShrink) :
    σ.radOne - σ.cornerShrink < ‖z - σ.vertexOne‖ := by
  have hi := Complex.abs_im_le_norm (z - σ.vertexOne)
  rw [sub_im, vertexOne_im'] at hi
  have := σ.radOne_lt_altitude
  rw [abs_lt] at h
  have := (abs_le.1 hi).1
  linarith

theorem dist_two_of_strip_one {z : ℂ} (h : |σ.wallSide 1 z| < σ.cornerShrink) :
    σ.radTwo - σ.cornerShrink < ‖z - σ.vertexTwo‖ := by
  have hi := σ.abs_wallSide_one_sub_le z σ.vertexTwo
  rw [σ.wallSide_one_vertexTwo'] at hi
  have := σ.radTwo_lt_altitude
  rw [abs_lt] at h
  have := (abs_le.1 hi).1
  linarith

theorem norm_of_strip_two {z : ℂ} (h : |σ.wallSide 2 z| < σ.cornerShrink) :
    σ.outerGermRadius < ‖z‖ := by
  have hl := σ.abs_wallSide_two_sub_le z 0
  rw [sub_zero] at hl
  have h0 : σ.wallSide 2 0 = Real.sin σ.θ₁ * Real.sin σ.θ₂ := by
    rw [wallSide_two_apply]
    simp
  rw [h0] at hl
  have ha := σ.two_inradius_lt_altitudeThree
  have hρ := σ.inradius_pos
  rw [abs_lt] at h
  rw [abs_le] at hl
  unfold outerGermRadius
  unfold cornerShrink at h
  linarith [hl.1]

theorem core_lt_of_wallSide {z : ℂ} {i : Fin 3}
    (hlip : |σ.wallSide i z - σ.wallSide i σ.incenter| ≤ ‖z - σ.incenter‖)
    (hI : σ.wallSide i σ.incenter = σ.inradius) (h : |σ.wallSide i z| < σ.cornerShrink) :
    σ.coreRadius + σ.coreMargin < ‖z - σ.incenter‖ := by
  rw [hI] at hlip
  have hρ := σ.inradius_pos
  rw [abs_lt] at h
  have := (abs_le.1 hlip).1
  unfold coreRadius coreMargin
  unfold cornerShrink at h
  linarith

theorem core_lt_of_strip_zero {z : ℂ} (h : |σ.wallSide 0 z| < σ.cornerShrink) :
    σ.coreRadius + σ.coreMargin < ‖z - σ.incenter‖ := by
  refine σ.core_lt_of_wallSide ?_ σ.wallSide_zero_incenter h
  change |z.im - σ.incenter.im| ≤ _
  rw [← sub_im]
  exact Complex.abs_im_le_norm _

theorem core_lt_of_strip_one {z : ℂ} (h : |σ.wallSide 1 z| < σ.cornerShrink) :
    σ.coreRadius + σ.coreMargin < ‖z - σ.incenter‖ :=
  σ.core_lt_of_wallSide (σ.abs_wallSide_one_sub_le z _) σ.wallSide_one_incenter h

theorem core_lt_of_strip_two {z : ℂ} (h : |σ.wallSide 2 z| < σ.cornerShrink) :
    σ.coreRadius + σ.coreMargin < ‖z - σ.incenter‖ :=
  σ.core_lt_of_wallSide (σ.abs_wallSide_two_sub_le z _) σ.wallSide_two_incenter h

theorem continuousAt_foldBlend' {z : ℂ} (hψ : 0 < ‖z‖ + z.re) :
    ContinuousAt σ.foldBlend z := by
  have h1 : ContinuousAt (fun u : ℂ => discAngle u) z := (contDiffAt_psiThree hψ).continuousAt
  have h2 : Continuous fun u : ℂ => σ.canon 1 u - σ.canon 0 u := by
    change Continuous fun u : ℂ => (‖u - σ.vertexTwo‖ - σ.radTwo) - (‖u - σ.vertexOne‖ - σ.radOne)
    fun_prop
  have e : σ.foldBlend = fun u => (2 * discAngle u / σ.θ₃ - 1) +
      (σ.canon 1 u - σ.canon 0 u) / σ.cornerShrink := funext σ.foldBlend_eq
  rw [e]
  exact (((continuousAt_const.mul h1).div_const _).sub continuousAt_const).add
    (h2.continuousAt.div_const _)

theorem germ_lt_radOne_sub : σ.germRadius < σ.radOne - σ.cornerShrink := by
  have hp := σ.params
  linarith [hp.2.1, hp.2.2.1, hp.2.2.2.1]

theorem germ_lt_radTwo_sub : σ.germRadius < σ.radTwo - σ.cornerShrink := by
  have hp := σ.params
  linarith [hp.2.1, hp.2.2.1, hp.2.2.2.2.1]

theorem blendStart_lt_radTwo_sub : σ.blendStart < σ.radTwo - σ.cornerShrink := by
  have hp := σ.params
  linarith [hp.2.2.1, hp.2.2.2.2.1]

theorem blendStart_lt_radOne_sub : σ.blendStart < σ.radOne - σ.cornerShrink := by
  have hp := σ.params
  linarith [hp.2.2.1, hp.2.2.2.1]

theorem switchTop_lt_quarter : σ.switchTop < σ.inradius / 4 := by
  unfold switchTop
  linarith [σ.inradius_pos]

theorem lensWidth_lt_switchTop : σ.lensWidth < σ.switchTop := σ.params.2.2.2.2.2.2.2.2.2.2.1

theorem cornerShrink_lt_lensWidth : σ.cornerShrink < σ.lensWidth := by
  unfold cornerShrink lensWidth
  linarith [σ.inradius_pos]

theorem switch_of_blendStart_le {d s : ℝ} (hs : 1 / 2 ≤ s) (hd : σ.blendStart ≤ d) :
    σ.switchTop < s * d := by
  have := σ.switchTop_lt_quarter
  have hρ := σ.inradius_pos
  unfold blendStart at hd
  nlinarith

def wallSetZero : Set ℂ :=
  {z | |z.im| < σ.cornerShrink ∧ 0 < ‖z‖ + z.re ∧ z ∈ σ.goodSet ∧
    (‖z - σ.vertexTwo‖ < σ.blendStart ∨ σ.switchTop < σ.wallSide 2 z) ∧ σ.foldBlend z < -1 ∧
    (‖z - σ.vertexTwo‖ < σ.germRadius ∨ (0 < ‖σ.rotTwo z‖ + (σ.rotTwo z).re ∧
      -Real.pi < 2 * σ.θ₂ - σ.psiTwo z ∧ 2 * σ.θ₂ - σ.psiTwo z < Real.pi))}

def wallNbhdZero : Set ℂ := σ.wallSetZero ∩ σ.refl 0 ⁻¹' σ.wallSetZero

theorem contAt_psiTwo' {z : ℂ} (h : 0 < ‖σ.rotTwo z‖ + (σ.rotTwo z).re) :
    ContinuousAt (fun u => 2 * σ.θ₂ - σ.psiTwo u) z :=
  continuousAt_const.sub (σ.contDiffAt_psiTwo h).continuousAt

theorem contAt_psiOne' {z : ℂ} (h : 0 < ‖σ.rotOne z‖ + (σ.rotOne z).re) :
    ContinuousAt (fun u => 2 * σ.θ₁ - σ.psiOne u) z :=
  continuousAt_const.sub (σ.contDiffAt_psiOne h).continuousAt

theorem contAt_normRotTwo (z : ℂ) :
    ContinuousAt (fun u => ‖σ.rotTwo u‖ + (σ.rotTwo u).re) z :=
  (σ.continuous_rotTwo.norm.add (Complex.continuous_re.comp σ.continuous_rotTwo)).continuousAt

theorem contAt_normRotOne (z : ℂ) :
    ContinuousAt (fun u => ‖σ.rotOne u‖ + (σ.rotOne u).re) z :=
  (σ.contDiff_rotOne.continuous.norm.add
    (Complex.continuous_re.comp σ.contDiff_rotOne.continuous)).continuousAt

theorem isOpen_wallSetZero : IsOpen σ.wallSetZero := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := hz
  have e4 : ∀ᶠ u in 𝓝 z, ‖u - σ.vertexTwo‖ < σ.blendStart ∨ σ.switchTop < σ.wallSide 2 u := by
    rcases a4 with h | h
    · exact (ev_gt (contAt_dist _ z) h).mono fun u hu => Or.inl hu
    · exact (ev_lt (σ.contAt_wallSide 2 z) h).mono fun u hu => Or.inr hu
  have e6 : ∀ᶠ u in 𝓝 z, ‖u - σ.vertexTwo‖ < σ.germRadius ∨ (0 < ‖σ.rotTwo u‖ +
      (σ.rotTwo u).re ∧ -Real.pi < 2 * σ.θ₂ - σ.psiTwo u ∧ 2 * σ.θ₂ - σ.psiTwo u < Real.pi) := by
    rcases a6 with h | ⟨h1, h2, h3⟩
    · exact (ev_gt (contAt_dist _ z) h).mono fun u hu => Or.inl hu
    · filter_upwards [ev_lt (σ.contAt_normRotTwo z) h1, ev_lt (σ.contAt_psiTwo' h1) h2,
        ev_gt (σ.contAt_psiTwo' h1) h3] with u b1 b2 b3
      exact Or.inr ⟨b1, b2, b3⟩
  filter_upwards [ev_gt (continuous_abs.comp Complex.continuous_im).continuousAt a1,
    ev_lt (contAt_normAddRe z) a2, σ.isOpen_goodSet.mem_nhds a3, e4,
    ev_gt (σ.continuousAt_foldBlend' a2) a5, e6] with u b1 b2 b3 b4 b5 b6
  exact ⟨b1, b2, b3, b4, b5, b6⟩

theorem isOpen_wallNbhdZero : IsOpen σ.wallNbhdZero :=
  σ.isOpen_wallSetZero.inter (σ.isOpen_wallSetZero.preimage (by
    change Continuous fun z : ℂ => conj z
    exact Complex.continuous_conj))

theorem wall_mem_wallSetZero {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (hw : σ.wallSide 0 z = 0) : z ∈ σ.wallSetZero := by
  have hδ := σ.cornerShrink_pos
  have him : z.im = 0 := hw
  have h1 : z ≠ σ.vertexOne := by
    rintro rfl
    rw [wallSide_zero_apply, vertexOne_im'] at hw
    exact (mul_pos σ.sin_θ₂_pos σ.sin_θ₃_pos).ne' hw
  have hc : σ.coreRadius - σ.coreMargin ≤ ‖z - σ.incenter‖ := by
    have := σ.core_lt_of_strip_zero (by rw [hw, abs_zero]; exact hδ)
    unfold coreMargin at *
    linarith [σ.inradius_pos]
  refine ⟨by rw [him, abs_zero]; exact hδ, σ.norm_pos_add_re hz h0, σ.mem_goodSet hz h0 hc, ?_,
    σ.foldBlend_lt_of_wallZero hz h0 hw, ?_⟩
  · rcases lt_or_ge ‖z - σ.vertexTwo‖ σ.blendStart with h | h
    · exact Or.inl h
    · right
      rw [σ.wallSide_two_of_wallZero hz hw]
      exact σ.switch_of_blendStart_le σ.half_le_sin_θ₂ h
  · rcases lt_or_ge ‖z - σ.vertexTwo‖ σ.germRadius with h | h
    · exact Or.inl h
    · right
      have h2 : z ≠ σ.vertexTwo := ne_of_norm_pos σ.params.2.2.2.2.2.2.2.2.2.2.2.2.1 h
      have hψ := σ.psiTwo_pos_of_domTwo (σ.triangle_subset_domTwo hz h1 h2)
      have a := hz 2
      have b : 0 ≤ -(exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z).im := by
        rw [← wallSide_zero_eq_rotTwo]; exact hz 0
      have e := (discAngle_sector σ.θ₂_pos σ.θ₂_le hψ a b).2.2.2.2.2
        (by rw [← wallSide_zero_eq_rotTwo]; exact hw)
      change 0 < ‖σ.rotTwo z‖ + (σ.rotTwo z).re ∧ -Real.pi < 2 * σ.θ₂ - discAngle (σ.rotTwo z) ∧
        2 * σ.θ₂ - discAngle (σ.rotTwo z) < Real.pi
      rw [e]
      exact ⟨hψ, by linarith [σ.θ₂_pos, Real.pi_pos], by linarith [σ.θ₂_le, Real.pi_pos]⟩

theorem wall_mem_wallNbhdZero {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (hw : σ.wallSide 0 z = 0) : z ∈ σ.wallNbhdZero := by
  have hm := σ.wall_mem_wallSetZero hz h0 hw
  refine ⟨hm, ?_⟩
  change σ.refl 0 z ∈ σ.wallSetZero
  rw [σ.refl_of_wallSide_eq_zero hw]
  exact hm

theorem refl_mapsTo_wallNbhdZero : MapsTo (σ.refl 0) σ.wallNbhdZero σ.wallNbhdZero := by
  intro z hz
  refine ⟨hz.2, ?_⟩
  change σ.refl 0 (σ.refl 0 z) ∈ σ.wallSetZero
  rw [σ.refl_refl]
  exact hz.1

theorem lensSwitch_eq_one {z : ℂ} (h : σ.switchTop < σ.wallSide 2 z) :
    σ.lensSwitch σ.lensWidth σ.switchTop z = 1 :=
  coneStep_eq_one σ.lensWidth_lt_switchTop h.le

theorem lensSwitch_eq_zero {z : ℂ} (h : |σ.wallSide 2 z| < σ.cornerShrink) :
    σ.lensSwitch σ.lensWidth σ.switchTop z = 0 :=
  coneStep_eq_zero σ.lensWidth_lt_switchTop
    (by linarith [le_abs_self (σ.wallSide 2 z), σ.cornerShrink_lt_lensWidth])

theorem not_lens_of {z : ℂ} {d r : ℝ} (hr : σ.blendStart < r) (hd : ¬ d < r)
    (h : d < σ.blendStart ∨ σ.switchTop < σ.wallSide 2 z) :
    ¬ |σ.wallSide 2 z| < σ.lensWidth := by
  rcases h with h | h
  · exact absurd (h.trans hr) hd
  · intro hl
    linarith [le_abs_self (σ.wallSide 2 z), σ.lensWidth_lt_switchTop]

theorem switch_cases {z z' : ℂ} {d : ℝ} (h : d < σ.blendStart ∨ σ.switchTop < σ.wallSide 2 z)
    (h' : d < σ.blendStart ∨ σ.switchTop < σ.wallSide 2 z') :
    coneStep σ.blendStart σ.blendEnd d = 0 ∨
      (σ.lensSwitch σ.lensWidth σ.switchTop z = 1 ∧
        σ.lensSwitch σ.lensWidth σ.switchTop z' = 1) := by
  rcases h with h | h
  · exact Or.inl (coneStep_eq_zero σ.params.2.2.1 h.le)
  rcases h' with h' | h'
  · exact Or.inl (coneStep_eq_zero σ.params.2.2.1 h'.le)
  exact Or.inr ⟨σ.lensSwitch_eq_one h, σ.lensSwitch_eq_one h'⟩

theorem preFold_refl_zero {z : ℂ} (hz : z ∈ σ.wallNbhdZero) :
    σ.preFold (σ.refl 0 z) = conj (σ.preFold z) := by
  obtain ⟨⟨a1, -, -, a4, a5, a6⟩, ⟨b1, -, -, b4, b5, -⟩⟩ := hz
  have n2 : ‖σ.refl 0 z - σ.vertexTwo‖ = ‖z - σ.vertexTwo‖ :=
    σ.norm_refl_sub 0 z _ σ.wallSide_zero_vertexTwo
  have n0 : ‖σ.refl 0 z‖ = ‖z‖ := Complex.norm_conj z
  rw [n2] at b4
  have f1 := not_lt.2 (σ.dist_one_of_strip_zero a1).le
  have f1' := not_lt.2 (σ.dist_one_of_strip_zero b1).le
  have g1 : ¬ ‖z - σ.vertexOne‖ < σ.germRadius := fun h => f1 (h.trans σ.germ_lt_radOne_sub)
  have g1' : ¬ ‖σ.refl 0 z - σ.vertexOne‖ < σ.germRadius := fun h =>
    f1' (h.trans σ.germ_lt_radOne_sub)
  simp only [preFold, g1, g1', f1, f1', n2, n0, ite_false]
  by_cases c2 : ‖z - σ.vertexTwo‖ < σ.germRadius
  · simp only [c2, ite_true]
    exact σ.apexTwo_refl_zero z
  simp only [c2, ite_false]
  by_cases c3 : ‖z‖ < σ.outerGermRadius
  · simp only [c3, ite_true]
    exact σ.outerGerm_refl_zero z
  simp only [c3, ite_false]
  by_cases c5 : ‖z - σ.vertexTwo‖ < σ.radTwo - σ.cornerShrink
  · simp only [c5, ite_true]
    obtain ⟨hψ, h1, h2⟩ := a6.resolve_left c2
    exact σ.cornerTwo_refl_zero _ _ _ _ hψ h1 h2 (σ.switch_cases a4 b4)
  simp only [c5, ite_false, σ.not_lens_of σ.blendStart_lt_radTwo_sub c5 a4,
    σ.not_lens_of σ.blendStart_lt_radTwo_sub c5 b4]
  exact σ.cornerThree_refl_zero _ _ _ _ (Or.inr ⟨coneStep_eq_zero (by norm_num) a5.le,
    coneStep_eq_zero (by norm_num) b5.le⟩)

def wallSetOne : Set ℂ :=
  {z | |σ.wallSide 1 z| < σ.cornerShrink ∧ 0 < ‖z‖ + z.re ∧ z ∈ σ.goodSet ∧
    (‖z - σ.vertexOne‖ < σ.blendStart ∨ σ.switchTop < σ.wallSide 2 z) ∧ 1 < σ.foldBlend z ∧
    -Real.pi < 2 * σ.θ₃ - discAngle z ∧ 2 * σ.θ₃ - discAngle z < Real.pi}

def wallNbhdOne : Set ℂ := σ.wallSetOne ∩ σ.refl 1 ⁻¹' σ.wallSetOne

theorem continuous_refl_one : Continuous (σ.refl 1) := by
  change Continuous fun z : ℂ => exp (2 * (σ.θ₃ : ℂ) * I) * conj z
  exact continuous_const.mul Complex.continuous_conj

theorem continuous_refl_two : Continuous (σ.refl 2) := by
  change Continuous fun z : ℂ =>
    σ.vertexTwo + exp (-(2 * (σ.θ₂ : ℂ) * I)) * conj (z - σ.vertexTwo)
  exact continuous_const.add (continuous_const.mul
    (Complex.continuous_conj.comp (continuous_id.sub continuous_const)))

theorem isOpen_wallSetOne : IsOpen σ.wallSetOne := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hz
  have e4 : ∀ᶠ u in 𝓝 z, ‖u - σ.vertexOne‖ < σ.blendStart ∨ σ.switchTop < σ.wallSide 2 u := by
    rcases a4 with h | h
    · exact (ev_gt (contAt_dist _ z) h).mono fun u hu => Or.inl hu
    · exact (ev_lt (σ.contAt_wallSide 2 z) h).mono fun u hu => Or.inr hu
  have hd : ContinuousAt (fun u : ℂ => 2 * σ.θ₃ - discAngle u) z :=
    continuousAt_const.sub (contDiffAt_psiThree a2).continuousAt
  filter_upwards [ev_gt (continuous_abs.comp (σ.contDiff_wallSide 1).continuous).continuousAt a1,
    ev_lt (contAt_normAddRe z) a2, σ.isOpen_goodSet.mem_nhds a3, e4,
    ev_lt (σ.continuousAt_foldBlend' a2) a5, ev_lt hd a6, ev_gt hd a7] with u b1 b2 b3 b4 b5 b6 b7
  exact ⟨b1, b2, b3, b4, b5, b6, b7⟩

theorem isOpen_wallNbhdOne : IsOpen σ.wallNbhdOne :=
  σ.isOpen_wallSetOne.inter (σ.isOpen_wallSetOne.preimage σ.continuous_refl_one)

theorem wall_mem_wallSetOne {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (hw : σ.wallSide 1 z = 0) : z ∈ σ.wallSetOne := by
  have hδ := σ.cornerShrink_pos
  have hc : σ.coreRadius - σ.coreMargin ≤ ‖z - σ.incenter‖ := by
    have := σ.core_lt_of_strip_one (by rw [hw, abs_zero]; exact hδ)
    unfold coreMargin at *
    linarith [σ.inradius_pos]
  have ht : discAngle z = σ.θ₃ := (σ.discAngle_mem hz h0).2.2.2.2.2 hw
  refine ⟨by rw [hw, abs_zero]; exact hδ, σ.norm_pos_add_re hz h0, σ.mem_goodSet hz h0 hc, ?_,
    σ.foldBlend_gt_of_wallOne hz h0 hw, ?_, ?_⟩
  · rcases lt_or_ge ‖z - σ.vertexOne‖ σ.blendStart with h | h
    · exact Or.inl h
    · right
      rw [σ.wallSide_two_of_wallOne hz hw]
      exact σ.switch_of_blendStart_le σ.half_le_sin_θ₁ h
  · rw [ht]
    linarith [σ.θ₃_pos, Real.pi_pos]
  · rw [ht]
    linarith [σ.θ₃_le, Real.pi_pos]

theorem wall_mem_wallNbhdOne {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (hw : σ.wallSide 1 z = 0) : z ∈ σ.wallNbhdOne := by
  have hm := σ.wall_mem_wallSetOne hz h0 hw
  refine ⟨hm, ?_⟩
  change σ.refl 1 z ∈ σ.wallSetOne
  rw [σ.refl_of_wallSide_eq_zero hw]
  exact hm

theorem refl_mapsTo_wallNbhdOne : MapsTo (σ.refl 1) σ.wallNbhdOne σ.wallNbhdOne := by
  intro z hz
  refine ⟨hz.2, ?_⟩
  change σ.refl 1 (σ.refl 1 z) ∈ σ.wallSetOne
  rw [σ.refl_refl]
  exact hz.1

theorem preFold_refl_one {z : ℂ} (hz : z ∈ σ.wallNbhdOne) :
    σ.preFold (σ.refl 1 z) = conj (σ.preFold z) := by
  obtain ⟨⟨a1, a2, -, a4, a5, a6, a7⟩, ⟨b1, -, -, b4, b5, -, -⟩⟩ := hz
  have n1 : ‖σ.refl 1 z - σ.vertexOne‖ = ‖z - σ.vertexOne‖ :=
    σ.norm_refl_sub 1 z _ σ.wallSide_one_vertexOne
  have n0 : ‖σ.refl 1 z‖ = ‖z‖ := by
    have := σ.norm_refl_sub 1 z 0 σ.wallSide_one_zero
    rwa [sub_zero, sub_zero] at this
  rw [n1] at b4
  have f2 := not_lt.2 (σ.dist_two_of_strip_one a1).le
  have f2' := not_lt.2 (σ.dist_two_of_strip_one b1).le
  have g2 : ¬ ‖z - σ.vertexTwo‖ < σ.germRadius := fun h => f2 (h.trans σ.germ_lt_radTwo_sub)
  have g2' : ¬ ‖σ.refl 1 z - σ.vertexTwo‖ < σ.germRadius := fun h =>
    f2' (h.trans σ.germ_lt_radTwo_sub)
  simp only [preFold, g2, g2', f2, f2', n1, n0, ite_false]
  by_cases c1 : ‖z - σ.vertexOne‖ < σ.germRadius
  · simp only [c1, ite_true]
    exact σ.apexOne_refl_one z
  simp only [c1, ite_false]
  by_cases c3 : ‖z‖ < σ.outerGermRadius
  · simp only [c3, ite_true]
    exact σ.outerGerm_refl_one z
  simp only [c3, ite_false]
  by_cases c4 : ‖z - σ.vertexOne‖ < σ.radOne - σ.cornerShrink
  · simp only [c4, ite_true]
    exact σ.cornerOne_refl_one _ _ _ _ (σ.switch_cases a4 b4)
  simp only [c4, ite_false, σ.not_lens_of σ.blendStart_lt_radOne_sub c4 a4,
    σ.not_lens_of σ.blendStart_lt_radOne_sub c4 b4]
  exact σ.cornerThree_refl_one _ _ _ _ a2 a6 a7 (Or.inr ⟨coneStep_eq_one (by norm_num) a5.le,
    coneStep_eq_one (by norm_num) b5.le⟩)

def wallSetTwo : Set ℂ :=
  {z | |σ.wallSide 2 z| < σ.cornerShrink ∧ z ∈ σ.goodSet ∧
    (‖z - σ.vertexOne‖ < σ.germRadius ∨ (0 < ‖σ.rotOne z‖ + (σ.rotOne z).re ∧
      -Real.pi < 2 * σ.θ₁ - σ.psiOne z ∧ 2 * σ.θ₁ - σ.psiOne z < Real.pi))}

def wallNbhdTwo : Set ℂ := σ.wallSetTwo ∩ σ.refl 2 ⁻¹' σ.wallSetTwo

theorem isOpen_wallSetTwo : IsOpen σ.wallSetTwo := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨a1, a3, a6⟩ := hz
  have e6 : ∀ᶠ u in 𝓝 z, ‖u - σ.vertexOne‖ < σ.germRadius ∨ (0 < ‖σ.rotOne u‖ +
      (σ.rotOne u).re ∧ -Real.pi < 2 * σ.θ₁ - σ.psiOne u ∧ 2 * σ.θ₁ - σ.psiOne u < Real.pi) := by
    rcases a6 with h | ⟨h1, h2, h3⟩
    · exact (ev_gt (contAt_dist _ z) h).mono fun u hu => Or.inl hu
    · filter_upwards [ev_lt (σ.contAt_normRotOne z) h1, ev_lt (σ.contAt_psiOne' h1) h2,
        ev_gt (σ.contAt_psiOne' h1) h3] with u b1 b2 b3
      exact Or.inr ⟨b1, b2, b3⟩
  filter_upwards [ev_gt (σ.contAt_abs_wallSide z) a1, σ.isOpen_goodSet.mem_nhds a3, e6]
    with u b1 b3 b6
  exact ⟨b1, b3, b6⟩

theorem isOpen_wallNbhdTwo : IsOpen σ.wallNbhdTwo :=
  σ.isOpen_wallSetTwo.inter (σ.isOpen_wallSetTwo.preimage σ.continuous_refl_two)

theorem wall_mem_wallSetTwo {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (hw : σ.wallSide 2 z = 0) : z ∈ σ.wallSetTwo := by
  have hδ := σ.cornerShrink_pos
  have hc : σ.coreRadius - σ.coreMargin ≤ ‖z - σ.incenter‖ := by
    have := σ.core_lt_of_strip_two (by rw [hw, abs_zero]; exact hδ)
    unfold coreMargin at *
    linarith [σ.inradius_pos]
  refine ⟨by rw [hw, abs_zero]; exact hδ, σ.mem_goodSet hz h0 hc, ?_⟩
  rcases lt_or_ge ‖z - σ.vertexOne‖ σ.germRadius with h | h
  · exact Or.inl h
  · right
    have h1 : z ≠ σ.vertexOne := ne_of_norm_pos σ.params.2.2.2.2.2.2.2.2.2.2.2.2.1 h
    have hψ := σ.psiOne_pos_of_domOne (σ.triangle_subset_domOne hz h0 h1)
    have a := hz 1
    have b := hz 2
    rw [wallSide_one_eq_im_rotOne] at a
    rw [wallSide_two_eq_rotOne] at b
    have e := (discAngle_sector σ.θ₁_pos σ.θ₁_le hψ a b).2.2.2.2.2
      (by rw [← wallSide_two_eq_rotOne]; exact hw)
    change 0 < ‖σ.rotOne z‖ + (σ.rotOne z).re ∧ -Real.pi < 2 * σ.θ₁ - discAngle (σ.rotOne z) ∧
      2 * σ.θ₁ - discAngle (σ.rotOne z) < Real.pi
    rw [e]
    exact ⟨hψ, by linarith [σ.θ₁_pos, Real.pi_pos], by linarith [σ.θ₁_le, Real.pi_pos]⟩

theorem wall_mem_wallNbhdTwo {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (hw : σ.wallSide 2 z = 0) : z ∈ σ.wallNbhdTwo := by
  have hm := σ.wall_mem_wallSetTwo hz h0 hw
  refine ⟨hm, ?_⟩
  change σ.refl 2 z ∈ σ.wallSetTwo
  rw [σ.refl_of_wallSide_eq_zero hw]
  exact hm

theorem refl_mapsTo_wallNbhdTwo : MapsTo (σ.refl 2) σ.wallNbhdTwo σ.wallNbhdTwo := by
  intro z hz
  refine ⟨hz.2, ?_⟩
  change σ.refl 2 (σ.refl 2 z) ∈ σ.wallSetTwo
  rw [σ.refl_refl]
  exact hz.1

theorem preFold_refl_two {z : ℂ} (hz : z ∈ σ.wallNbhdTwo) :
    σ.preFold (σ.refl 2 z) = conj (σ.preFold z) := by
  obtain ⟨⟨a1, -, a6⟩, ⟨b1, -, -⟩⟩ := hz
  have n1 : ‖σ.refl 2 z - σ.vertexOne‖ = ‖z - σ.vertexOne‖ :=
    σ.norm_refl_sub 2 z _ σ.wallSide_two_vertexOne
  have n2 : ‖σ.refl 2 z - σ.vertexTwo‖ = ‖z - σ.vertexTwo‖ :=
    σ.norm_refl_sub 2 z _ σ.wallSide_two_vertexTwo
  have f3 := not_lt.2 (σ.norm_of_strip_two a1).le
  have f3' := not_lt.2 (σ.norm_of_strip_two b1).le
  have l : |σ.wallSide 2 z| < σ.lensWidth := a1.trans σ.cornerShrink_lt_lensWidth
  have l' : |σ.wallSide 2 (σ.refl 2 z)| < σ.lensWidth := b1.trans σ.cornerShrink_lt_lensWidth
  have s0 := σ.lensSwitch_eq_zero a1
  have s0' := σ.lensSwitch_eq_zero b1
  simp only [preFold, f3, f3', n1, n2, l, l', ite_false, ite_true]
  by_cases c1 : ‖z - σ.vertexOne‖ < σ.germRadius
  · simp only [c1, ite_true]
    exact σ.apexOne_refl_two z
  simp only [c1, ite_false]
  by_cases c2 : ‖z - σ.vertexTwo‖ < σ.germRadius
  · simp only [c2, ite_true]
    exact σ.apexTwo_refl_two z
  simp only [c2, ite_false]
  by_cases c4 : ‖z - σ.vertexOne‖ < σ.radOne - σ.cornerShrink
  · simp only [c4, ite_true]
    obtain ⟨hψ, h1, h2⟩ := a6.resolve_left c1
    exact σ.cornerOne_refl_two _ _ _ _ hψ h1 h2 (Or.inr ⟨s0, s0'⟩)
  simp only [c4, ite_false]
  by_cases c5 : ‖z - σ.vertexTwo‖ < σ.radTwo - σ.cornerShrink
  · simp only [c5, ite_true]
    exact σ.cornerTwo_refl_two _ _ _ _ (Or.inr ⟨s0, s0'⟩)
  simp only [c5, ite_false]
  exact σ.bridgeTwo_refl_two z

end EuclidShape

end GC.Seifert
