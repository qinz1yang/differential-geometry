import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldHypPreFold

/-!
# Wall neighbourhoods and wall identities of the hyperbolic compact fold

Lane CF-H3w, tier 3, curvature `-1` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §4–§7, review 23 §6.1: reflection-stable wall
neighbourhoods). Template: `CompactFoldEuclidWalls`.

**Germs.** The apex models `3/2 + rotOne^{p₁}/2`, `-3/2 + rotTwo^{p₂}/2` and the outer germ
`compactOuterGerm p₃` are equivariant under the two reflections through their vertex
(`hypApexOne_refl_one`, `hypApexOne_refl_two`, `hypApexTwo_refl_two`, `hypApexTwo_refl_zero`,
`hypOuterGerm_refl_zero`, `hypOuterGerm_refl_one`), because `e^{2iθⱼ pⱼ} = 1`.

**Selectors.** The lens coordinate is odd under the reflection in wall 2
(`lensCoord_refl_two`); the distances to the vertices of a wall are invariant under its reflection
(`hd_refl_*` of `CompactFoldHypBridges`); `‖·‖` is invariant under `refl 0`, `refl 1`.

**On the walls.** On wall `i` the canonical coordinates of its two vertices add up to zero, so by
the nonnegative sums of `CompactFoldHypBlend` the third one dominates: `|canon 1| ≤ canon 0` on
wall 0, `|canon 0| ≤ canon 1` on wall 1, `|canon 0| ≤ canon 2` on wall 2
(`canon_zero_ge_of_wallZero`, …), i.e. a wall stays outside the canonical disc of the opposite
vertex. Away from `v₃` the inequality is strict where it feeds the outer weight:
`blendThree < -w` on wall 0 and `> w` on wall 1 (`blendThree_lt_of_wallZero`,
`blendThree_gt_of_wallOne`). On walls 0 and 1 the lens coordinate is
`2 sin θⱼ ϖ/(1 - ϖ²)` with `ϖ` the pseudo-distance to the vertex of the wall other than `v₃`, so it
is at least `2 sin θⱼ ϖ` (`lensCoord_ge_of_wallZero`, `lensCoord_ge_of_wallOne`); on wall 2 it
vanishes. The rotated angles take their wall values there (`psiTwo_of_wallZero`,
`psiOne_of_wallTwo`, `discAngle_of_wallOne`, `discAngle_of_wallZero`).

**Neighbourhoods.** For an open `W` inside the disc, `reflNbhd i W = W ∩ (refl i)⁻¹ W` is open,
stable under `refl i`, inside the chart of `refl i`, and contains every point of `W` on wall `i`
(`isOpen_reflNbhd`, `refl_mapsTo_reflNbhd`, `reflNbhd_subset_reflChart`, `mem_reflNbhd_of_wall`).

**The wall stage of `hypPreFold`** (`CompactFoldHypPreFold`). The wall neighbourhood
`hypWallNbhd σ L i = reflNbhd i (hypWallSet* σ L)`, where `hypWallSet*` is cut out by strict
inequalities true on wall `i` minus `v₃` (`wall_mem_hypWallSet*`): the branches of the vertex
off the wall are excluded (`g < hd`, `-e < canon`, resp. `g₃ < ‖z‖`), the lens switch is
saturated where the radial weight is not zero (`hd < a ∨ 2β' < lensCoord`), the outer weight is
saturated (`blendThree < -1`, resp. `> 1`), the lens holds in the strip of wall 2
(`|lensCoord| < β/2`), and the rotated angles stay in the range of the corner reflection lemmas.
It is open, inside the punctured disc and the chart of `refl i`, stable under `refl i`, contains
`foldWall i \ {0}` (`isOpen_hypWallNbhd`, `hypWallNbhd_subset`, `hypWallNbhd_subset_reflChart`,
`refl_mapsTo_hypWallNbhd`, `foldWall_diff_subset_hypWallNbhd`), carries the separation conditions
used by the core (`hypWallNbhd_zero_subset`, `hypWallNbhd_one_subset`, `hypWallNbhd_two_subset`),
and on it `z` and `refl i z` take the same branch of `hypPreFold`, whose formula is equivariant:
`hypPreFold ∘ refl i = conj ∘ hypPreFold` (`hypPreFold_refl_zero`, `hypPreFold_refl_one`,
`hypPreFold_refl_two`, `hypPreFold_refl`).
-/

set_option autoImplicit false

noncomputable section

open Complex Filter Set
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace HypFold

theorem hypExp_two_pow_eq_one {θ : ℝ} {p : ℕ} (hθ : θ * p = Real.pi) :
    exp (2 * (θ : ℂ) * I) ^ p = 1 := by
  rw [← Complex.exp_nat_mul, show (p : ℂ) * (2 * (θ : ℂ) * I) = 2 * ((θ * p : ℝ) : ℂ) * I by
    push_cast; ring, hθ, Complex.exp_two_pi_mul_I]

theorem discAngle_eq_of_ray {θ : ℝ} (hθ0 : -Real.pi < θ) (hθ1 : θ < Real.pi) {w : ℂ}
    (hw : w ≠ 0) (him : (exp (-((θ : ℂ) * I)) * w).im = 0)
    (hre : 0 ≤ (exp (-((θ : ℂ) * I)) * w).re) : discAngle w = θ := by
  set u := exp (-((θ : ℂ) * I)) * w with hu
  have hu0 : u ≠ 0 := mul_ne_zero (Complex.exp_ne_zero _) hw
  have hpos : 0 < ‖u‖ + u.re := norm_add_re_pos_of_re hu0 hre
  have hw' : w = u * exp ((θ : ℂ) * I) := by
    rw [hu, mul_comm (exp _) w, mul_assoc, ← Complex.exp_add, neg_add_cancel, Complex.exp_zero,
      mul_one]
  have h0 : discAngle u = 0 := by
    rw [discAngle, him, halfArg_zero]
  rw [hw', discAngle_mul_exp hu0 hpos (by rw [h0]; linarith) (by rw [h0]; linarith), h0,
    zero_add]

variable {σ : CompactShape}

theorem norm_refl_zero' (z : ℂ) : ‖σ.refl 0 z‖ = ‖z‖ := Complex.norm_conj z

theorem norm_refl_one' (z : ℂ) : ‖σ.refl 1 z‖ = ‖z‖ := by
  change ‖exp (2 * (σ.θ₃ : ℂ) * I) * conj z‖ = ‖z‖
  rw [norm_mul, norm_exp_two, one_mul, Complex.norm_conj]

theorem hypOuterGerm_refl_zero (z : ℂ) :
    compactOuterGerm σ.p₃ (σ.refl 0 z) = conj (compactOuterGerm σ.p₃ z) :=
  compactOuterGerm_conj σ.p₃ z

theorem hypOuterGerm_refl_one (z : ℂ) :
    compactOuterGerm σ.p₃ (σ.refl 1 z) = conj (compactOuterGerm σ.p₃ z) := by
  rw [← compactOuterGerm_conj, compactOuterGerm, compactOuterGerm, norm_refl_one',
    Complex.norm_conj, Complex.conj_conj]
  change -(((7 / 2 - ‖z‖ ^ σ.p₃ / 2 : ℝ) : ℂ) * (conj (exp (2 * (σ.θ₃ : ℂ) * I) * conj z) /
    ‖z‖) ^ σ.p₃) = _
  have e : conj (exp (2 * (σ.θ₃ : ℂ) * I) * conj z) = exp (2 * ((-σ.θ₃ : ℝ) : ℂ) * I) * z := by
    rw [map_mul, Complex.conj_conj, ← Complex.exp_conj]
    congr 2
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    push_cast
    ring
  have hp : (-σ.θ₃) * (σ.p₃ : ℝ) = -Real.pi := by rw [neg_mul, θ₃_mul]
  have e1 : exp (2 * ((-σ.θ₃ : ℝ) : ℂ) * I) ^ σ.p₃ = 1 := by
    rw [← Complex.exp_nat_mul, show (σ.p₃ : ℂ) * (2 * ((-σ.θ₃ : ℝ) : ℂ) * I) =
      -(2 * ((σ.θ₃ * σ.p₃ : ℝ) : ℂ) * I) by push_cast; ring, θ₃_mul, Complex.exp_neg,
      Complex.exp_two_pi_mul_I, inv_one]
  rw [e, mul_div_assoc, mul_pow, e1, one_mul]

section Hyp

variable (h : σ.curv = .hyperbolic)
include h

theorem hypApexOne_refl_one (z : ℂ) :
    3 / 2 + σ.rotOne (σ.refl 1 z) ^ σ.p₁ / 2 = conj (3 / 2 + σ.rotOne z ^ σ.p₁ / 2) := by
  simp only [rotOne_refl_one h, map_add, map_div₀, map_pow, map_ofNat]

theorem hypApexOne_refl_two {z : ℂ} (hz : ‖z‖ < 1) :
    3 / 2 + σ.rotOne (σ.refl 2 z) ^ σ.p₁ / 2 = conj (3 / 2 + σ.rotOne z ^ σ.p₁ / 2) := by
  simp only [rotOne_refl_two h hz, mul_pow, hypExp_two_pow_eq_one (θ₁_mul σ), one_mul, map_add,
    map_div₀, map_pow, map_ofNat]

theorem hypApexTwo_refl_two {z : ℂ} (hz : ‖z‖ < 1) :
    -(3 / 2) + σ.rotTwo (σ.refl 2 z) ^ σ.p₂ / 2 = conj (-(3 / 2) + σ.rotTwo z ^ σ.p₂ / 2) := by
  simp only [rotTwo_refl_two h hz, map_add, map_div₀, map_pow, map_ofNat, map_neg]

theorem hypApexTwo_refl_zero (z : ℂ) :
    -(3 / 2) + σ.rotTwo (σ.refl 0 z) ^ σ.p₂ / 2 = conj (-(3 / 2) + σ.rotTwo z ^ σ.p₂ / 2) := by
  simp only [rotTwo_refl_zero h, mul_pow, hypExp_two_pow_eq_one (θ₂_mul σ), one_mul, map_add,
    map_div₀, map_pow, map_ofNat, map_neg]

theorem lensCoord_refl_two {z : ℂ} (hz : ‖z‖ < 1) :
    lensCoord σ (σ.refl 2 z) = -lensCoord σ z := by
  rw [lensCoord, lensCoord, rotTwo_refl_two h hz, Complex.conj_im, Complex.normSq_conj]
  ring

theorem abs_lensCoord_refl_two {z : ℂ} (hz : ‖z‖ < 1) :
    |lensCoord σ (σ.refl 2 z)| = |lensCoord σ z| := by
  rw [lensCoord_refl_two h hz, abs_neg]

theorem wallSide_zero_vertexOne_pos : 0 < σ.wallSide 0 σ.vertexOne := by
  change 0 < σ.vertexOne.im
  rw [vertexOne_eq, im_ofReal_mul, Complex.exp_ofReal_mul_I_im]
  exact mul_pos (sideOneThree_pos h) σ.sin_θ₃_pos

theorem wallSide_one_vertexTwo_pos : 0 < σ.wallSide 1 σ.vertexTwo := by
  rw [wallSide_one_apply, vertexTwo_eq, ofReal_re, ofReal_im, mul_zero, sub_zero]
  exact mul_pos σ.sin_θ₃_pos (sideTwoThree_pos h)

theorem ne_vertexOne_of_wallZero {z : ℂ} (hw : σ.wallSide 0 z = 0) : z ≠ σ.vertexOne := by
  rintro rfl
  linarith [wallSide_zero_vertexOne_pos h]

theorem ne_vertexTwo_of_wallOne {z : ℂ} (hw : σ.wallSide 1 z = 0) : z ≠ σ.vertexTwo := by
  rintro rfl
  linarith [wallSide_one_vertexTwo_pos h]

omit h in
theorem wallSide_one_ne_zero_of_wallZero {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (hw : σ.wallSide 0 z = 0) : σ.wallSide 1 z ≠ 0 := by
  intro h1
  obtain ⟨x, -, -, rfl⟩ := σ.eq_real_of_wallZero hz hw
  rw [wallSide_one_apply, ofReal_re, ofReal_im, mul_zero, sub_zero] at h1
  have hx : x = 0 := (mul_eq_zero.1 h1).resolve_left σ.sin_θ₃_pos.ne'
  exact h0 (by rw [hx, ofReal_zero])

omit h in
theorem wallSide_zero_ne_zero_of_wallOne {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (hw : σ.wallSide 1 z = 0) : σ.wallSide 0 z ≠ 0 := fun h1 =>
  wallSide_one_ne_zero_of_wallZero hz h0 h1 hw

theorem canon_sum_zero_of_wallZero {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 0 z = 0) :
    canon σ 1 z + canon σ 2 z = 0 := by
  by_cases h0 : z = 0
  · subst h0
    rw [canon_one_zero h, canon_two_zero]
    ring
  by_cases h2 : z = σ.vertexTwo
  · subst h2
    rw [canon_one_vertexTwo, canon_two_vertexTwo h]
    ring
  rw [canon_add_canon_zero_three h (mem_domZeroThree h hz h0 h2), hw]
  ring

theorem canon_sum_zero_of_wallOne {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 1 z = 0) :
    canon σ 0 z + canon σ 2 z = 0 := by
  by_cases h0 : z = 0
  · subst h0
    rw [canon_zero_zero h, canon_two_zero]
    ring
  by_cases h1 : z = σ.vertexOne
  · subst h1
    rw [canon_zero_vertexOne, canon_two_vertexOne h]
    ring
  rw [canon_add_canon_one_three h (mem_domOneThree h hz h0 h1), hw]
  ring

theorem canon_sum_zero_of_wallTwo {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 2 z = 0) :
    canon σ 0 z + canon σ 1 z = 0 := by
  by_cases h1 : z = σ.vertexOne
  · subst h1
    rw [canon_zero_vertexOne, canon_one_vertexOne h]
    ring
  by_cases h2 : z = σ.vertexTwo
  · subst h2
    rw [canon_zero_vertexTwo h, canon_one_vertexTwo]
    ring
  rw [canon_add_canon_one_two h (mem_domOneTwo h hz h1 h2), hw]
  ring

theorem canon_zero_ge_of_wallZero {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 0 z = 0) :
    |canon σ 1 z| ≤ canon σ 0 z := by
  have a := canon_zero_add_one_nonneg h hz
  have b := canon_zero_add_two_nonneg h hz
  have c := canon_sum_zero_of_wallZero h hz hw
  exact abs_le.2 ⟨by linarith, by linarith⟩

theorem canon_one_ge_of_wallOne {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 1 z = 0) :
    |canon σ 0 z| ≤ canon σ 1 z := by
  have a := canon_zero_add_one_nonneg h hz
  have b := canon_one_add_two_nonneg h hz
  have c := canon_sum_zero_of_wallOne h hz hw
  exact abs_le.2 ⟨by linarith, by linarith⟩

theorem canon_two_ge_of_wallTwo {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 2 z = 0) :
    |canon σ 0 z| ≤ canon σ 2 z := by
  have a := canon_zero_add_two_nonneg h hz
  have b := canon_one_add_two_nonneg h hz
  have c := canon_sum_zero_of_wallTwo h hz hw
  exact abs_le.2 ⟨by linarith, by linarith⟩

theorem canon_one_lt_of_wallZero {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (hw : σ.wallSide 0 z = 0) : canon σ 1 z < canon σ 0 z := by
  have hd := mem_domOneThree h hz h0 (ne_vertexOne_of_wallZero h hw)
  have e := canon_add_canon_one_three h hd
  have hp := mul_pos (pow_pos (abs_pos.2 (wallSide_one_ne_zero_of_wallZero hz h0 hw)) 2)
    (cofOneThree_pos h hd)
  rw [sq_abs] at hp
  linarith [canon_sum_zero_of_wallZero h hz hw]

theorem canon_zero_lt_of_wallOne {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (hw : σ.wallSide 1 z = 0) : canon σ 0 z < canon σ 1 z := by
  have hd := mem_domZeroThree h hz h0 (ne_vertexTwo_of_wallOne h hw)
  have e := canon_add_canon_zero_three h hd
  have hp := mul_pos (pow_pos (abs_pos.2 (wallSide_zero_ne_zero_of_wallOne hz h0 hw)) 2)
    (cofZeroThree_pos h hd)
  rw [sq_abs] at hp
  linarith [canon_sum_zero_of_wallOne h hz hw]

omit h in
theorem discAngle_of_wallZero {z : ℂ} (hw : σ.wallSide 0 z = 0) : discAngle z = 0 := by
  change halfArg ‖z‖ z.re z.im = 0
  change z.im = 0 at hw
  rw [hw, halfArg_zero]

omit h in
theorem discAngle_of_wallOne {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (hw : σ.wallSide 1 z = 0) : discAngle z = σ.θ₃ := by
  have hs := sector_three hz
  refine discAngle_eq_of_ray (by linarith [θ₃_pos σ, Real.pi_pos])
    (by linarith [θ₃_le σ, Real.pi_pos]) h0 ?_ (re_rot_nonneg (θ₃_pos σ) (θ₃_le σ) hs.1 hs.2)
  have := wallSide_one_eq_neg_im (σ := σ) z
  linarith

theorem psiTwo_of_wallZero {z : ℂ} (hz : z ∈ σ.triangle) (h2 : z ≠ σ.vertexTwo)
    (hw : σ.wallSide 0 z = 0) : psiTwo σ z = σ.θ₂ := by
  have hz1 := norm_lt_one_of_mem h hz
  have hs := sector_two h hz
  have hv := (valid_two h hz h2).1
  have hne : σ.rotTwo z ≠ 0 := by
    intro h0
    rw [h0, norm_zero, zero_re, add_zero] at hv
    exact lt_irrefl 0 hv
  refine discAngle_eq_of_ray (by linarith [θ₂_pos σ, Real.pi_pos])
    (by linarith [θ₂_le σ, Real.pi_pos]) hne ?_ (re_rot_nonneg (θ₂_pos σ) (θ₂_le σ) hs.1 hs.2)
  have e := rotTwo_rot_im_mul_normSq h z
  rw [hw, mul_zero, neg_zero] at e
  exact (mul_eq_zero.1 e).resolve_right
    (normSq_pos_of_ne (one_sub_vertexTwo_mul_ne_zero h hz1)).ne'

theorem im_rotTwo_of_wallTwo {z : ℂ} (hz : ‖z‖ < 1) (hw : σ.wallSide 2 z = 0) :
    (σ.rotTwo z).im = 0 := by
  rw [wallSide_two_eq_rotTwo h] at hw
  exact (mul_eq_zero.1 hw).resolve_right
    (normSq_pos_of_ne (one_sub_vertexTwo_mul_ne_zero h hz)).ne'

theorem psiOne_of_wallTwo {z : ℂ} (hz : z ∈ σ.triangle) (h1 : z ≠ σ.vertexOne)
    (hw : σ.wallSide 2 z = 0) : psiOne σ z = σ.θ₁ := by
  have hz1 := norm_lt_one_of_mem h hz
  obtain ⟨hv, -, hr⟩ := valid_one h hz h1
  have hne : σ.rotOne z ≠ 0 := rotOne_ne_zero h hz1 h1
  refine discAngle_eq_of_ray (by linarith [θ₁_pos σ, Real.pi_pos])
    (by linarith [θ₁_le σ, Real.pi_pos]) hne ?_ hr
  have e := rotOne_rot_im_mul_normSq h hz1
  rw [im_rotTwo_of_wallTwo h hz1 hw, mul_zero, neg_zero] at e
  have ht0 := sideOneTwo_pos h
  have hne' : 1 - (sideOneTwo σ : ℂ) * σ.rotTwo z ≠ 0 := by
    have := one_sub_conj_mul_ne_zero (a := (sideOneTwo σ : ℂ))
      (by rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos ht0]; exact sideOneTwo_lt_one h)
      (norm_rotTwo_lt_one h hz1)
    rwa [Complex.conj_ofReal] at this
  exact (mul_eq_zero.1 e).resolve_right (normSq_pos_of_ne hne').ne'

theorem lensCoord_of_wallTwo {z : ℂ} (hz : ‖z‖ < 1) (hw : σ.wallSide 2 z = 0) :
    lensCoord σ z = 0 := by
  rw [lensCoord, im_rotTwo_of_wallTwo h hz hw, mul_zero, zero_div]

theorem lensCoord_of_wallZero {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 0 z = 0) :
    lensCoord σ z = 2 * Real.sin σ.θ₂ * hd σ 1 z / (1 - hd σ 1 z ^ 2) := by
  have hz1 := norm_lt_one_of_mem h hz
  have hs := sector_two h hz
  set u := exp (-((σ.θ₂ : ℂ) * I)) * σ.rotTwo z with hu
  have him : u.im = 0 := by
    have e := rotTwo_rot_im_mul_normSq h z
    rw [hw, mul_zero, neg_zero] at e
    exact (mul_eq_zero.1 e).resolve_right
      (normSq_pos_of_ne (one_sub_vertexTwo_mul_ne_zero h hz1)).ne'
  have hre : 0 ≤ u.re := re_rot_nonneg (θ₂_pos σ) (θ₂_le σ) hs.1 hs.2
  have hW : σ.rotTwo z = exp ((σ.θ₂ : ℂ) * I) * u := by
    rw [hu, ← mul_assoc, exp_mul_exp_neg, one_mul]
  have hn : ‖σ.rotTwo z‖ = u.re := by
    rw [hW, norm_mul, Complex.norm_exp_ofReal_mul_I, one_mul, eq_ofReal_of_im him,
      Complex.norm_real, Real.norm_eq_abs, ofReal_re, abs_of_nonneg hre]
  have hd1 : hd σ 1 z = u.re := by
    change ‖mob σ.vertexTwo z‖ = u.re
    rw [← norm_rotTwo h, hn]
  have him' : (σ.rotTwo z).im = Real.sin σ.θ₂ * u.re := by
    rw [hW, mul_im, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im, him, mul_zero,
      zero_add]
  rw [lensCoord, him', hd1, Complex.normSq_eq_norm_sq, hn]
  ring

theorem lensCoord_of_wallOne {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 1 z = 0) :
    lensCoord σ z = 2 * Real.sin σ.θ₁ * hd σ 0 z / (1 - hd σ 0 z ^ 2) := by
  have hz1 := norm_lt_one_of_mem h hz
  have hs := sector_one h hz
  have him : (σ.rotOne z).im = 0 := by
    have e := rotOne_im_mul_normSq h hz1
    rw [hw, mul_zero] at e
    exact (mul_eq_zero.1 e).resolve_right
      (normSq_pos_of_ne (one_sub_conj_vertexOne_mul_ne_zero h hz1)).ne'
  have hre : 0 ≤ (σ.rotOne z).re := re_nonneg_of_sector (θ₁_pos σ) (θ₁_le σ) hs.1 hs.2
  have hn : ‖σ.rotOne z‖ = (σ.rotOne z).re := by
    rw [eq_ofReal_of_im him, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hre, ofReal_re]
  have hd0 : hd σ 0 z = (σ.rotOne z).re := by
    change ‖mob σ.vertexOne z‖ = _
    rw [← norm_rotOne h, hn]
  have him' : (exp (-((σ.θ₁ : ℂ) * I)) * σ.rotOne z).im = -(Real.sin σ.θ₁ * (σ.rotOne z).re) := by
    rw [exp_neg_ofReal_mul_I_eq]
    simp only [mul_im, sub_re, sub_im, ofReal_re, ofReal_im, mul_re, I_re, I_im, him]
    ring
  rw [lensCoord_eq_rotOne h hz1, him', hd0, Complex.normSq_eq_norm_sq, hn]
  ring

omit h in
theorem lensCoord_ge_aux {s ϖ : ℝ} (hs : 0 ≤ s) (hϖ0 : 0 ≤ ϖ) (hϖ1 : ϖ < 1) :
    2 * s * ϖ ≤ 2 * s * ϖ / (1 - ϖ ^ 2) := by
  have hD : 0 < 1 - ϖ ^ 2 := by nlinarith
  rw [le_div_iff₀ hD]
  have := mul_nonneg (mul_nonneg (mul_nonneg zero_le_two hs) hϖ0) (sq_nonneg ϖ)
  nlinarith

theorem lensCoord_ge_of_wallZero {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 0 z = 0) :
    2 * Real.sin σ.θ₂ * hd σ 1 z ≤ lensCoord σ z := by
  rw [lensCoord_of_wallZero h hz hw]
  exact lensCoord_ge_aux σ.sin_θ₂_pos.le (hd_nonneg 1 z)
    (hd_lt_one h 1 (norm_lt_one_of_mem h hz))

theorem lensCoord_ge_of_wallOne {z : ℂ} (hz : z ∈ σ.triangle) (hw : σ.wallSide 1 z = 0) :
    2 * Real.sin σ.θ₁ * hd σ 0 z ≤ lensCoord σ z := by
  rw [lensCoord_of_wallOne h hz hw]
  exact lensCoord_ge_aux σ.sin_θ₁_pos.le (hd_nonneg 0 z)
    (hd_lt_one h 0 (norm_lt_one_of_mem h hz))

theorem blendThree_lt_of_wallZero {w δ : ℝ} (hw : 0 < w) (hδ : 0 < δ) {z : ℂ}
    (hz : z ∈ σ.triangle) (h0 : z ≠ 0) (hw0 : σ.wallSide 0 z = 0) :
    blendThree σ w δ z < -w := by
  have hc := canon_one_lt_of_wallZero h hz h0 hw0
  have hq : 0 < w / δ := div_pos hw hδ
  rw [blendThree, discAngle_of_wallZero hw0, mul_zero, zero_div, zero_sub]
  have := mul_pos hq (sub_pos.2 hc)
  nlinarith

theorem blendThree_gt_of_wallOne {w δ : ℝ} (hw : 0 < w) (hδ : 0 < δ) {z : ℂ}
    (hz : z ∈ σ.triangle) (h0 : z ≠ 0) (hw1 : σ.wallSide 1 z = 0) :
    w < blendThree σ w δ z := by
  have hc := canon_zero_lt_of_wallOne h hz h0 hw1
  have hq : 0 < w / δ := div_pos hw hδ
  rw [blendThree, discAngle_of_wallOne hz h0 hw1, mul_div_assoc, div_self (θ₃_pos σ).ne']
  have := mul_pos hq (sub_pos.2 hc)
  nlinarith

theorem continuousAt_refl (i : Fin 3) {z : ℂ} (hz : ‖z‖ < 1) : ContinuousAt (σ.refl i) z := by
  fin_cases i
  · exact Complex.continuous_conj.continuousAt
  · change ContinuousAt (fun z : ℂ => exp (2 * (σ.θ₃ : ℂ) * I) * conj z) z
    exact (continuous_const.mul Complex.continuous_conj).continuousAt
  · change ContinuousAt (σ.refl 2) z
    have e : σ.refl 2 = fun u => mob (-σ.vertexTwo)
        (exp (-(2 * (σ.θ₂ : ℂ) * I)) * conj (mob σ.vertexTwo u)) := by
      funext u
      rw [refl_two_eq h, mobInv_eq_mob_neg]
    rw [e]
    have hv := norm_vertexTwo_lt_one h
    have h1 : 1 - conj (-σ.vertexTwo) * (exp (-(2 * (σ.θ₂ : ℂ) * I)) *
        conj (mob σ.vertexTwo z)) ≠ 0 := by
      rw [map_neg, neg_mul, sub_neg_eq_add]
      apply one_add_conj_mul_ne_zero hv
      rw [norm_mul, norm_exp_neg_two, one_mul, Complex.norm_conj]
      exact norm_mob_lt_one hv hz
    have hm : ContinuousAt (mob σ.vertexTwo) z :=
      (contDiffAt_mob (one_sub_conj_mul_ne_zero hv hz)).continuousAt
    exact ContinuousAt.comp (g := mob (-σ.vertexTwo)) (contDiffAt_mob h1).continuousAt
      (continuousAt_const.mul (Complex.continuous_conj.continuousAt.comp hm))

variable (σ) in
def reflNbhd (i : Fin 3) (W : Set ℂ) : Set ℂ := W ∩ σ.refl i ⁻¹' W

omit h in
theorem reflNbhd_subset (i : Fin 3) (W : Set ℂ) : reflNbhd σ i W ⊆ W := inter_subset_left

theorem isOpen_reflNbhd (i : Fin 3) {W : Set ℂ} (hW : IsOpen W) (hWd : ∀ z ∈ W, ‖z‖ < 1) :
    IsOpen (reflNbhd σ i W) :=
  ContinuousOn.isOpen_inter_preimage
    (fun z hz => (continuousAt_refl h i (hWd z hz)).continuousWithinAt) hW hW

theorem refl_mapsTo_reflNbhd (i : Fin 3) {W : Set ℂ} (hWd : ∀ z ∈ W, ‖z‖ < 1) :
    MapsTo (σ.refl i) (reflNbhd σ i W) (reflNbhd σ i W) := by
  intro z hz
  refine ⟨hz.2, ?_⟩
  change σ.refl i (σ.refl i z) ∈ W
  rw [refl_refl h i (hWd z hz.1)]
  exact hz.1

theorem mem_reflNbhd_of_wall (i : Fin 3) {W : Set ℂ} {z : ℂ} (hzW : z ∈ W) (hz : ‖z‖ < 1)
    (hw : σ.wallSide i z = 0) : z ∈ reflNbhd σ i W := by
  refine ⟨hzW, ?_⟩
  change σ.refl i z ∈ W
  rw [refl_eq_self h i hz hw]
  exact hzW

theorem reflNbhd_subset_reflChart (i : Fin 3) {W : Set ℂ} (hWd : ∀ z ∈ W, ‖z‖ < 1) :
    reflNbhd σ i W ⊆ σ.reflChart i := fun z hz => mem_reflChart h i (hWd z hz.1)

end Hyp

variable (σ)

def hypWallSetZero (L : HypLayout) : Set ℂ :=
  {z | ‖z‖ < 1 ∧ 0 < ‖z‖ + z.re ∧ L.g < hd σ 0 z ∧ -L.e < canon σ 0 z ∧
    (hd σ 1 z < L.a ∨ 2 * L.β' < lensCoord σ z) ∧ blendThree σ 1 L.e z < -1 ∧
    (hd σ 1 z < L.g ∨ (0 < ‖σ.rotTwo z‖ + (σ.rotTwo z).re ∧
      -Real.pi < 2 * σ.θ₂ - psiTwo σ z ∧ 2 * σ.θ₂ - psiTwo σ z < Real.pi))}

def hypWallSetOne (L : HypLayout) : Set ℂ :=
  {z | ‖z‖ < 1 ∧ 0 < ‖z‖ + z.re ∧ L.g < hd σ 1 z ∧ -L.e < canon σ 1 z ∧
    (hd σ 0 z < L.a ∨ 2 * L.β' < lensCoord σ z) ∧ 1 < blendThree σ 1 L.e z ∧
    -Real.pi < 2 * σ.θ₃ - discAngle z ∧ 2 * σ.θ₃ - discAngle z < Real.pi}

def hypWallSetTwo (L : HypLayout) : Set ℂ :=
  {z | ‖z‖ < 1 ∧ L.g₃ < ‖z‖ ∧ |lensCoord σ z| < L.β / 2 ∧
    (hd σ 0 z < L.g ∨ (0 < ‖σ.rotOne z‖ + (σ.rotOne z).re ∧
      -Real.pi < 2 * σ.θ₁ - psiOne σ z ∧ 2 * σ.θ₁ - psiOne σ z < Real.pi))}

def hypWallNbhd (L : HypLayout) : Fin 3 → Set ℂ
  | 0 => reflNbhd σ 0 (hypWallSetZero σ L)
  | 1 => reflNbhd σ 1 (hypWallSetOne σ L)
  | 2 => reflNbhd σ 2 (hypWallSetTwo σ L)

variable {σ}

theorem canonForm_lt_canonForm {τ x y : ℝ} (hτ0 : 0 < τ) (hτ1 : τ < 1)
    (hxy : x < y) (hy : y < 1) : canonForm τ x < canonForm τ y := by
  have hdx : 0 < 1 - x * τ := by nlinarith
  have hdy : 0 < 1 - y * τ := by nlinarith
  rw [canonForm, canonForm, div_lt_div_iff₀ hdx hdy]
  nlinarith [mul_pos (sub_pos.2 hxy) (by nlinarith : (0 : ℝ) < 1 - τ ^ 2)]

theorem hypWallNbhd_zero_subset (L : HypLayout) :
    hypWallNbhd σ L 0 ⊆ {z | hd σ 1 z < L.a ∨ 2 * L.β' < lensCoord σ z} :=
  fun _ hz => hz.1.2.2.2.2.1

theorem hypWallNbhd_one_subset (L : HypLayout) :
    hypWallNbhd σ L 1 ⊆ {z | hd σ 0 z < L.a ∨ 2 * L.β' < lensCoord σ z} :=
  fun _ hz => hz.1.2.2.2.2.1

theorem hypWallNbhd_two_subset (L : HypLayout) :
    hypWallNbhd σ L 2 ⊆ {z | |lensCoord σ z| < L.β / 2} :=
  fun _ hz => hz.1.2.2.1

theorem hypWallNbhd_subset (L : HypLayout) (hg₃ : 0 < L.g₃) (i : Fin 3) :
    hypWallNbhd σ L i ⊆ {z | ‖z‖ < 1 ∧ z ≠ 0} := by
  have hne : ∀ z : ℂ, 0 < ‖z‖ + z.re → z ≠ 0 := fun z hz h0 => by
    rw [h0, norm_zero, zero_re, add_zero] at hz
    exact lt_irrefl 0 hz
  fin_cases i
  · exact fun z hz => ⟨hz.1.1, hne z hz.1.2.1⟩
  · exact fun z hz => ⟨hz.1.1, hne z hz.1.2.1⟩
  · refine fun z hz => ⟨hz.1.1, fun h0 => ?_⟩
    have := hz.1.2.1
    rw [h0, norm_zero] at this
    linarith

section Fold

variable (h : σ.curv = .hyperbolic)
include h

theorem tau_le_hd_of_canon_nonneg (j : Fin 3) {z : ℂ} (hc : 0 ≤ canon σ j z) :
    tau σ j ≤ hd σ j z := by
  have hτ := tau_mem h j
  by_contra hlt
  push Not at hlt
  have hD : 0 < 1 - hd σ j z * tau σ j := by nlinarith [hd_nonneg (σ := σ) j z]
  have : canon σ j z < 0 := div_neg_of_neg_of_pos (by linarith) hD
  linarith

theorem canon_lt_of_hd_lt (j : Fin 3) {z : ℂ} {a : ℝ} (ha : a < 1) (hlt : hd σ j z < a) :
    canon σ j z < canonForm (tau σ j) a :=
  canonForm_lt_canonForm (tau_mem h j).1 (tau_mem h j).2 hlt ha

theorem lt_hd_of_canon_nonneg (j : Fin 3) {z : ℂ} (hc : 0 ≤ canon σ j z)
    {g b e : ℝ} (hgb : g < b) (hb1 : b < 1) (he : 0 < e) (hcb : canonForm (tau σ j) b < -e) :
    g < hd σ j z := by
  by_contra hle
  push Not at hle
  have := canon_lt_of_hd_lt h j hb1 (lt_of_le_of_lt hle hgb)
  linarith

theorem continuousAt_hd_of_disc (j : Fin 3) {z : ℂ} (hz : ‖z‖ < 1) :
    ContinuousAt (hd σ j) z := by
  fin_cases j
  · change ContinuousAt (fun u => ‖mob σ.vertexOne u‖) z
    exact (contDiffAt_mob (one_sub_conj_mul_ne_zero (norm_vertexOne_lt_one h) hz)).continuousAt.norm
  · change ContinuousAt (fun u => ‖mob σ.vertexTwo u‖) z
    exact (contDiffAt_mob (one_sub_conj_mul_ne_zero (norm_vertexTwo_lt_one h) hz)).continuousAt.norm
  · exact continuous_norm.continuousAt

theorem continuousAt_canon_of_disc (j : Fin 3) {z : ℂ} (hz : ‖z‖ < 1) :
    ContinuousAt (canon σ j) z := by
  have hc := continuousAt_hd_of_disc h j hz
  have hne : 1 - hd σ j z * tau σ j ≠ 0 := by
    have := hd_lt_one h j hz
    have := hd_nonneg (σ := σ) j z
    have := tau_mem h j
    nlinarith
  exact (hc.sub continuousAt_const).div (continuousAt_const.sub (hc.mul continuousAt_const)) hne

theorem continuousAt_blendThree_of_disc (w δ : ℝ) {z : ℂ} (hz : ‖z‖ < 1)
    (hψ : 0 < ‖z‖ + z.re) : ContinuousAt (blendThree σ w δ) z := by
  have hd : ContinuousAt (fun u : ℂ => discAngle u) z :=
    (contDiffAt_discAngle_comp' contDiffAt_id hψ).continuousAt
  exact (continuousAt_const.mul (((continuousAt_const.mul hd).div_const _).sub
    continuousAt_const)).add (continuousAt_const.mul
      ((continuousAt_canon_of_disc h 1 hz).sub (continuousAt_canon_of_disc h 0 hz)))

omit h in
theorem hypSwitch_cases {a b β β' d : ℝ} (hab : a < b) (hβ0 : 0 < β) (hβ : β < β') {z z' : ℂ}
    (h1 : d < a ∨ 2 * β' < lensCoord σ z) (h2 : d < a ∨ 2 * β' < lensCoord σ z') :
    coneStep a b d = 0 ∨ (lensSwitch σ β β' z = 1 ∧ lensSwitch σ β β' z' = 1) := by
  rcases h1 with h1 | h1
  · exact Or.inl (coneStep_eq_zero hab h1.le)
  rcases h2 with h2 | h2
  · exact Or.inl (coneStep_eq_zero hab h2.le)
  exact Or.inr ⟨coneStep_eq_one hβ (by linarith), coneStep_eq_one hβ (by linarith)⟩

theorem isOpen_hypWallSetZero (L : HypLayout) : IsOpen (hypWallSetZero σ L) := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hz
  have e5 : ∀ᶠ u in 𝓝 z, hd σ 1 u < L.a ∨ 2 * L.β' < lensCoord σ u := by
    rcases a5 with q | q
    · exact ((continuousAt_hd_of_disc h 1 a1).eventually (gt_mem_nhds q)).mono
        fun u hu => Or.inl hu
    · exact ((contDiffAt_lensCoord h a1).continuousAt.eventually (lt_mem_nhds q)).mono
        fun u hu => Or.inr hu
  have e7 : ∀ᶠ u in 𝓝 z, hd σ 1 u < L.g ∨ (0 < ‖σ.rotTwo u‖ + (σ.rotTwo u).re ∧
      -Real.pi < 2 * σ.θ₂ - psiTwo σ u ∧ 2 * σ.θ₂ - psiTwo σ u < Real.pi) := by
    rcases a7 with q | ⟨q1, q2, q3⟩
    · exact ((continuousAt_hd_of_disc h 1 a1).eventually (gt_mem_nhds q)).mono
        fun u hu => Or.inl hu
    · have c1 : ContinuousAt (fun u => ‖σ.rotTwo u‖ + (σ.rotTwo u).re) z :=
        ((contDiffAt_rotTwo h a1).continuousAt.norm).add
          (Complex.continuous_re.continuousAt.comp (contDiffAt_rotTwo h a1).continuousAt)
      have c2 : ContinuousAt (fun u => 2 * σ.θ₂ - psiTwo σ u) z :=
        continuousAt_const.sub (contDiffAt_psiTwo h a1 q1).continuousAt
      filter_upwards [c1.eventually (lt_mem_nhds q1), c2.eventually (lt_mem_nhds q2),
        c2.eventually (gt_mem_nhds q3)] with u b1 b2 b3
      exact Or.inr ⟨b1, b2, b3⟩
  have c2 : ContinuousAt (fun u : ℂ => ‖u‖ + u.re) z :=
    (continuous_norm.add Complex.continuous_re).continuousAt
  filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds a1),
    c2.eventually (lt_mem_nhds a2), (continuousAt_hd_of_disc h 0 a1).eventually (lt_mem_nhds a3),
    (continuousAt_canon_of_disc h 0 a1).eventually (lt_mem_nhds a4), e5,
    (continuousAt_blendThree_of_disc h _ _ a1 a2).eventually (gt_mem_nhds a6), e7]
    with u b1 b2 b3 b4 b5 b6 b7
  exact ⟨b1, b2, b3, b4, b5, b6, b7⟩

theorem isOpen_hypWallSetOne (L : HypLayout) : IsOpen (hypWallSetOne σ L) := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hz
  have e5 : ∀ᶠ u in 𝓝 z, hd σ 0 u < L.a ∨ 2 * L.β' < lensCoord σ u := by
    rcases a5 with q | q
    · exact ((continuousAt_hd_of_disc h 0 a1).eventually (gt_mem_nhds q)).mono
        fun u hu => Or.inl hu
    · exact ((contDiffAt_lensCoord h a1).continuousAt.eventually (lt_mem_nhds q)).mono
        fun u hu => Or.inr hu
  have c2 : ContinuousAt (fun u : ℂ => ‖u‖ + u.re) z :=
    (continuous_norm.add Complex.continuous_re).continuousAt
  have c8 : ContinuousAt (fun u : ℂ => 2 * σ.θ₃ - discAngle u) z :=
    continuousAt_const.sub (contDiffAt_discAngle_comp' contDiffAt_id a2).continuousAt
  filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds a1),
    c2.eventually (lt_mem_nhds a2), (continuousAt_hd_of_disc h 1 a1).eventually (lt_mem_nhds a3),
    (continuousAt_canon_of_disc h 1 a1).eventually (lt_mem_nhds a4), e5,
    (continuousAt_blendThree_of_disc h _ _ a1 a2).eventually (lt_mem_nhds a6),
    c8.eventually (lt_mem_nhds a7), c8.eventually (gt_mem_nhds a8)]
    with u b1 b2 b3 b4 b5 b6 b7 b8
  exact ⟨b1, b2, b3, b4, b5, b6, b7, b8⟩

theorem isOpen_hypWallSetTwo (L : HypLayout) : IsOpen (hypWallSetTwo σ L) := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨a1, a2, a3, a4⟩ := hz
  have e4 : ∀ᶠ u in 𝓝 z, hd σ 0 u < L.g ∨ (0 < ‖σ.rotOne u‖ + (σ.rotOne u).re ∧
      -Real.pi < 2 * σ.θ₁ - psiOne σ u ∧ 2 * σ.θ₁ - psiOne σ u < Real.pi) := by
    rcases a4 with q | ⟨q1, q2, q3⟩
    · exact ((continuousAt_hd_of_disc h 0 a1).eventually (gt_mem_nhds q)).mono
        fun u hu => Or.inl hu
    · have c1 : ContinuousAt (fun u => ‖σ.rotOne u‖ + (σ.rotOne u).re) z :=
        ((contDiffAt_rotOne h a1).continuousAt.norm).add
          (Complex.continuous_re.continuousAt.comp (contDiffAt_rotOne h a1).continuousAt)
      have c2 : ContinuousAt (fun u => 2 * σ.θ₁ - psiOne σ u) z :=
        continuousAt_const.sub (contDiffAt_psiOne h a1 q1).continuousAt
      filter_upwards [c1.eventually (lt_mem_nhds q1), c2.eventually (lt_mem_nhds q2),
        c2.eventually (gt_mem_nhds q3)] with u b1 b2 b3
      exact Or.inr ⟨b1, b2, b3⟩
  filter_upwards [continuous_norm.continuousAt.eventually (gt_mem_nhds a1),
    continuous_norm.continuousAt.eventually (lt_mem_nhds a2),
    (contDiffAt_lensCoord h a1).continuousAt.abs.eventually (gt_mem_nhds a3), e4]
    with u b1 b2 b3 b4
  exact ⟨b1, b2, b3, b4⟩

theorem isOpen_hypWallNbhd (L : HypLayout) (i : Fin 3) : IsOpen (hypWallNbhd σ L i) := by
  fin_cases i
  · exact isOpen_reflNbhd h 0 (isOpen_hypWallSetZero h L) fun _ hz => hz.1
  · exact isOpen_reflNbhd h 1 (isOpen_hypWallSetOne h L) fun _ hz => hz.1
  · exact isOpen_reflNbhd h 2 (isOpen_hypWallSetTwo h L) fun _ hz => hz.1

theorem refl_mapsTo_hypWallNbhd (L : HypLayout) (i : Fin 3) :
    MapsTo (σ.refl i) (hypWallNbhd σ L i) (hypWallNbhd σ L i) := by
  fin_cases i
  · exact refl_mapsTo_reflNbhd h 0 fun _ hz => hz.1
  · exact refl_mapsTo_reflNbhd h 1 fun _ hz => hz.1
  · exact refl_mapsTo_reflNbhd h 2 fun _ hz => hz.1

theorem hypWallNbhd_subset_reflChart (L : HypLayout) (i : Fin 3) :
    hypWallNbhd σ L i ⊆ σ.reflChart i := by
  fin_cases i
  · exact reflNbhd_subset_reflChart h 0 fun _ hz => hz.1
  · exact reflNbhd_subset_reflChart h 1 fun _ hz => hz.1
  · exact reflNbhd_subset_reflChart h 2 fun _ hz => hz.1

theorem wall_mem_hypWallSetZero {L : HypLayout} (hg0 : 0 < L.g) (hgb : L.g < L.b)
    (hb1 : L.b < 1) (he : 0 < L.e) (hc1 : canonForm (tauOne σ) L.b < -L.e)
    (hs2 : L.β' < L.a * Real.sin σ.θ₂) {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (hw0 : σ.wallSide 0 z = 0) : z ∈ hypWallSetZero σ L := by
  have hz1 := norm_lt_one_of_mem h hz
  have hc0 := le_trans (abs_nonneg _) (canon_zero_ge_of_wallZero h hz hw0)
  refine ⟨hz1, valid_three hz h0, lt_hd_of_canon_nonneg h 0 hc0 hgb hb1 he hc1,
    by linarith, ?_, blendThree_lt_of_wallZero h one_pos he hz h0 hw0, ?_⟩
  · rcases lt_or_ge (hd σ 1 z) L.a with q | q
    · exact Or.inl q
    · right
      have hl := lensCoord_ge_of_wallZero h hz hw0
      have := mul_le_mul_of_nonneg_left q (mul_nonneg zero_le_two σ.sin_θ₂_pos.le)
      linarith
  · by_cases h2 : z = σ.vertexTwo
    · left
      rw [h2]
      change ‖mob σ.vertexTwo σ.vertexTwo‖ < L.g
      rw [mob_self, norm_zero]
      exact hg0
    · right
      rw [psiTwo_of_wallZero h hz h2 hw0]
      exact ⟨(valid_two h hz h2).1, by linarith [θ₂_pos σ, Real.pi_pos],
        by linarith [θ₂_le σ, Real.pi_pos]⟩

theorem wall_mem_hypWallSetOne {L : HypLayout} (hgb : L.g < L.b) (hb1 : L.b < 1)
    (he : 0 < L.e) (hc2 : canonForm (tauTwo σ) L.b < -L.e)
    (hs1 : L.β' < L.a * Real.sin σ.θ₁) {z : ℂ} (hz : z ∈ σ.triangle) (h0 : z ≠ 0)
    (hw1 : σ.wallSide 1 z = 0) : z ∈ hypWallSetOne σ L := by
  have hz1 := norm_lt_one_of_mem h hz
  have hc1 := le_trans (abs_nonneg _) (canon_one_ge_of_wallOne h hz hw1)
  have hd3 := discAngle_of_wallOne hz h0 hw1
  refine ⟨hz1, valid_three hz h0, lt_hd_of_canon_nonneg h 1 hc1 hgb hb1 he hc2,
    by linarith, ?_, blendThree_gt_of_wallOne h one_pos he hz h0 hw1, ?_, ?_⟩
  · rcases lt_or_ge (hd σ 0 z) L.a with q | q
    · exact Or.inl q
    · right
      have hl := lensCoord_ge_of_wallOne h hz hw1
      have := mul_le_mul_of_nonneg_left q (mul_nonneg zero_le_two σ.sin_θ₁_pos.le)
      linarith
  · rw [hd3]
    linarith [θ₃_pos σ, Real.pi_pos]
  · rw [hd3]
    linarith [θ₃_le σ, Real.pi_pos]

theorem wall_mem_hypWallSetTwo {L : HypLayout} (hg0 : 0 < L.g) (hβ0 : 0 < L.β)
    (hg₃ : L.g₃ < tauThree σ) {z : ℂ} (hz : z ∈ σ.triangle) (hw2 : σ.wallSide 2 z = 0) :
    z ∈ hypWallSetTwo σ L := by
  have hz1 := norm_lt_one_of_mem h hz
  have hc2 := le_trans (abs_nonneg _) (canon_two_ge_of_wallTwo h hz hw2)
  have ht := tau_le_hd_of_canon_nonneg h 2 hc2
  refine ⟨hz1, lt_of_lt_of_le hg₃ ht, by
    rw [lensCoord_of_wallTwo h hz1 hw2, abs_zero]; exact half_pos hβ0, ?_⟩
  by_cases h1 : z = σ.vertexOne
  · left
    rw [h1]
    change ‖mob σ.vertexOne σ.vertexOne‖ < L.g
    rw [mob_self, norm_zero]
    exact hg0
  · right
    rw [psiOne_of_wallTwo h hz h1 hw2]
    exact ⟨(valid_one h hz h1).1, by linarith [θ₁_pos σ, Real.pi_pos],
      by linarith [θ₁_le σ, Real.pi_pos]⟩

theorem foldWall_diff_subset_hypWallNbhd {L : HypLayout} (hg0 : 0 < L.g) (hga : L.g < L.a)
    (hab : L.a < L.b) (hb1 : L.b < 1) (he : 0 < L.e) (hc1 : canonForm (tauOne σ) L.b < -L.e)
    (hc2 : canonForm (tauTwo σ) L.b < -L.e) (hβ0 : 0 < L.β)
    (hs1 : L.β' < L.a * Real.sin σ.θ₁) (hs2 : L.β' < L.a * Real.sin σ.θ₂)
    (hg₃ : L.g₃ < L.a₃) (ha₃ : L.a₃ < L.b₃) (hb₃ : L.b₃ < tauThree σ) (i : Fin 3) :
    σ.foldWall i \ {0} ⊆ hypWallNbhd σ L i := by
  have hgb : L.g < L.b := hga.trans hab
  intro z ⟨⟨hz, hw⟩, h0⟩
  have h0' : z ≠ 0 := h0
  have hz1 := norm_lt_one_of_mem h hz
  fin_cases i
  · exact mem_reflNbhd_of_wall h 0
      (wall_mem_hypWallSetZero h hg0 hgb hb1 he hc1 hs2 hz h0' hw) hz1 hw
  · exact mem_reflNbhd_of_wall h 1
      (wall_mem_hypWallSetOne h hgb hb1 he hc2 hs1 hz h0' hw) hz1 hw
  · exact mem_reflNbhd_of_wall h 2
      (wall_mem_hypWallSetTwo h hg0 hβ0 ((hg₃.trans ha₃).trans hb₃) hz hw) hz1 hw

theorem hypPreFold_refl_zero {L : HypLayout} (hab : L.a < L.b) (hb1 : L.b < 1)
    (hc2 : canonForm (tauTwo σ) L.b < -L.e) (hβ0 : 0 < L.β) (hβ : L.β < L.β') {z : ℂ}
    (hz : z ∈ hypWallNbhd σ L 0) :
    hypPreFold σ L (σ.refl 0 z) = conj (hypPreFold σ L z) := by
  obtain ⟨⟨-, -, a3, a4, a5, a6, a7⟩, ⟨-, -, b3, b4, b5, b6, -⟩⟩ := hz
  have n1 : hd σ 1 (σ.refl 0 z) = hd σ 1 z := hd_refl_zero_one h z
  have c1 : canon σ 1 (σ.refl 0 z) = canon σ 1 z := canon_eq_of_hd n1
  have n0 : ‖σ.refl 0 z‖ = ‖z‖ := norm_refl_zero' z
  rw [n1] at b5
  have g1 : ¬ hd σ 0 z < L.g := not_lt.2 a3.le
  have g1' : ¬ hd σ 0 (σ.refl 0 z) < L.g := not_lt.2 b3.le
  have k1 : ¬ canon σ 0 z < -L.e := not_lt.2 a4.le
  have k1' : ¬ canon σ 0 (σ.refl 0 z) < -L.e := not_lt.2 b4.le
  simp only [hypPreFold, g1, g1', k1, k1', n1, c1, n0, ite_false]
  by_cases c2 : hd σ 1 z < L.g
  · simp only [c2, ite_true]
    exact hypApexTwo_refl_zero h z
  simp only [c2, ite_false]
  by_cases c3 : ‖z‖ < L.g₃
  · simp only [c3, ite_true]
    exact hypOuterGerm_refl_zero z
  simp only [c3, ite_false]
  by_cases c5 : canon σ 1 z < -L.e
  · simp only [c5, ite_true]
    obtain ⟨hψ, q1, q2⟩ := a7.resolve_left c2
    exact cornerTwo_refl_zero h _ _ _ _ hψ q1 q2 (hypSwitch_cases hab hβ0 hβ a5 b5)
  simp only [c5, ite_false]
  have hca := (canonForm_lt_canonForm (tau_mem h 1).1 (tau_mem h 1).2 hab hb1).trans hc2
  have hna : ¬ hd σ 1 z < L.a := fun q =>
    c5 ((canon_lt_of_hd_lt h 1 (hab.trans hb1) q).trans hca)
  have l1 := a5.resolve_left hna
  have l1' := b5.resolve_left hna
  have nl : ¬ |lensCoord σ z| < L.β := fun q => by
    linarith [le_abs_self (lensCoord σ z)]
  have nl' : ¬ |lensCoord σ (σ.refl 0 z)| < L.β := fun q => by
    linarith [le_abs_self (lensCoord σ (σ.refl 0 z))]
  simp only [nl, nl', ite_false]
  exact cornerThree_refl_zero h _ _ _ _ (Or.inr ⟨coneStep_eq_zero (by norm_num) a6.le,
    coneStep_eq_zero (by norm_num) b6.le⟩)

theorem hypPreFold_refl_one {L : HypLayout} (hab : L.a < L.b) (hb1 : L.b < 1)
    (hc1 : canonForm (tauOne σ) L.b < -L.e) (hβ0 : 0 < L.β) (hβ : L.β < L.β') {z : ℂ}
    (hz : z ∈ hypWallNbhd σ L 1) :
    hypPreFold σ L (σ.refl 1 z) = conj (hypPreFold σ L z) := by
  obtain ⟨⟨-, a2, a3, a4, a5, a6, a7, a8⟩, ⟨-, -, b3, b4, b5, b6, -, -⟩⟩ := hz
  have n0 : hd σ 0 (σ.refl 1 z) = hd σ 0 z := hd_refl_one_zero h z
  have c0 : canon σ 0 (σ.refl 1 z) = canon σ 0 z := canon_eq_of_hd n0
  have nn : ‖σ.refl 1 z‖ = ‖z‖ := norm_refl_one' z
  rw [n0] at b5
  have g2 : ¬ hd σ 1 z < L.g := not_lt.2 a3.le
  have g2' : ¬ hd σ 1 (σ.refl 1 z) < L.g := not_lt.2 b3.le
  have k2 : ¬ canon σ 1 z < -L.e := not_lt.2 a4.le
  have k2' : ¬ canon σ 1 (σ.refl 1 z) < -L.e := not_lt.2 b4.le
  simp only [hypPreFold, g2, g2', k2, k2', n0, c0, nn, ite_false]
  by_cases c1 : hd σ 0 z < L.g
  · simp only [c1, ite_true]
    exact hypApexOne_refl_one h z
  simp only [c1, ite_false]
  by_cases c3 : ‖z‖ < L.g₃
  · simp only [c3, ite_true]
    exact hypOuterGerm_refl_one z
  simp only [c3, ite_false]
  by_cases c4 : canon σ 0 z < -L.e
  · simp only [c4, ite_true]
    exact cornerOne_refl_one h _ _ _ _ (hypSwitch_cases hab hβ0 hβ a5 b5)
  simp only [c4, ite_false]
  have hca := (canonForm_lt_canonForm (tau_mem h 0).1 (tau_mem h 0).2 hab hb1).trans hc1
  have hna : ¬ hd σ 0 z < L.a := fun q =>
    c4 ((canon_lt_of_hd_lt h 0 (hab.trans hb1) q).trans hca)
  have l1 := a5.resolve_left hna
  have l1' := b5.resolve_left hna
  have nl : ¬ |lensCoord σ z| < L.β := fun q => by
    linarith [le_abs_self (lensCoord σ z)]
  have nl' : ¬ |lensCoord σ (σ.refl 1 z)| < L.β := fun q => by
    linarith [le_abs_self (lensCoord σ (σ.refl 1 z))]
  simp only [nl, nl', ite_false]
  exact cornerThree_refl_one h _ _ _ _ a2 a7 a8 (Or.inr ⟨coneStep_eq_one (by norm_num) a6.le,
    coneStep_eq_one (by norm_num) b6.le⟩)

theorem hypPreFold_refl_two {L : HypLayout} (hβ0 : 0 < L.β) (hβ : L.β < L.β') {z : ℂ}
    (hz : z ∈ hypWallNbhd σ L 2) :
    hypPreFold σ L (σ.refl 2 z) = conj (hypPreFold σ L z) := by
  obtain ⟨⟨a1, a2, a3, a4⟩, ⟨-, b2, b3, -⟩⟩ := hz
  have n0 : hd σ 0 (σ.refl 2 z) = hd σ 0 z := hd_refl_two_zero h a1
  have n1 : hd σ 1 (σ.refl 2 z) = hd σ 1 z := hd_refl_two_one h a1
  have c0 : canon σ 0 (σ.refl 2 z) = canon σ 0 z := canon_eq_of_hd n0
  have c1 : canon σ 1 (σ.refl 2 z) = canon σ 1 z := canon_eq_of_hd n1
  have g3 : ¬ ‖z‖ < L.g₃ := not_lt.2 a2.le
  have g3' : ¬ ‖σ.refl 2 z‖ < L.g₃ := not_lt.2 b2.le
  have l : |lensCoord σ z| < L.β := by linarith
  have l' : |lensCoord σ (σ.refl 2 z)| < L.β := by linarith
  have s0 : lensSwitch σ L.β L.β' z = 0 :=
    coneStep_eq_zero hβ (by linarith [le_abs_self (lensCoord σ z)])
  have s0' : lensSwitch σ L.β L.β' (σ.refl 2 z) = 0 :=
    coneStep_eq_zero hβ (by linarith [le_abs_self (lensCoord σ (σ.refl 2 z))])
  simp only [hypPreFold, g3, g3', n0, n1, c0, c1, l, l', ite_false, ite_true]
  by_cases q1 : hd σ 0 z < L.g
  · simp only [q1, ite_true]
    exact hypApexOne_refl_two h a1
  simp only [q1, ite_false]
  by_cases q2 : hd σ 1 z < L.g
  · simp only [q2, ite_true]
    exact hypApexTwo_refl_two h a1
  simp only [q2, ite_false]
  by_cases q4 : canon σ 0 z < -L.e
  · simp only [q4, ite_true]
    obtain ⟨hψ, r1, r2⟩ := a4.resolve_left q1
    exact cornerOne_refl_two h _ _ _ _ a1 hψ r1 r2 (Or.inr ⟨s0, s0'⟩)
  simp only [q4, ite_false]
  by_cases q5 : canon σ 1 z < -L.e
  · simp only [q5, ite_true]
    exact cornerTwo_refl_two h _ _ _ _ a1 (Or.inr ⟨s0, s0'⟩)
  simp only [q5, ite_false]
  exact bridgeTwo_refl_two h a1

theorem hypPreFold_refl {L : HypLayout} (hab : L.a < L.b) (hb1 : L.b < 1)
    (hc1 : canonForm (tauOne σ) L.b < -L.e) (hc2 : canonForm (tauTwo σ) L.b < -L.e)
    (hβ0 : 0 < L.β) (hβ : L.β < L.β') (i : Fin 3) {z : ℂ} (hz : z ∈ hypWallNbhd σ L i) :
    hypPreFold σ L (σ.refl i z) = conj (hypPreFold σ L z) := by
  fin_cases i
  · exact hypPreFold_refl_zero h hab hb1 hc2 hβ0 hβ hz
  · exact hypPreFold_refl_one h hab hb1 hc1 hβ0 hβ hz
  · exact hypPreFold_refl_two h hβ0 hβ hz

end Fold

end HypFold

end GC.Seifert
