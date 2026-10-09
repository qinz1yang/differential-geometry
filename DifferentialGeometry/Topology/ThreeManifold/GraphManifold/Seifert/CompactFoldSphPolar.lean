import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldSphAngles
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldEuclidAngles

/-!
# Polar forms of the spherical bridges and the vertex angles

Lane CF-S, tier 2, curvature `+4` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §4). The profiles, moduli and bridge angles are smooth
on the bridge domains (`contDiffAt_sphCanon_*`, `contDiffAt_sphAngle*`), and each bridge is the
polar point `c + R e^{iΘ}` about the centres of its two circles (`sphBridgeOne_eq_polar_one`, …).
On the closed upper half plane the bridge angles about a common centre are ordered
(`sphAngleOneAtOne_le_sphAngleTwoAtOne`, …).

The vertex angles are the arguments of the rotated disc coordinates, `sphPsiOne = arg rotOne`,
`sphPsiTwo = arg rotTwo`, `arg z` at `v₃`, in A4's `discAngle` form. They have derivative `1` along
the circles about their vertex (`hasDerivAt_sphPsiOne_sphCirc`, …), and the reflections act on them
as on the sectors: `ψ ↦ -ψ` across the first wall and `ψ ↦ 2θ - ψ` across the second
(`sphPsiOne_refl_one`, `sphPsiOne_refl_two`, …). The bridge angles change by `Θ ↦ -Θ` or
`Θ ↦ 2π - Θ` under the reflection of their wall (`sphAngleOneAtOne_refl_one`, …).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace CompactShape

variable {σ : CompactShape}

def sphPsiOne (σ : CompactShape) (z : ℂ) : ℝ := discAngle (σ.rotOne z)

def sphPsiTwo (σ : CompactShape) (z : ℂ) : ℝ := discAngle (σ.rotTwo z)

section Spherical

variable (hs : σ.curv = .spherical)
include hs

theorem contDiffAt_sphCanon_zero {z : ℂ} (hv : 1 + conj σ.vertexOne * z ≠ 0)
    (hne : sphMoeb σ.vertexOne z ≠ 0) : ContDiffAt ℝ ∞ (σ.sphCanon 0) z :=
  contDiffAt_sphCanon_of hs (d := fun u => ‖sphMoeb σ.vertexOne u‖)
    ((contDiffAt_sphMoeb hv).norm ℝ hne)
    (Filter.Eventually.of_forall fun u => norm_rotOne_sph hs u)

theorem contDiffAt_sphCanon_one {z : ℂ} (hv : 1 + conj σ.vertexTwo * z ≠ 0)
    (hne : sphMoeb σ.vertexTwo z ≠ 0) : ContDiffAt ℝ ∞ (σ.sphCanon 1) z :=
  contDiffAt_sphCanon_of hs (d := fun u => ‖sphMoeb σ.vertexTwo u‖)
    ((contDiffAt_sphMoeb hv).norm ℝ hne)
    (Filter.Eventually.of_forall fun u => norm_rotTwo_sph hs u)

theorem contDiffAt_sphCanon_two {z : ℂ} (h0 : z ≠ 0) : ContDiffAt ℝ ∞ (σ.sphCanon 2) z :=
  contDiffAt_sphCanon_of hs (d := fun u => ‖u‖) (contDiffAt_norm ℝ h0)
    (Filter.Eventually.of_forall fun _ => rfl)

theorem contDiffAt_sphModOne {z : ℂ} (hv : 1 + conj σ.vertexOne * z ≠ 0)
    (hne : sphMoeb σ.vertexOne z ≠ 0) : ContDiffAt ℝ ∞ σ.sphModOne z :=
  contDiffAt_const.add (contDiffAt_const.mul (contDiffAt_sphCanon_zero hs hv hne))

theorem contDiffAt_sphModTwo {z : ℂ} (hv : 1 + conj σ.vertexTwo * z ≠ 0)
    (hne : sphMoeb σ.vertexTwo z ≠ 0) : ContDiffAt ℝ ∞ σ.sphModTwo z :=
  contDiffAt_const.add (contDiffAt_const.mul (contDiffAt_sphCanon_one hs hv hne))

theorem contDiffAt_sphModThree {z : ℂ} (h0 : z ≠ 0) : ContDiffAt ℝ ∞ σ.sphModThree z :=
  contDiffAt_const.sub (contDiffAt_const.mul (contDiffAt_sphCanon_two hs h0))

omit hs in
theorem ne_zero_of_domOne {z : ℂ} (hz : z ∈ σ.sphDomOne) : z ≠ 0 := by
  intro h0
  have := hz.1
  rw [h0, mul_zero] at this
  simp at this

omit hs in
theorem ne_zero_of_domZero {z : ℂ} (hz : z ∈ σ.sphDomZero) : z ≠ 0 :=
  ne_zero_of_pos_norm_add_re_sph hz.1

theorem contDiffAt_sphAngleOneAtOne {z : ℂ} (hz : z ∈ σ.sphDomOne)
    (hpos : 0 < σ.sphModOne z + ((σ.sphBridgeOne z).re - 3 / 2)) :
    ContDiffAt ℝ ∞ σ.sphAngleOneAtOne z :=
  ConeShape.contDiffAt_halfArg_comp (contDiffAt_sphModOne hs
      (one_add_conj_vertexOne_ne_of_domOne hz) (sphMoeb_vertexOne_ne_of_domOne hs hz))
    ((EuclidShape.contDiffAt_re_comp (contDiffAt_sphBridgeOne hs hz)).sub contDiffAt_const)
    (EuclidShape.contDiffAt_im_comp (contDiffAt_sphBridgeOne hs hz)) hpos

theorem contDiffAt_sphAngleTwoAtOne {z : ℂ} (hz : z ∈ σ.sphDomTwo)
    (hpos : 0 < σ.sphModOne z - ((σ.sphBridgeTwo z).re - 3 / 2)) :
    ContDiffAt ℝ ∞ σ.sphAngleTwoAtOne z :=
  ConeShape.contDiffAt_negHalfArg_comp (contDiffAt_sphModOne hs hz.2.1
      (sphMoeb_vertexOne_ne_of_domTwo hs hz))
    ((EuclidShape.contDiffAt_re_comp (contDiffAt_sphBridgeTwo hs hz)).sub contDiffAt_const)
    (EuclidShape.contDiffAt_im_comp (contDiffAt_sphBridgeTwo hs hz)) hpos

theorem contDiffAt_sphAngleTwoAtTwo {z : ℂ} (hz : z ∈ σ.sphDomTwo)
    (hpos : 0 < σ.sphModTwo z + ((σ.sphBridgeTwo z).re + 3 / 2)) :
    ContDiffAt ℝ ∞ σ.sphAngleTwoAtTwo z :=
  ConeShape.contDiffAt_halfArg_comp (contDiffAt_sphModTwo hs
      (one_add_vertexTwo_ne_of_domTwo hz) (sphMoeb_vertexTwo_ne_of_domTwo hs hz))
    ((EuclidShape.contDiffAt_re_comp (contDiffAt_sphBridgeTwo hs hz)).add contDiffAt_const)
    (EuclidShape.contDiffAt_im_comp (contDiffAt_sphBridgeTwo hs hz)) hpos

theorem contDiffAt_sphAngleZeroAtTwo {z : ℂ} (hz : z ∈ σ.sphDomZero)
    (hpos : 0 < σ.sphModTwo z - ((σ.sphBridgeZero z).re + 3 / 2)) :
    ContDiffAt ℝ ∞ σ.sphAngleZeroAtTwo z :=
  ConeShape.contDiffAt_negHalfArg_comp (contDiffAt_sphModTwo hs
      (one_add_vertexTwo_ne_of_domZero hz) (sphMoeb_vertexTwo_ne_of_domZero hz))
    ((EuclidShape.contDiffAt_re_comp (contDiffAt_sphBridgeZero hs hz)).add contDiffAt_const)
    (EuclidShape.contDiffAt_im_comp (contDiffAt_sphBridgeZero hs hz)) hpos

theorem contDiffAt_sphAngleOneAtThree {z : ℂ} (hz : z ∈ σ.sphDomOne)
    (hpos : 0 < σ.sphModThree z + (σ.sphBridgeOne z).re) :
    ContDiffAt ℝ ∞ σ.sphAngleOneAtThree z :=
  ConeShape.contDiffAt_halfArg_comp (contDiffAt_sphModThree hs (ne_zero_of_domOne hz))
    (EuclidShape.contDiffAt_re_comp (contDiffAt_sphBridgeOne hs hz))
    (EuclidShape.contDiffAt_im_comp (contDiffAt_sphBridgeOne hs hz)) hpos

theorem contDiffAt_sphAngleZeroAtThree {z : ℂ} (hz : z ∈ σ.sphDomZero)
    (hpos : 0 < σ.sphModThree z - (σ.sphBridgeZero z).re) :
    ContDiffAt ℝ ∞ σ.sphAngleZeroAtThree z :=
  ConeShape.contDiffAt_negHalfArg_comp (contDiffAt_sphModThree hs (ne_zero_of_domZero hz))
    (EuclidShape.contDiffAt_re_comp (contDiffAt_sphBridgeZero hs hz))
    (EuclidShape.contDiffAt_im_comp (contDiffAt_sphBridgeZero hs hz)) hpos

theorem sphBridgeOne_eq_polar_one {z : ℂ} (hz : z ∈ σ.sphDomOne)
    (hpos : 0 < σ.sphModOne z + ((σ.sphBridgeOne z).re - 3 / 2)) :
    σ.sphBridgeOne z =
      ((3 / 2 : ℝ) : ℂ) + (σ.sphModOne z : ℂ) * exp ((σ.sphAngleOneAtOne z : ℂ) * I) := by
  have hn : ‖σ.sphBridgeOne z - ((3 / 2 : ℝ) : ℂ)‖ = σ.sphModOne z := by
    push_cast
    exact (norm_sphBridgeOne hs hz).2
  have hsq := EuclidShape.polar_of_norm_sub (σ.sphBridgeOne z) ((3 / 2 : ℝ) : ℂ) (by simp) hn
  rw [ofReal_re] at hsq
  exact EuclidShape.eq_of_polar (halfArg_polar (sphModOne_pos hs z) hpos hsq)

theorem sphBridgeTwo_eq_polar_one {z : ℂ} (hz : z ∈ σ.sphDomTwo)
    (hpos : 0 < σ.sphModOne z - ((σ.sphBridgeTwo z).re - 3 / 2)) :
    σ.sphBridgeTwo z =
      ((3 / 2 : ℝ) : ℂ) + (σ.sphModOne z : ℂ) * exp ((σ.sphAngleTwoAtOne z : ℂ) * I) := by
  have hn : ‖σ.sphBridgeTwo z - ((3 / 2 : ℝ) : ℂ)‖ = σ.sphModOne z := by
    push_cast
    exact (norm_sphBridgeTwo hs hz).1
  have hsq := EuclidShape.polar_of_norm_sub (σ.sphBridgeTwo z) ((3 / 2 : ℝ) : ℂ) (by simp) hn
  rw [ofReal_re] at hsq
  exact EuclidShape.eq_of_polar (negHalfArg_polar (sphModOne_pos hs z) hpos hsq)

theorem sphBridgeTwo_eq_polar_two {z : ℂ} (hz : z ∈ σ.sphDomTwo)
    (hpos : 0 < σ.sphModTwo z + ((σ.sphBridgeTwo z).re + 3 / 2)) :
    σ.sphBridgeTwo z = ((-(3 / 2) : ℝ) : ℂ) + (σ.sphModTwo z : ℂ) *
      exp ((σ.sphAngleTwoAtTwo z : ℂ) * I) := by
  have hn : ‖σ.sphBridgeTwo z - ((-(3 / 2) : ℝ) : ℂ)‖ = σ.sphModTwo z := by
    push_cast
    rw [sub_neg_eq_add]
    exact (norm_sphBridgeTwo hs hz).2
  have hsq := EuclidShape.polar_of_norm_sub (σ.sphBridgeTwo z) ((-(3 / 2) : ℝ) : ℂ) (by simp) hn
  rw [ofReal_re, sub_neg_eq_add] at hsq
  exact EuclidShape.eq_of_polar_add (halfArg_polar (sphModTwo_pos hs z) hpos hsq)

theorem sphBridgeZero_eq_polar_two {z : ℂ} (hz : z ∈ σ.sphDomZero)
    (hpos : 0 < σ.sphModTwo z - ((σ.sphBridgeZero z).re + 3 / 2)) :
    σ.sphBridgeZero z = ((-(3 / 2) : ℝ) : ℂ) + (σ.sphModTwo z : ℂ) *
      exp ((σ.sphAngleZeroAtTwo z : ℂ) * I) := by
  have hn : ‖σ.sphBridgeZero z - ((-(3 / 2) : ℝ) : ℂ)‖ = σ.sphModTwo z := by
    push_cast
    rw [sub_neg_eq_add]
    exact (norm_sphBridgeZero hs hz).2
  have hsq := EuclidShape.polar_of_norm_sub (σ.sphBridgeZero z) ((-(3 / 2) : ℝ) : ℂ) (by simp) hn
  rw [ofReal_re, sub_neg_eq_add] at hsq
  exact EuclidShape.eq_of_polar_add (negHalfArg_polar (sphModTwo_pos hs z) hpos hsq)

theorem sphBridgeOne_eq_polar_three {z : ℂ} (hz : z ∈ σ.sphDomOne)
    (hpos : 0 < σ.sphModThree z + (σ.sphBridgeOne z).re) :
    σ.sphBridgeOne z = ((0 : ℝ) : ℂ) + (σ.sphModThree z : ℂ) *
      exp ((σ.sphAngleOneAtThree z : ℂ) * I) := by
  have hn : ‖σ.sphBridgeOne z - ((0 : ℝ) : ℂ)‖ = σ.sphModThree z := by
    push_cast
    rw [sub_zero]
    exact (norm_sphBridgeOne hs hz).1
  have hsq := EuclidShape.polar_of_norm_sub (σ.sphBridgeOne z) ((0 : ℝ) : ℂ) (by simp) hn
  rw [ofReal_re, sub_zero] at hsq
  exact EuclidShape.eq_of_polar_zero
    (halfArg_polar (sphModThree_pos (sphCanon_bounds_one hs hz).2) hpos hsq)

theorem sphBridgeZero_eq_polar_three {z : ℂ} (hz : z ∈ σ.sphDomZero)
    (hpos : 0 < σ.sphModThree z - (σ.sphBridgeZero z).re) :
    σ.sphBridgeZero z = ((0 : ℝ) : ℂ) + (σ.sphModThree z : ℂ) *
      exp ((σ.sphAngleZeroAtThree z : ℂ) * I) := by
  have hn : ‖σ.sphBridgeZero z - ((0 : ℝ) : ℂ)‖ = σ.sphModThree z := by
    push_cast
    rw [sub_zero]
    exact (norm_sphBridgeZero hs hz).1
  have hsq := EuclidShape.polar_of_norm_sub (σ.sphBridgeZero z) ((0 : ℝ) : ℂ) (by simp) hn
  rw [ofReal_re, sub_zero] at hsq
  exact EuclidShape.eq_of_polar_zero
    (negHalfArg_polar (sphModThree_pos (sphCanon_bounds_zero hs hz).2) hpos hsq)

theorem sphAngleOneAtOne_le_sphAngleTwoAtOne {z : ℂ} (hz1 : z ∈ σ.sphDomOne)
    (hz2 : z ∈ σ.sphDomTwo) (hpos1 : 0 < σ.sphModOne z + ((σ.sphBridgeOne z).re - 3 / 2))
    (hpos2 : 0 < σ.sphModOne z - ((σ.sphBridgeTwo z).re - 3 / 2))
    (hw1 : 0 ≤ σ.wallSide 1 z) (hw2 : 0 ≤ σ.sphSideTwo z)
    (hre : (σ.sphBridgeTwo z).re ≤ (σ.sphBridgeOne z).re) :
    σ.sphAngleOneAtOne z ≤ σ.sphAngleTwoAtOne z := by
  have hn1 := EuclidShape.polar_of_norm_sub (σ.sphBridgeOne z) (3 / 2) (by simp)
    (norm_sphBridgeOne hs hz1).2
  have hn2 := EuclidShape.polar_of_norm_sub (σ.sphBridgeTwo z) (3 / 2) (by simp)
    (norm_sphBridgeTwo hs hz2).1
  simp only [div_ofNat_re, Complex.re_ofNat] at hn1 hn2
  have hI1 : 0 ≤ (σ.sphBridgeOne z).im := by
    rw [sphBridgeOne, twoCircle_im]
    have := Real.sqrt_nonneg (σ.sphCofBridgeOne z)
    positivity
  have hI2 : 0 ≤ (σ.sphBridgeTwo z).im := by
    rw [sphBridgeTwo, twoCircle_im]
    have := Real.sqrt_nonneg (σ.sphCofBridgeTwo z)
    positivity
  exact EuclidShape.halfArg_le_negHalfArg (sphModOne_pos hs z) hpos1 hpos2 hn1 hn2 hI1 hI2
    (by linarith)

theorem sphAngleTwoAtTwo_le_sphAngleZeroAtTwo {z : ℂ} (hz2 : z ∈ σ.sphDomTwo)
    (hz0 : z ∈ σ.sphDomZero) (hpos2 : 0 < σ.sphModTwo z + ((σ.sphBridgeTwo z).re + 3 / 2))
    (hpos0 : 0 < σ.sphModTwo z - ((σ.sphBridgeZero z).re + 3 / 2))
    (hw2 : 0 ≤ σ.sphSideTwo z) (hw0 : 0 ≤ σ.wallSide 0 z)
    (hre : (σ.sphBridgeZero z).re ≤ (σ.sphBridgeTwo z).re) :
    σ.sphAngleTwoAtTwo z ≤ σ.sphAngleZeroAtTwo z := by
  have e2 : ‖σ.sphBridgeTwo z - -(3 / 2)‖ = σ.sphModTwo z := by
    rw [sub_neg_eq_add]; exact (norm_sphBridgeTwo hs hz2).2
  have e0 : ‖σ.sphBridgeZero z - -(3 / 2)‖ = σ.sphModTwo z := by
    rw [sub_neg_eq_add]; exact (norm_sphBridgeZero hs hz0).2
  have hn2 := EuclidShape.polar_of_norm_sub (σ.sphBridgeTwo z) (-(3 / 2)) (by simp) e2
  have hn0 := EuclidShape.polar_of_norm_sub (σ.sphBridgeZero z) (-(3 / 2)) (by simp) e0
  simp only [neg_re, div_ofNat_re, Complex.re_ofNat, sub_neg_eq_add] at hn2 hn0
  have hI2 : 0 ≤ (σ.sphBridgeTwo z).im := by
    rw [sphBridgeTwo, twoCircle_im]
    have := Real.sqrt_nonneg (σ.sphCofBridgeTwo z)
    positivity
  have hI0 : 0 ≤ (σ.sphBridgeZero z).im := by
    rw [sphBridgeZero, twoCircle_im]
    have := Real.sqrt_nonneg (σ.sphCofBridgeZero z)
    positivity
  exact EuclidShape.halfArg_le_negHalfArg (sphModTwo_pos hs z) hpos2 hpos0 hn2 hn0 hI2 hI0
    (by linarith)

theorem sphAngleOneAtThree_le_sphAngleZeroAtThree {z : ℂ} (hz1 : z ∈ σ.sphDomOne)
    (hz0 : z ∈ σ.sphDomZero) (hpos1 : 0 < σ.sphModThree z + (σ.sphBridgeOne z).re)
    (hpos0 : 0 < σ.sphModThree z - (σ.sphBridgeZero z).re)
    (hw1 : 0 ≤ σ.wallSide 1 z) (hw0 : 0 ≤ σ.wallSide 0 z)
    (hre : (σ.sphBridgeZero z).re ≤ (σ.sphBridgeOne z).re) :
    σ.sphAngleOneAtThree z ≤ σ.sphAngleZeroAtThree z := by
  have e1 : ‖σ.sphBridgeOne z - 0‖ = σ.sphModThree z := by
    rw [sub_zero]; exact (norm_sphBridgeOne hs hz1).1
  have e0 : ‖σ.sphBridgeZero z - 0‖ = σ.sphModThree z := by
    rw [sub_zero]; exact (norm_sphBridgeZero hs hz0).1
  have hn1 := EuclidShape.polar_of_norm_sub (σ.sphBridgeOne z) 0 (by simp) e1
  have hn0 := EuclidShape.polar_of_norm_sub (σ.sphBridgeZero z) 0 (by simp) e0
  simp only [zero_re, sub_zero] at hn1 hn0
  have hI1 : 0 ≤ (σ.sphBridgeOne z).im := by
    rw [sphBridgeOne, twoCircle_im]
    have := Real.sqrt_nonneg (σ.sphCofBridgeOne z)
    positivity
  have hI0 : 0 ≤ (σ.sphBridgeZero z).im := by
    rw [sphBridgeZero, twoCircle_im]
    have := Real.sqrt_nonneg (σ.sphCofBridgeZero z)
    positivity
  exact EuclidShape.halfArg_le_negHalfArg (sphModThree_pos (sphCanon_bounds_one hs hz1).2)
    hpos1 hpos0 hn1 hn0 hI1 hI0 hre

theorem contDiffAt_rotOne_sph {z : ℂ} (h : 1 + conj σ.vertexOne * z ≠ 0) :
    ContDiffAt ℝ ∞ σ.rotOne z := by
  have e : σ.rotOne = fun w => -exp (-((σ.θ₃ : ℂ) * I)) * sphMoeb σ.vertexOne w :=
    funext (rotOne_eq_mul_sph hs)
  rw [e]
  exact contDiffAt_const.mul (contDiffAt_sphMoeb h)

theorem contDiffAt_sphPsiOne {z : ℂ} (h : 1 + conj σ.vertexOne * z ≠ 0)
    (hψ : 0 < ‖σ.rotOne z‖ + (σ.rotOne z).re) : ContDiffAt ℝ ∞ σ.sphPsiOne z :=
  EuclidShape.contDiffAt_discAngle_comp (contDiffAt_rotOne_sph hs h) hψ

theorem contDiffAt_sphPsiTwo {z : ℂ} (h : 1 + σ.vertexTwo * z ≠ 0)
    (hψ : 0 < ‖σ.rotTwo z‖ + (σ.rotTwo z).re) : ContDiffAt ℝ ∞ σ.sphPsiTwo z :=
  EuclidShape.contDiffAt_discAngle_comp (contDiffAt_rotTwo_sph hs h) hψ

theorem hasDerivAt_sphPsiOne_sphCirc {z : ℂ} (h : 1 + conj σ.vertexOne * z ≠ 0)
    (hψ : 0 < ‖σ.rotOne z‖ + (σ.rotOne z).re) :
    HasDerivAt (fun t => σ.sphPsiOne (sphCirc σ.vertexOne z t)) 1 0 := by
  refine (EuclidShape.hasDerivAt_discAngle_mul_exp hψ).congr_of_eventuallyEq ?_
  filter_upwards [eventually_rotOne_sphCirc hs h] with t ht
  rw [sphPsiOne, ht]

theorem hasDerivAt_sphPsiTwo_sphCirc {z : ℂ} (h : 1 + σ.vertexTwo * z ≠ 0)
    (hψ : 0 < ‖σ.rotTwo z‖ + (σ.rotTwo z).re) :
    HasDerivAt (fun t => σ.sphPsiTwo (sphCirc σ.vertexTwo z t)) 1 0 := by
  refine (EuclidShape.hasDerivAt_discAngle_mul_exp hψ).congr_of_eventuallyEq ?_
  filter_upwards [eventually_rotTwo_sphCirc hs h] with t ht
  rw [sphPsiTwo, ht]

omit hs in
theorem hasDerivAt_sphPsiThree_sphCirc {z : ℂ} (hψ : 0 < ‖z‖ + z.re) :
    HasDerivAt (fun t => discAngle (sphCirc 0 z t)) 1 0 := by
  have e : (fun t => discAngle (sphCirc 0 z t)) =
      fun t : ℝ => discAngle (z * exp ((t : ℂ) * I)) := by
    funext t
    rw [sphCirc_center_zero]
  rw [e]
  exact EuclidShape.hasDerivAt_discAngle_mul_exp hψ

theorem rotOne_refl_one_sph (z : ℂ) : σ.rotOne (σ.refl 1 z) = conj (σ.rotOne z) := by
  rw [rotOne_eq_mul_sph hs, rotOne_eq_mul_sph hs, sphMoeb_vertexOne_refl_one, map_mul,
    map_neg, conj_exp_neg_sph, exp_two_mul_eq_sph]
  have := exp_mul_exp_neg_sph σ.θ₃
  linear_combination (-(exp ((σ.θ₃ : ℂ) * I) * conj (sphMoeb σ.vertexOne z))) * this

theorem rotTwo_refl_zero_sph (z : ℂ) :
    σ.rotTwo (σ.refl 0 z) = exp (2 * (σ.θ₂ : ℂ) * I) * conj (σ.rotTwo z) := by
  rw [rotTwo_eq_mul_sph hs, rotTwo_eq_mul_sph hs, sphMoeb_vertexTwo_refl_zero, map_mul,
    map_neg, conj_exp_ofReal_mul_I_sph, exp_two_mul_eq_sph]
  have := exp_mul_exp_neg_sph σ.θ₂
  linear_combination (exp ((σ.θ₂ : ℂ) * I) * conj (sphMoeb σ.vertexTwo z)) * this

theorem sphPsiOne_refl_one (z : ℂ) : σ.sphPsiOne (σ.refl 1 z) = -σ.sphPsiOne z := by
  rw [sphPsiOne, rotOne_refl_one_sph hs, EuclidShape.discAngle_conj, sphPsiOne]

theorem sphPsiTwo_refl_two {z : ℂ} (hz : z ∈ σ.reflChart 2) :
    σ.sphPsiTwo (σ.refl 2 z) = -σ.sphPsiTwo z := by
  rw [sphPsiTwo, rotTwo_refl_two_sph hs hz, EuclidShape.discAngle_conj, sphPsiTwo]

theorem sphPsiTwo_refl_zero {z : ℂ} (h : 0 < ‖σ.rotTwo z‖ + (σ.rotTwo z).re)
    (h1 : -Real.pi < 2 * σ.θ₂ - σ.sphPsiTwo z) (h2 : 2 * σ.θ₂ - σ.sphPsiTwo z < Real.pi) :
    σ.sphPsiTwo (σ.refl 0 z) = 2 * σ.θ₂ - σ.sphPsiTwo z := by
  rw [sphPsiTwo, rotTwo_refl_zero_sph hs, EuclidShape.two_mul_ofReal_mul_I]
  exact EuclidShape.discAngle_exp_mul_conj h h1 h2

omit hs in
theorem sphPsiThree_refl_zero (z : ℂ) : discAngle (σ.refl 0 z) = -discAngle z :=
  EuclidShape.discAngle_conj z

omit hs in
theorem sphPsiThree_refl_one {z : ℂ} (h : 0 < ‖z‖ + z.re)
    (h1 : -Real.pi < 2 * σ.θ₃ - discAngle z) (h2 : 2 * σ.θ₃ - discAngle z < Real.pi) :
    discAngle (σ.refl 1 z) = 2 * σ.θ₃ - discAngle z := by
  change discAngle (exp (2 * (σ.θ₃ : ℂ) * I) * conj z) = _
  rw [EuclidShape.two_mul_ofReal_mul_I]
  exact EuclidShape.discAngle_exp_mul_conj h h1 h2

theorem sphAngleOneAtOne_refl_one (z : ℂ) :
    σ.sphAngleOneAtOne (σ.refl 1 z) = -σ.sphAngleOneAtOne z := by
  have hm : σ.sphModOne (σ.refl 1 z) = σ.sphModOne z := by
    rw [sphModOne, sphModOne, sphCanon_refl_one_zero hs]
  rw [sphAngleOneAtOne, sphAngleOneAtOne, hm, sphBridgeOne_refl_one hs, conj_re, conj_im,
    halfArg_neg]

theorem sphAngleOneAtThree_refl_one (z : ℂ) :
    σ.sphAngleOneAtThree (σ.refl 1 z) = -σ.sphAngleOneAtThree z := by
  have hm : σ.sphModThree (σ.refl 1 z) = σ.sphModThree z := by
    rw [sphModThree, sphModThree, sphCanon_refl_one_two]
  rw [sphAngleOneAtThree, sphAngleOneAtThree, hm, sphBridgeOne_refl_one hs, conj_re, conj_im,
    halfArg_neg]

theorem sphAngleTwoAtOne_refl_two {z : ℂ} (hz : z ∈ σ.reflChart 2)
    (h1 : 1 + conj σ.vertexOne * z ≠ 0) :
    σ.sphAngleTwoAtOne (σ.refl 2 z) = 2 * Real.pi - σ.sphAngleTwoAtOne z := by
  have hm : σ.sphModOne (σ.refl 2 z) = σ.sphModOne z := by
    rw [sphModOne, sphModOne, sphCanon_refl_two_zero hs hz h1]
  rw [sphAngleTwoAtOne, sphAngleTwoAtOne, hm, sphBridgeTwo_refl_two hs hz h1, conj_re, conj_im,
    negHalfArg_neg]

theorem sphAngleTwoAtTwo_refl_two {z : ℂ} (hz : z ∈ σ.reflChart 2)
    (h1 : 1 + conj σ.vertexOne * z ≠ 0) :
    σ.sphAngleTwoAtTwo (σ.refl 2 z) = -σ.sphAngleTwoAtTwo z := by
  have hm : σ.sphModTwo (σ.refl 2 z) = σ.sphModTwo z := by
    rw [sphModTwo, sphModTwo, sphCanon_refl_two_one hs hz]
  rw [sphAngleTwoAtTwo, sphAngleTwoAtTwo, hm, sphBridgeTwo_refl_two hs hz h1, conj_re, conj_im,
    halfArg_neg]

theorem sphAngleZeroAtTwo_refl_zero (z : ℂ) :
    σ.sphAngleZeroAtTwo (σ.refl 0 z) = 2 * Real.pi - σ.sphAngleZeroAtTwo z := by
  have hm : σ.sphModTwo (σ.refl 0 z) = σ.sphModTwo z := by
    rw [sphModTwo, sphModTwo, sphCanon_refl_zero_one hs]
  rw [sphAngleZeroAtTwo, sphAngleZeroAtTwo, hm, sphBridgeZero_refl_zero hs, conj_re, conj_im,
    negHalfArg_neg]

theorem sphAngleZeroAtThree_refl_zero (z : ℂ) :
    σ.sphAngleZeroAtThree (σ.refl 0 z) = 2 * Real.pi - σ.sphAngleZeroAtThree z := by
  have hm : σ.sphModThree (σ.refl 0 z) = σ.sphModThree z := by
    rw [sphModThree, sphModThree, sphCanon_refl_zero_two]
  rw [sphAngleZeroAtThree, sphAngleZeroAtThree, hm, sphBridgeZero_refl_zero hs, conj_re, conj_im,
    negHalfArg_neg]

end Spherical

end CompactShape

end GC.Seifert
