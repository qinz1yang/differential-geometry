import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldSphValid

/-!
# The open pieces of the spherical fold and the good set

Lane CF-S3, tier 3, curvature `+4` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §5, review 23 §6.1: a gluing certificate made of
open sets on which the fold is given by one smooth formula with positive Jacobian).

The three bridges are polar maps about `3/2`, `3/2`, `-3/2` with a modulus
`3/2 + κ T(‖sphMoeb v ·‖)` depending on the chordal distance to one vertex only, so the polar
Jacobian formula along the Möbius circles `sphCirc v z` gives positive Jacobians
(`det_polar_sph_bridge`, `det_fderiv_sphBridgeOne_pos`, `det_fderiv_sphBridgeTwo_pos`,
`det_fderiv_sphBridgeZero_pos`).

Nine open pieces carry one formula each (`sphPieceApexOne`, …, `sphPieceJunctionTwo`). Each piece
contains the chart conditions of the coordinates it uses and the strict negations of the earlier
branches of `sphPreFold` that must not fire, so `sphPreFold` equals the formula on the piece
(`sphPreFold_eq_*`); the formula is smooth there with positive Jacobian off `v₁, v₂`
(`sphGood_*`). The angle orders of the corners come from the signs of the real parts of the bridge
points relative to the centre (`halfArg_lt_negHalfArg_of_re`). The union `sphGoodSet` is open and
`sphPreFold` is smooth on it with positive Jacobian off `v₁, v₂` (`sphGood_sphPreFold`,
`contDiffAt_sphPreFold_of_good`).
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

theorem det_polar_sph_bridge {c τ : ℝ} {a z : ℂ} {Θ : ℂ → ℝ} {g : ℂ → ℂ} (hτ : 0 ≤ τ)
    (ha : 1 + conj a * z ≠ 0) (hne : sphMoeb a z ≠ 0)
    (hev : g =ᶠ[𝓝 z] fun u => (c : ℂ) +
      ((3 / 2 + compactProfileSlope * sphCanonF τ ‖sphMoeb a u‖ : ℝ) : ℂ) *
        exp ((Θ u : ℂ) * I))
    (hS : 0 < 3 / 2 + compactProfileSlope * sphCanonF τ ‖sphMoeb a z‖)
    (hΘ : DifferentiableAt ℝ Θ z) {D : ℝ} (hD : 0 < D)
    (hΘγ : HasDerivAt (fun t => Θ (sphCirc a z t)) D 0) :
    0 < (fderiv ℝ g z).det := by
  rw [hev.fderiv_eq]
  have hd0 : 0 ≤ ‖sphMoeb a z‖ := norm_nonneg _
  have hden : 0 < 1 + ‖sphMoeb a z‖ * τ := by
    have := mul_nonneg hd0 hτ
    linarith
  have hSd : HasDerivAt (fun d : ℝ => 3 / 2 + compactProfileSlope * sphCanonF τ d)
      (compactProfileSlope * ((1 + τ ^ 2) / (1 + ‖sphMoeb a z‖ * τ) ^ 2)) ‖sphMoeb a z‖ :=
    ((hasDerivAt_sphCanonF_id hden.ne').const_mul compactProfileSlope).const_add (3 / 2)
  have hρ : DifferentiableAt ℝ (fun u => ‖sphMoeb a u‖) z :=
    ((contDiffAt_sphMoeb ha).norm ℝ hne).differentiableAt (by simp)
  have hγ : HasDerivAt (sphCirc a z) (sphRayDir a z * I) 0 := by
    have := hasDerivAt_sphCirc ha
    rwa [sphCirc_deriv_eq] at this
  have key := det_fderiv_polar (c := (c : ℂ))
    (S := fun d : ℝ => 3 / 2 + compactProfileSlope * sphCanonF τ d)
    (ρ := fun u => ‖sphMoeb a u‖) (Θ := Θ) (N := sphRayDir a z) hSd hρ hΘ hγ (sphCirc_zero ha)
    (eventually_norm_sphMoeb_sphCirc ha) hΘγ (hasDerivAt_norm_sphMoeb_ray ha hne)
    (EuclidShape.hasDerivAt_comp_ray hΘ)
  rw [EuclidShape.cross_mul_I] at key
  have hN : sphRayDir a z ≠ 0 := by
    intro h0
    have := sphRayDir_mul (a := a) ha
    rw [h0, mul_zero] at this
    exact hne this.symm
  have hm := norm_pos_iff.2 hne
  have hκ : (0 : ℝ) < compactProfileSlope := by unfold compactProfileSlope; norm_num
  have hS' : 0 < compactProfileSlope * ((1 + τ ^ 2) / (1 + ‖sphMoeb a z‖ * τ) ^ 2) :=
    mul_pos hκ (div_pos (by positivity) (by positivity))
  exact EuclidShape.det_pos_of_polar (by positivity) key
    (mul_pos (mul_pos (mul_pos hS hS') hD) hm)

namespace CompactShape

variable {σ : CompactShape}

def sphPieceApexOne (σ : CompactShape) : Set ℂ :=
  {z | 1 + conj σ.vertexOne * z ≠ 0 ∧ ‖σ.rotOne z‖ < σ.sphGermRadius}

def sphPieceApexTwo (σ : CompactShape) : Set ℂ :=
  {z | 1 + σ.vertexTwo * z ≠ 0 ∧ ‖σ.rotTwo z‖ < σ.sphGermRadius ∧
    1 + conj σ.vertexOne * z ≠ 0 ∧ σ.sphGermRadius < ‖σ.rotOne z‖}

def sphPieceOuter (σ : CompactShape) : Set ℂ :=
  {z | 0 < ‖z‖ ∧ ‖z‖ < σ.sphOuterGermRadius ∧ 1 + conj σ.vertexOne * z ≠ 0 ∧
    σ.sphGermRadius < ‖σ.rotOne z‖ ∧ 1 + σ.vertexTwo * z ≠ 0 ∧ σ.sphGermRadius < ‖σ.rotTwo z‖}

def sphValidOne (σ : CompactShape) : Set ℂ :=
  {z | z ∈ σ.sphDomOne ∧ z ∈ σ.sphDomTwo ∧ 0 < ‖σ.rotOne z‖ + (σ.rotOne z).re ∧
    3 / 2 < (σ.sphBridgeOne z).re ∧ (σ.sphBridgeTwo z).re < 3 / 2 ∧
    (((σ.rotTwo z - σ.sphTOneTwo) * (1 + σ.sphTOneTwo * σ.rotTwo z)).re < 0 ∨
      σ.sphSwitchTop < σ.sphSideTwo z ∨ σ.sphSideTwo z < σ.sphLensWidth)}

def sphPieceCornerOne (σ : CompactShape) : Set ℂ :=
  {z | σ.sphGermRadius / 2 < ‖σ.rotOne z‖ ∧ ‖σ.rotOne z‖ < σ.sphCornerRad 0 ∧
    σ.sphGermRadius < ‖σ.rotTwo z‖ ∧ σ.sphOuterGermRadius < ‖z‖} ∩ σ.sphValidOne

def sphValidTwo (σ : CompactShape) : Set ℂ :=
  {z | z ∈ σ.sphDomTwo ∧ z ∈ σ.sphDomZero ∧ -(3 / 2) < (σ.sphBridgeTwo z).re ∧
    (σ.sphBridgeZero z).re < -(3 / 2) ∧
    (0 < (σ.rotTwo z).re ∨ σ.sphSwitchTop < σ.sphSideTwo z ∨ σ.sphSideTwo z < σ.sphLensWidth)}

def sphPieceCornerTwo (σ : CompactShape) : Set ℂ :=
  {z | σ.sphGermRadius / 2 < ‖σ.rotTwo z‖ ∧ ‖σ.rotTwo z‖ < σ.sphCornerRad 1 ∧
    σ.sphCornerRad 0 < ‖σ.rotOne z‖ ∧ σ.sphOuterGermRadius < ‖z‖} ∩ σ.sphValidTwo

def sphValidLens (σ : CompactShape) : Set ℂ :=
  {z | z ∈ σ.sphDomTwo ∧ -(3 / 2) < (σ.sphBridgeTwo z).re ∧ (σ.sphBridgeTwo z).re < 3 / 2}

def sphPieceLens (σ : CompactShape) : Set ℂ :=
  {z | σ.sphBlendEnd < ‖σ.rotOne z‖ ∧ σ.sphBlendEnd < ‖σ.rotTwo z‖ ∧
    |σ.sphSideTwo z| < σ.sphLensWidth ∧ σ.sphOuterGermRadius < ‖z‖} ∩ σ.sphValidLens

def sphValidThree (σ : CompactShape) : Set ℂ :=
  {z | z ∈ σ.sphDomOne ∧ z ∈ σ.sphDomZero ∧ 0 < (σ.sphBridgeOne z).re ∧
    (σ.sphBridgeZero z).re < 0 ∧
    ((0 < σ.wallSide 0 z ∧ 0 < σ.wallSide 1 z) ∨ 1 < σ.sphFoldBlend z ∨ σ.sphFoldBlend z < -1)}

def sphPieceCornerThree (σ : CompactShape) : Set ℂ :=
  {z | σ.sphCornerRad 0 < ‖σ.rotOne z‖ ∧ σ.sphCornerRad 1 < ‖σ.rotTwo z‖ ∧
    σ.sphLensWidth < |σ.sphSideTwo z| ∧ σ.sphOuterGermRadius / 2 < ‖z‖} ∩ σ.sphValidThree

def sphValidJunctionOne (σ : CompactShape) : Set ℂ :=
  {z | z ∈ σ.sphDomOne ∧ 0 < ‖z‖ + z.re ∧ 1 + σ.vertexTwo * z ≠ 0 ∧
    3 / 2 < (σ.sphBridgeOne z).re}

def sphPieceJunctionOne (σ : CompactShape) : Set ℂ :=
  {z | σ.sphBlendEnd < ‖σ.rotOne z‖ ∧ σ.sphCornerRad 1 < ‖σ.rotTwo z‖ ∧
    σ.sphSwitchTop < σ.sphSideTwo z ∧ σ.sphOuterBlendEnd < ‖z‖ ∧ 1 < σ.sphFoldBlend z} ∩
    σ.sphValidJunctionOne

def sphValidJunctionTwo (σ : CompactShape) : Set ℂ :=
  {z | z ∈ σ.sphDomZero ∧ 1 + conj σ.vertexOne * z ≠ 0 ∧ (σ.sphBridgeZero z).re < -(3 / 2)}

def sphPieceJunctionTwo (σ : CompactShape) : Set ℂ :=
  {z | σ.sphBlendEnd < ‖σ.rotTwo z‖ ∧ σ.sphCornerRad 0 < ‖σ.rotOne z‖ ∧
    σ.sphSwitchTop < σ.sphSideTwo z ∧ σ.sphOuterBlendEnd < ‖z‖ ∧ σ.sphFoldBlend z < -1} ∩
    σ.sphValidJunctionTwo

def sphGoodSet (σ : CompactShape) : Set ℂ :=
  σ.sphPieceApexOne ∪ σ.sphPieceApexTwo ∪ σ.sphPieceOuter ∪ σ.sphPieceCornerOne ∪
    σ.sphPieceCornerTwo ∪ σ.sphPieceLens ∪ σ.sphPieceCornerThree ∪ σ.sphPieceJunctionOne ∪
      σ.sphPieceJunctionTwo

theorem ev_chartOne_sph {z : ℂ} (h : 1 + conj σ.vertexOne * z ≠ 0) :
    ∀ᶠ u in 𝓝 z, 1 + conj σ.vertexOne * u ≠ 0 :=
  (continuousAt_const.add (continuousAt_const.mul continuousAt_id)).eventually_ne h

theorem ev_chartTwo_sph {z : ℂ} (h : 1 + σ.vertexTwo * z ≠ 0) :
    ∀ᶠ u in 𝓝 z, 1 + σ.vertexTwo * u ≠ 0 :=
  (continuousAt_const.add (continuousAt_const.mul continuousAt_id)).eventually_ne h

section Spherical

variable (hs : σ.curv = .spherical)
include hs

theorem sphGoodConsts :
    σ.sphBlendEnd < σ.sphCornerRad 0 ∧ σ.sphBlendEnd < σ.sphCornerRad 1 ∧
      σ.sphSwitchTop < σ.sphGermRadius ∧ σ.sphOuterBlendEnd < σ.sphTau 2 ∧
      σ.sphGermRadius < σ.sphBlendEnd := by
  obtain ⟨c0, -⟩ := sphCornerRad_bounds hs 0
  obtain ⟨c1, -⟩ := sphCornerRad_bounds hs 1
  have t0 := sphTau_pos hs 0
  have t1 := sphTau_pos hs 1
  have t2 := sphTau_pos hs 2
  have m0 : σ.sphInnerScale ≤ σ.sphTau 0 := min_le_left _ _
  have m1 : σ.sphInnerScale ≤ σ.sphTau 1 := min_le_right _ _
  have hm : 0 < σ.sphInnerScale := lt_min t0 t1
  have s0 := sphScale_le_tau hs 0
  have s1 := sphScale_le_tau hs 1
  have hsm : σ.sphScale ≤ σ.sphInnerScale / 16 := by
    rcases min_choice (σ.sphTau 0) (σ.sphTau 1) with h | h
    · change σ.sphScale ≤ min (σ.sphTau 0) (σ.sphTau 1) / 16
      rw [h]
      exact s0
    · change σ.sphScale ≤ min (σ.sphTau 0) (σ.sphTau 1) / 16
      rw [h]
      exact s1
  unfold sphBlendEnd sphSwitchTop sphGermRadius sphOuterBlendEnd
  refine ⟨by linarith, by linarith, by linarith, by linarith, by linarith⟩

theorem sq_sphBridgeOne_one {z : ℂ} (hz : z ∈ σ.sphDomOne) :
    ((σ.sphBridgeOne z).re - 3 / 2) ^ 2 + (σ.sphBridgeOne z).im ^ 2 = σ.sphModOne z ^ 2 := by
  have h := EuclidShape.polar_of_norm_sub (σ.sphBridgeOne z) (3 / 2) (by simp)
    (norm_sphBridgeOne hs hz).2
  simpa using h

theorem sq_sphBridgeTwo_one {z : ℂ} (hz : z ∈ σ.sphDomTwo) :
    ((σ.sphBridgeTwo z).re - 3 / 2) ^ 2 + (σ.sphBridgeTwo z).im ^ 2 = σ.sphModOne z ^ 2 := by
  have h := EuclidShape.polar_of_norm_sub (σ.sphBridgeTwo z) (3 / 2) (by simp)
    (norm_sphBridgeTwo hs hz).1
  simpa using h

theorem sq_sphBridgeTwo_two {z : ℂ} (hz : z ∈ σ.sphDomTwo) :
    ((σ.sphBridgeTwo z).re + 3 / 2) ^ 2 + (σ.sphBridgeTwo z).im ^ 2 = σ.sphModTwo z ^ 2 := by
  have e : ‖σ.sphBridgeTwo z - -(3 / 2)‖ = σ.sphModTwo z := by
    rw [sub_neg_eq_add]; exact (norm_sphBridgeTwo hs hz).2
  have h := EuclidShape.polar_of_norm_sub (σ.sphBridgeTwo z) (-(3 / 2)) (by simp) e
  simpa using h

theorem sq_sphBridgeZero_two {z : ℂ} (hz : z ∈ σ.sphDomZero) :
    ((σ.sphBridgeZero z).re + 3 / 2) ^ 2 + (σ.sphBridgeZero z).im ^ 2 = σ.sphModTwo z ^ 2 := by
  have e : ‖σ.sphBridgeZero z - -(3 / 2)‖ = σ.sphModTwo z := by
    rw [sub_neg_eq_add]; exact (norm_sphBridgeZero hs hz).2
  have h := EuclidShape.polar_of_norm_sub (σ.sphBridgeZero z) (-(3 / 2)) (by simp) e
  simpa using h

theorem sq_sphBridgeOne_three {z : ℂ} (hz : z ∈ σ.sphDomOne) :
    (σ.sphBridgeOne z).re ^ 2 + (σ.sphBridgeOne z).im ^ 2 = σ.sphModThree z ^ 2 := by
  have e : ‖σ.sphBridgeOne z - 0‖ = σ.sphModThree z := by
    rw [sub_zero]; exact (norm_sphBridgeOne hs hz).1
  have h := EuclidShape.polar_of_norm_sub (σ.sphBridgeOne z) 0 (by simp) e
  simpa using h

theorem sq_sphBridgeZero_three {z : ℂ} (hz : z ∈ σ.sphDomZero) :
    (σ.sphBridgeZero z).re ^ 2 + (σ.sphBridgeZero z).im ^ 2 = σ.sphModThree z ^ 2 := by
  have e : ‖σ.sphBridgeZero z - 0‖ = σ.sphModThree z := by
    rw [sub_zero]; exact (norm_sphBridgeZero hs hz).1
  have h := EuclidShape.polar_of_norm_sub (σ.sphBridgeZero z) 0 (by simp) e
  simpa using h

theorem det_fderiv_sphBridgeTwo_pos {z : ℂ} (hz : z ∈ σ.sphDomTwo)
    (hpos : 0 < σ.sphModOne z - ((σ.sphBridgeTwo z).re - 3 / 2)) :
    0 < (fderiv ℝ σ.sphBridgeTwo z).det := by
  have hv1 : 1 + conj σ.vertexOne * z ≠ 0 := hz.2.1
  have hne := sphMoeb_vertexOne_ne_of_domTwo hs hz
  have hcont : ContinuousAt (fun u => σ.sphModOne u - ((σ.sphBridgeTwo u).re - 3 / 2)) z :=
    ((contDiffAt_sphModOne hs hv1 hne).continuousAt).sub
      ((EuclidShape.contDiffAt_re_comp (contDiffAt_sphBridgeTwo hs hz)).continuousAt.sub
        continuousAt_const)
  have hev : σ.sphBridgeTwo =ᶠ[𝓝 z] fun u => ((3 / 2 : ℝ) : ℂ) +
      ((3 / 2 + compactProfileSlope * sphCanonF (σ.sphTau 0) ‖sphMoeb σ.vertexOne u‖ : ℝ) : ℂ) *
        exp ((σ.sphAngleTwoAtOne u : ℂ) * I) := by
    filter_upwards [EuclidShape.eventually_mem_and_pos (isOpen_sphDomTwo hs) hz hcont hpos] with
      u hu
    rw [sphBridgeTwo_eq_polar_one hs hu.1 hu.2, sphModOne, sphCanon_zero_eq_F hs]
  have hS : 0 < 3 / 2 + compactProfileSlope * sphCanonF (σ.sphTau 0) ‖sphMoeb σ.vertexOne z‖ := by
    have := sphModOne_pos hs z
    rwa [sphModOne, sphCanon_zero_eq_F hs] at this
  obtain ⟨D, hD, hΘγ⟩ := exists_hasDerivAt_sphAngleTwoAtOne hs hz hpos
  exact det_polar_sph_bridge (sphTau_pos hs 0).le hv1 hne hev hS
    ((contDiffAt_sphAngleTwoAtOne hs hz hpos).differentiableAt (by simp)) hD hΘγ

theorem det_fderiv_sphBridgeOne_pos {z : ℂ} (hz : z ∈ σ.sphDomOne)
    (hpos : 0 < σ.sphModOne z + ((σ.sphBridgeOne z).re - 3 / 2)) :
    0 < (fderiv ℝ σ.sphBridgeOne z).det := by
  have hv1 : 1 + conj σ.vertexOne * z ≠ 0 := one_add_conj_vertexOne_ne_of_domOne hz
  have hne := sphMoeb_vertexOne_ne_of_domOne hs hz
  have hcont : ContinuousAt (fun u => σ.sphModOne u + ((σ.sphBridgeOne u).re - 3 / 2)) z :=
    ((contDiffAt_sphModOne hs hv1 hne).continuousAt).add
      ((EuclidShape.contDiffAt_re_comp (contDiffAt_sphBridgeOne hs hz)).continuousAt.sub
        continuousAt_const)
  have hev : σ.sphBridgeOne =ᶠ[𝓝 z] fun u => ((3 / 2 : ℝ) : ℂ) +
      ((3 / 2 + compactProfileSlope * sphCanonF (σ.sphTau 0) ‖sphMoeb σ.vertexOne u‖ : ℝ) : ℂ) *
        exp ((σ.sphAngleOneAtOne u : ℂ) * I) := by
    filter_upwards [EuclidShape.eventually_mem_and_pos isOpen_sphDomOne hz hcont hpos] with u hu
    rw [sphBridgeOne_eq_polar_one hs hu.1 hu.2, sphModOne, sphCanon_zero_eq_F hs]
  have hS : 0 < 3 / 2 + compactProfileSlope * sphCanonF (σ.sphTau 0) ‖sphMoeb σ.vertexOne z‖ := by
    have := sphModOne_pos hs z
    rwa [sphModOne, sphCanon_zero_eq_F hs] at this
  obtain ⟨D, hD, hΘγ⟩ := exists_hasDerivAt_sphAngleOneAtOne hs hz hpos
  exact det_polar_sph_bridge (sphTau_pos hs 0).le hv1 hne hev hS
    ((contDiffAt_sphAngleOneAtOne hs hz hpos).differentiableAt (by simp)) hD hΘγ

theorem det_fderiv_sphBridgeZero_pos {z : ℂ} (hz : z ∈ σ.sphDomZero)
    (hpos : 0 < σ.sphModTwo z - ((σ.sphBridgeZero z).re + 3 / 2)) :
    0 < (fderiv ℝ σ.sphBridgeZero z).det := by
  have hv2 : 1 + conj σ.vertexTwo * z ≠ 0 := one_add_vertexTwo_ne_of_domZero hz
  have hne := sphMoeb_vertexTwo_ne_of_domZero hz
  have hcont : ContinuousAt (fun u => σ.sphModTwo u - ((σ.sphBridgeZero u).re + 3 / 2)) z :=
    ((contDiffAt_sphModTwo hs hv2 hne).continuousAt).sub
      ((EuclidShape.contDiffAt_re_comp (contDiffAt_sphBridgeZero hs hz)).continuousAt.add
        continuousAt_const)
  have hev : σ.sphBridgeZero =ᶠ[𝓝 z] fun u => ((-(3 / 2) : ℝ) : ℂ) +
      ((3 / 2 + compactProfileSlope * sphCanonF (σ.sphTau 1) ‖sphMoeb σ.vertexTwo u‖ : ℝ) : ℂ) *
        exp ((σ.sphAngleZeroAtTwo u : ℂ) * I) := by
    filter_upwards [EuclidShape.eventually_mem_and_pos isOpen_sphDomZero hz hcont hpos] with u hu
    rw [sphBridgeZero_eq_polar_two hs hu.1 hu.2, sphModTwo, sphCanon_one_eq_F hs]
  have hS : 0 < 3 / 2 + compactProfileSlope * sphCanonF (σ.sphTau 1) ‖sphMoeb σ.vertexTwo z‖ := by
    have := sphModTwo_pos hs z
    rwa [sphModTwo, sphCanon_one_eq_F hs] at this
  obtain ⟨D, hD, hΘγ⟩ := exists_hasDerivAt_sphAngleZeroAtTwo hs hz hpos
  exact det_polar_sph_bridge (sphTau_pos hs 1).le hv2 hne hev hS
    ((contDiffAt_sphAngleZeroAtTwo hs hz hpos).differentiableAt (by simp)) hD hΘγ

theorem contDiffAt_sphCornerTwo_sph (a b β β' : ℝ) {z : ℂ} (hz2 : z ∈ σ.sphDomTwo)
    (hz0 : z ∈ σ.sphDomZero)
    (hpos2 : 0 < σ.sphModTwo z + ((σ.sphBridgeTwo z).re + 3 / 2))
    (hpos0 : 0 < σ.sphModTwo z - ((σ.sphBridgeZero z).re + 3 / 2)) :
    ContDiffAt ℝ ∞ (σ.sphCornerTwo a b β β') z := by
  have hv2 : 1 + σ.vertexTwo * z ≠ 0 := hz2.1
  have hd := contDiffAt_norm_rotTwo hs hv2 (rotTwo_ne_zero_of_domTwo hz2)
  have hS : ContDiffAt ℝ ∞ (fun u => sphInnerRadial σ.p₂ a b (σ.sphTau 1) ‖σ.rotTwo u‖) z := by
    have hpos : 1 + ‖σ.rotTwo z‖ * σ.sphTau 1 ≠ 0 := by
      have := mul_nonneg (norm_nonneg (σ.rotTwo z)) (sphTau_pos hs 1).le
      linarith
    exact (contDiff_sphInnerRadial_at σ.p₂ a b hpos).comp z hd
  have hΘ := contDiffAt_sphAngleCornerTwo hs a b β β' hz2 hz0 hpos2 hpos0
  have hof : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ)) := ofRealCLM.contDiff
  exact contDiffAt_const.add ((hof.contDiffAt.comp z hS).mul
    (((hof.contDiffAt.comp z hΘ).mul contDiffAt_const).cexp))

theorem contDiffAt_sphCornerThree_sph (a b w δ : ℝ) {z : ℂ} (hz1 : z ∈ σ.sphDomOne)
    (hz0 : z ∈ σ.sphDomZero) (hψ : 0 < ‖z‖ + z.re)
    (hpos1 : 0 < σ.sphModThree z + (σ.sphBridgeOne z).re)
    (hpos0 : 0 < σ.sphModThree z - (σ.sphBridgeZero z).re) :
    ContDiffAt ℝ ∞ (σ.sphCornerThree a b w δ) z := by
  have hz0' := ne_zero_of_domOne hz1
  have hd : ContDiffAt ℝ ∞ (fun u : ℂ => ‖u‖) z := contDiffAt_norm ℝ hz0'
  have hS : ContDiffAt ℝ ∞ (fun u : ℂ => sphOuterRadial σ.p₃ a b (σ.sphTau 2) ‖u‖) z := by
    have hpos : 1 + ‖z‖ * σ.sphTau 2 ≠ 0 := by
      have := mul_nonneg (norm_nonneg z) (sphTau_pos hs 2).le
      linarith
    exact (contDiff_sphOuterRadial_at σ.p₃ a b hpos).comp z hd
  have hΘ := contDiffAt_sphAngleCornerThree hs a b w δ hz1 hz0 hψ hpos1 hpos0
  have hof : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ)) := ofRealCLM.contDiff
  exact contDiffAt_const.add ((hof.contDiffAt.comp z hS).mul
    (((hof.contDiffAt.comp z hΘ).mul contDiffAt_const).cexp))

omit hs in
theorem sphPreFold_eq_apexOne {z : ℂ} (hz : z ∈ σ.sphPieceApexOne) :
    σ.sphPreFold z = σ.sphApexOne z := by
  simp only [sphPreFold, hz.2, ↓reduceIte]

omit hs in
theorem sphPreFold_eq_apexTwo {z : ℂ} (hz : z ∈ σ.sphPieceApexTwo) :
    σ.sphPreFold z = σ.sphApexTwo z := by
  have h1 : ¬ ‖σ.rotOne z‖ < σ.sphGermRadius := not_lt.2 hz.2.2.2.le
  simp only [sphPreFold, h1, hz.2.1, ↓reduceIte]

omit hs in
theorem sphPreFold_eq_outer {z : ℂ} (hz : z ∈ σ.sphPieceOuter) :
    σ.sphPreFold z = compactOuterGerm σ.p₃ z := by
  obtain ⟨-, h3, -, h1, -, h2⟩ := hz
  simp only [sphPreFold, not_lt.2 h1.le, not_lt.2 h2.le, h3, ↓reduceIte]

theorem sphPreFold_eq_cornerOne {z : ℂ} (hz : z ∈ σ.sphPieceCornerOne) :
    σ.sphPreFold z = σ.sphFoldCornerOne z := by
  obtain ⟨hδ, hβ, hββ', hg, hga, hab, hb1, hg3, hga3, hab3, hb3⟩ := sphParams hs
  obtain ⟨⟨-, hr, h2, h3⟩, -, -, hψ, -⟩ := hz
  have hc2 : ¬ ‖σ.rotTwo z‖ < σ.sphGermRadius := not_lt.2 h2.le
  have hc3 : ¬ ‖z‖ < σ.sphOuterGermRadius := not_lt.2 h3.le
  rcases lt_or_ge ‖σ.rotOne z‖ σ.sphGermRadius with h1 | h1
  · simp only [sphPreFold, h1, ↓reduceIte, sphFoldCornerOne, sphApexOne]
    exact (sphCornerOne_eq_apex hab (by linarith) (by linarith) (Or.inr hψ)).symm
  · simp only [sphPreFold, not_lt.2 h1, hc2, hc3, hr, ↓reduceIte]

theorem sphPreFold_eq_cornerTwo {z : ℂ} (hz : z ∈ σ.sphPieceCornerTwo) :
    σ.sphPreFold z = σ.sphFoldCornerTwo z := by
  obtain ⟨hδ, hβ, hββ', hg, hga, hab, hb1, hg3, hga3, hab3, hb3⟩ := sphParams hs
  obtain ⟨hgc1, -⟩ := sphLayout_ineqs hs
  obtain ⟨⟨-, hr, h1, h3⟩, hz2, -⟩ := hz
  have hc1 : ¬ ‖σ.rotOne z‖ < σ.sphGermRadius := not_lt.2 (by linarith)
  have hc4 : ¬ ‖σ.rotOne z‖ < σ.sphCornerRad 0 := not_lt.2 h1.le
  have hc3 : ¬ ‖z‖ < σ.sphOuterGermRadius := not_lt.2 h3.le
  rcases lt_or_ge ‖σ.rotTwo z‖ σ.sphGermRadius with h2 | h2
  · simp only [sphPreFold, hc1, h2, ↓reduceIte, sphFoldCornerTwo, sphApexTwo]
    exact (sphCornerTwo_eq_apex hab (by linarith) (by linarith) (Or.inr hz2.2.2.1)).symm
  · simp only [sphPreFold, hc1, not_lt.2 h2, hc3, hc4, hr, ↓reduceIte]

theorem sphPreFold_eq_lens {z : ℂ} (hz : z ∈ σ.sphPieceLens) :
    σ.sphPreFold z = σ.sphBridgeTwo z := by
  obtain ⟨hδ, hβ, hββ', hg, hga, hab, hb1, hg3, hga3, hab3, hb3⟩ := sphParams hs
  obtain ⟨⟨h1, h2, hw, h3⟩, hz2, b1, b2⟩ := hz
  have hc1 : ¬ ‖σ.rotOne z‖ < σ.sphGermRadius := not_lt.2 (by linarith)
  have hc2 : ¬ ‖σ.rotTwo z‖ < σ.sphGermRadius := not_lt.2 (by linarith)
  have hc3 : ¬ ‖z‖ < σ.sphOuterGermRadius := not_lt.2 h3.le
  have hw' : σ.sphSideTwo z ≤ σ.sphLensWidth := le_trans (le_abs_self _) hw.le
  by_cases hr1 : ‖σ.rotOne z‖ < σ.sphCornerRad 0
  · simp only [sphPreFold, hc1, hc2, hc3, hr1, ↓reduceIte, sphFoldCornerOne]
    exact sphCornerOne_eq_bridgeTwo hs hab hββ' hz2 (by linarith [sphModOne_pos hs z]) h1.le hw'
  by_cases hr2 : ‖σ.rotTwo z‖ < σ.sphCornerRad 1
  · simp only [sphPreFold, hc1, hc2, hc3, hr1, hr2, ↓reduceIte, sphFoldCornerTwo]
    exact sphCornerTwo_eq_bridgeTwo hs hab hββ' hz2 (by linarith [sphModTwo_pos hs z]) h2.le hw'
  simp only [sphPreFold, hc1, hc2, hc3, hr1, hr2, hw, ↓reduceIte]

theorem sphPreFold_eq_cornerThree {z : ℂ} (hz : z ∈ σ.sphPieceCornerThree) :
    σ.sphPreFold z = σ.sphFoldCornerThree z := by
  obtain ⟨hδ, hβ, hββ', hg, hga, hab, hb1, hg3, hga3, hab3, hb3⟩ := sphParams hs
  obtain ⟨hgc1, hgc2, -⟩ := sphLayout_ineqs hs
  obtain ⟨⟨h1, h2, hw, -⟩, -, hz0, -⟩ := hz
  have hc1 : ¬ ‖σ.rotOne z‖ < σ.sphGermRadius := not_lt.2 (by linarith)
  have hc2 : ¬ ‖σ.rotTwo z‖ < σ.sphGermRadius := not_lt.2 (by linarith)
  have hr1 : ¬ ‖σ.rotOne z‖ < σ.sphCornerRad 0 := not_lt.2 h1.le
  have hr2 : ¬ ‖σ.rotTwo z‖ < σ.sphCornerRad 1 := not_lt.2 h2.le
  have hl : ¬ |σ.sphSideTwo z| < σ.sphLensWidth := not_lt.2 hw.le
  by_cases h3 : ‖z‖ < σ.sphOuterGermRadius
  · simp only [sphPreFold, hc1, hc2, h3, ↓reduceIte, sphFoldCornerThree]
    exact (sphCornerThree_eq_outerGerm hab3 (by linarith) hz0.1).symm
  · simp only [sphPreFold, hc1, hc2, h3, hr1, hr2, hl, ↓reduceIte]

theorem sphPreFold_eq_junctionOne {z : ℂ} (hz : z ∈ σ.sphPieceJunctionOne) :
    σ.sphPreFold z = σ.sphBridgeOne z := by
  obtain ⟨hδ, hβ, hββ', hg, hga, hab, hb1, hg3, hga3, hab3, hb3⟩ := sphParams hs
  obtain ⟨hgc1, hgc2, -⟩ := sphLayout_ineqs hs
  obtain ⟨⟨h1, h2, hw, h3, hbl⟩, hz1, -, -, b1⟩ := hz
  have hc1 : ¬ ‖σ.rotOne z‖ < σ.sphGermRadius := not_lt.2 (by linarith)
  have hc2 : ¬ ‖σ.rotTwo z‖ < σ.sphGermRadius := not_lt.2 (by linarith)
  have hc3 : ¬ ‖z‖ < σ.sphOuterGermRadius := not_lt.2 (by linarith)
  have hr2 : ¬ ‖σ.rotTwo z‖ < σ.sphCornerRad 1 := not_lt.2 h2.le
  have hl : ¬ |σ.sphSideTwo z| < σ.sphLensWidth :=
    not_lt.2 (le_trans (by linarith) (le_abs_self _))
  by_cases hr1 : ‖σ.rotOne z‖ < σ.sphCornerRad 0
  · simp only [sphPreFold, hc1, hc2, hc3, hr1, ↓reduceIte, sphFoldCornerOne]
    exact sphCornerOne_eq_bridgeOne hs hab hββ' hz1 (by linarith [sphModOne_pos hs z]) h1.le
      hw.le
  · simp only [sphPreFold, hc1, hc2, hc3, hr1, hr2, hl, ↓reduceIte, sphFoldCornerThree]
    have hm := sphModThree_pos (sphCanon_bounds_one hs hz1).2
    exact sphCornerThree_eq_bridgeOne hs hab3 one_pos hz1 (by linarith) h3.le hbl.le

theorem sphPreFold_eq_junctionTwo {z : ℂ} (hz : z ∈ σ.sphPieceJunctionTwo) :
    σ.sphPreFold z = σ.sphBridgeZero z := by
  obtain ⟨hδ, hβ, hββ', hg, hga, hab, hb1, hg3, hga3, hab3, hb3⟩ := sphParams hs
  obtain ⟨hgc1, hgc2, -⟩ := sphLayout_ineqs hs
  obtain ⟨⟨h2, h1, hw, h3, hbl⟩, hz0, -, b1⟩ := hz
  have hc1 : ¬ ‖σ.rotOne z‖ < σ.sphGermRadius := not_lt.2 (by linarith)
  have hc2 : ¬ ‖σ.rotTwo z‖ < σ.sphGermRadius := not_lt.2 (by linarith)
  have hc3 : ¬ ‖z‖ < σ.sphOuterGermRadius := not_lt.2 (by linarith)
  have hr1 : ¬ ‖σ.rotOne z‖ < σ.sphCornerRad 0 := not_lt.2 h1.le
  have hl : ¬ |σ.sphSideTwo z| < σ.sphLensWidth :=
    not_lt.2 (le_trans (by linarith) (le_abs_self _))
  by_cases hr2 : ‖σ.rotTwo z‖ < σ.sphCornerRad 1
  · simp only [sphPreFold, hc1, hc2, hc3, hr1, hr2, ↓reduceIte, sphFoldCornerTwo]
    exact sphCornerTwo_eq_bridgeZero hs hab hββ' hz0 (by linarith [sphModTwo_pos hs z]) h2.le
      hw.le
  · simp only [sphPreFold, hc1, hc2, hc3, hr1, hr2, hl, ↓reduceIte, sphFoldCornerThree]
    have hm := sphModThree_pos (sphCanon_bounds_zero hs hz0).2
    exact sphCornerThree_eq_bridgeZero hs hab3 one_pos hz0 (by linarith) h3.le hbl.le

theorem sphGood_apexOne {z : ℂ} (hz : z ∈ σ.sphPieceApexOne) (h1 : z ≠ σ.vertexOne) :
    ContDiffAt ℝ ∞ σ.sphApexOne z ∧ 0 < (fderiv ℝ σ.sphApexOne z).det :=
  ⟨contDiffAt_sphApexOne hs hz.1, det_fderiv_sphApexOne_pos hs hz.1 (rotOne_ne_zero_sph hs hz.1 h1)⟩

theorem sphGood_apexTwo {z : ℂ} (hz : z ∈ σ.sphPieceApexTwo) (h2 : z ≠ σ.vertexTwo) :
    ContDiffAt ℝ ∞ σ.sphApexTwo z ∧ 0 < (fderiv ℝ σ.sphApexTwo z).det :=
  ⟨contDiffAt_sphApexTwo hs hz.1, det_fderiv_sphApexTwo_pos hs hz.1 (rotTwo_ne_zero_sph hs hz.1 h2)⟩

theorem sphGood_outer {z : ℂ} (hz : z ∈ σ.sphPieceOuter) :
    ContDiffAt ℝ ∞ (compactOuterGerm σ.p₃) z ∧
      0 < (fderiv ℝ (compactOuterGerm σ.p₃) z).det := by
  obtain ⟨hδ, hβ, hββ', hg, hga, hab, hb1, hg3, hga3, hab3, hb3⟩ := sphParams hs
  have hz0 : z ≠ 0 := norm_pos_iff.1 hz.1
  have h1 : ‖z‖ ≤ 1 := by linarith [hz.2.1]
  refine ⟨contDiffAt_compactOuterGerm _ hz0,
    det_fderiv_compactOuterGerm_pos (le_trans (by norm_num) σ.two_le_p₃) hz0 ?_⟩
  have := pow_le_one₀ (norm_nonneg z) h1 (n := σ.p₃)
  linarith

theorem sphGood_cornerOne {z : ℂ} (hz : z ∈ σ.sphPieceCornerOne) :
    ContDiffAt ℝ ∞ σ.sphFoldCornerOne z ∧ 0 < (fderiv ℝ σ.sphFoldCornerOne z).det := by
  obtain ⟨hδ, hβ, hββ', hg, hga, hab, hb1, hg3, hga3, hab3, hb3⟩ := sphParams hs
  obtain ⟨-, h1, h2, hψ, b1, b2, hlam⟩ := hz
  have hm := sphModOne_pos hs z
  have hpos1 : 0 < σ.sphModOne z + ((σ.sphBridgeOne z).re - 3 / 2) := by linarith
  have hpos2 : 0 < σ.sphModOne z - ((σ.sphBridgeTwo z).re - 3 / 2) := by linarith
  have hord : σ.sphAngleOneAtOne z ≤ σ.sphAngleTwoAtOne z :=
    (halfArg_lt_negHalfArg_of_re hm (by linarith) (by linarith) (sq_sphBridgeOne_one hs h1)
      (sq_sphBridgeTwo_one hs h2)).le
  exact ⟨contDiffAt_sphCornerOne hs _ _ _ _ h1 h2 hψ hpos1 hpos2,
    det_fderiv_sphCornerOne_pos hs hab hb1 hββ' h1 h2 hψ hpos1 hpos2 hord
      (hlam.imp_left le_of_lt)⟩

theorem sphGood_cornerTwo {z : ℂ} (hz : z ∈ σ.sphPieceCornerTwo) :
    ContDiffAt ℝ ∞ σ.sphFoldCornerTwo z ∧ 0 < (fderiv ℝ σ.sphFoldCornerTwo z).det := by
  obtain ⟨hδ, hβ, hββ', hg, hga, hab, hb1, hg3, hga3, hab3, hb3⟩ := sphParams hs
  obtain ⟨-, h2, h0, b1, b2, hlam⟩ := hz
  have hm := sphModTwo_pos hs z
  have hpos2 : 0 < σ.sphModTwo z + ((σ.sphBridgeTwo z).re + 3 / 2) := by linarith
  have hpos0 : 0 < σ.sphModTwo z - ((σ.sphBridgeZero z).re + 3 / 2) := by linarith
  have hord : σ.sphAngleTwoAtTwo z ≤ σ.sphAngleZeroAtTwo z :=
    (halfArg_lt_negHalfArg_of_re hm (by linarith) (by linarith) (sq_sphBridgeTwo_two hs h2)
      (sq_sphBridgeZero_two hs h0)).le
  exact ⟨contDiffAt_sphCornerTwo_sph hs _ _ _ _ h2 h0 hpos2 hpos0,
    det_fderiv_sphCornerTwo_pos hs hab hb1 hββ' h2 h0 hpos2 hpos0 hord
      (hlam.imp_left le_of_lt)⟩

theorem sphGood_cornerThree {z : ℂ} (hz : z ∈ σ.sphPieceCornerThree) :
    ContDiffAt ℝ ∞ σ.sphFoldCornerThree z ∧ 0 < (fderiv ℝ σ.sphFoldCornerThree z).det := by
  obtain ⟨hδ, hβ, hββ', hg, hga, hab, hb1, hg3, hga3, hab3, hb3⟩ := sphParams hs
  obtain ⟨-, h1, h0, r1, r0, hside⟩ := hz
  have hm := sphModThree_pos (sphCanon_bounds_one hs h1).2
  have hψ : 0 < ‖z‖ + z.re := h0.1
  have hpos1 : 0 < σ.sphModThree z + (σ.sphBridgeOne z).re := by linarith
  have hpos0 : 0 < σ.sphModThree z - (σ.sphBridgeZero z).re := by linarith
  have hord : σ.sphAngleOneAtThree z ≤ σ.sphAngleZeroAtThree z :=
    (halfArg_lt_negHalfArg_of_re hm r1 r0 (sq_sphBridgeOne_three hs h1)
      (sq_sphBridgeZero_three hs h0)).le
  refine ⟨contDiffAt_sphCornerThree_sph hs _ _ _ _ h1 h0 hψ hpos1 hpos0,
    det_fderiv_sphCornerThree_pos hs hab3 hb3 one_pos hδ h1 h0 hψ hpos1 hpos0 hord ?_⟩
  rcases hside with ⟨a, b⟩ | h | h
  · exact Or.inl ⟨a.le, b.le⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)

theorem sphGood_lens {z : ℂ} (hz : z ∈ σ.sphPieceLens) :
    ContDiffAt ℝ ∞ σ.sphBridgeTwo z ∧ 0 < (fderiv ℝ σ.sphBridgeTwo z).det := by
  obtain ⟨-, h2, -, hb⟩ := hz
  exact ⟨contDiffAt_sphBridgeTwo hs h2,
    det_fderiv_sphBridgeTwo_pos hs h2 (by linarith [sphModOne_pos hs z])⟩

theorem sphGood_junctionOne {z : ℂ} (hz : z ∈ σ.sphPieceJunctionOne) :
    ContDiffAt ℝ ∞ σ.sphBridgeOne z ∧ 0 < (fderiv ℝ σ.sphBridgeOne z).det := by
  obtain ⟨-, h1, -, -, hb⟩ := hz
  exact ⟨contDiffAt_sphBridgeOne hs h1,
    det_fderiv_sphBridgeOne_pos hs h1 (by linarith [sphModOne_pos hs z])⟩

theorem sphGood_junctionTwo {z : ℂ} (hz : z ∈ σ.sphPieceJunctionTwo) :
    ContDiffAt ℝ ∞ σ.sphBridgeZero z ∧ 0 < (fderiv ℝ σ.sphBridgeZero z).det := by
  obtain ⟨-, h0, -, hb⟩ := hz
  exact ⟨contDiffAt_sphBridgeZero hs h0,
    det_fderiv_sphBridgeZero_pos hs h0 (by linarith [sphModTwo_pos hs z])⟩

theorem sphContAt_hlam {z : ℂ} (hv2 : 1 + σ.vertexTwo * z ≠ 0) :
    ContinuousAt (fun u => ((σ.rotTwo u - σ.sphTOneTwo) *
      (1 + σ.sphTOneTwo * σ.rotTwo u)).re) z :=
  (EuclidShape.contDiffAt_re_comp (((contDiffAt_rotTwo_sph hs hv2).sub contDiffAt_const).mul
    (contDiffAt_const.add (contDiffAt_const.mul (contDiffAt_rotTwo_sph hs hv2))))).continuousAt

theorem sphContAt_side {z : ℂ} (hv2 : 1 + σ.vertexTwo * z ≠ 0) :
    ContinuousAt σ.sphSideTwo z :=
  (contDiffAt_sphSideTwo hs hv2).continuousAt

theorem sphContAt_absSide {z : ℂ} (hv2 : 1 + σ.vertexTwo * z ≠ 0) :
    ContinuousAt (fun u => |σ.sphSideTwo u|) z :=
  continuous_abs.continuousAt.comp (sphContAt_side hs hv2)

theorem sphContAt_reRotTwo {z : ℂ} (hv2 : 1 + σ.vertexTwo * z ≠ 0) :
    ContinuousAt (fun u => (σ.rotTwo u).re) z :=
  (EuclidShape.contDiffAt_re_comp (contDiffAt_rotTwo_sph hs hv2)).continuousAt

theorem sphContAt_psiOne {z : ℂ} (hv1 : 1 + conj σ.vertexOne * z ≠ 0) :
    ContinuousAt (fun u => ‖σ.rotOne u‖ + (σ.rotOne u).re) z :=
  (continuousAt_normRotOne_sph hs hv1).add
    (EuclidShape.contDiffAt_re_comp (contDiffAt_rotOne_sph hs hv1)).continuousAt

theorem sphContAt_reBridgeOne {z : ℂ} (hz : z ∈ σ.sphDomOne) :
    ContinuousAt (fun u => (σ.sphBridgeOne u).re) z :=
  (EuclidShape.contDiffAt_re_comp (contDiffAt_sphBridgeOne hs hz)).continuousAt

theorem sphContAt_reBridgeTwo {z : ℂ} (hz : z ∈ σ.sphDomTwo) :
    ContinuousAt (fun u => (σ.sphBridgeTwo u).re) z :=
  (EuclidShape.contDiffAt_re_comp (contDiffAt_sphBridgeTwo hs hz)).continuousAt

theorem sphContAt_reBridgeZero {z : ℂ} (hz : z ∈ σ.sphDomZero) :
    ContinuousAt (fun u => (σ.sphBridgeZero u).re) z :=
  (EuclidShape.contDiffAt_re_comp (contDiffAt_sphBridgeZero hs hz)).continuousAt

theorem sphContAt_blend {z : ℂ} (hψ : 0 < ‖z‖ + z.re) (hv1 : 1 + conj σ.vertexOne * z ≠ 0)
    (hv2 : 1 + σ.vertexTwo * z ≠ 0) : ContinuousAt σ.sphFoldBlend z :=
  continuousAt_sphBlendThree_sph hs 1 σ.sphCornerShrink hψ hv1 hv2

omit hs in
theorem sphContAt_normAddRe (z : ℂ) : ContinuousAt (fun u : ℂ => ‖u‖ + u.re) z :=
  (continuous_norm.add Complex.continuous_re).continuousAt

theorem isOpen_sphPieceApexOne : IsOpen σ.sphPieceApexOne := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  filter_upwards [ev_chartOne_sph hz.1,
    EuclidShape.ev_gt (continuousAt_normRotOne_sph hs hz.1) hz.2] with u c1 c2
  exact ⟨c1, c2⟩

theorem isOpen_sphPieceApexTwo : IsOpen σ.sphPieceApexTwo := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨a1, a2, a3, a4⟩ := hz
  filter_upwards [ev_chartTwo_sph a1, EuclidShape.ev_gt (continuousAt_normRotTwo_sph hs a1) a2,
    ev_chartOne_sph a3, EuclidShape.ev_lt (continuousAt_normRotOne_sph hs a3) a4] with
    u c1 c2 c3 c4
  exact ⟨c1, c2, c3, c4⟩

theorem isOpen_sphPieceOuter : IsOpen σ.sphPieceOuter := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨a0, a1, a2, a3, a4, a5⟩ := hz
  filter_upwards [EuclidShape.ev_lt continuous_norm.continuousAt a0,
    EuclidShape.ev_gt continuous_norm.continuousAt a1, ev_chartOne_sph a2,
    EuclidShape.ev_lt (continuousAt_normRotOne_sph hs a2) a3, ev_chartTwo_sph a4,
    EuclidShape.ev_lt (continuousAt_normRotTwo_sph hs a4) a5] with u c0 c1 c2 c3 c4 c5
  exact ⟨c0, c1, c2, c3, c4, c5⟩

theorem isOpen_sphPieceCornerOne : IsOpen σ.sphPieceCornerOne := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨⟨a1, a2, a3, a4⟩, h1, h2, hψ, b1, b2, hl⟩ := hz
  have hv1 : 1 + conj σ.vertexOne * z ≠ 0 := h2.2.1
  have hv2 : 1 + σ.vertexTwo * z ≠ 0 := h2.1
  have hl' : ∀ᶠ u in 𝓝 z, ((σ.rotTwo u - σ.sphTOneTwo) *
      (1 + σ.sphTOneTwo * σ.rotTwo u)).re < 0 ∨
      σ.sphSwitchTop < σ.sphSideTwo u ∨ σ.sphSideTwo u < σ.sphLensWidth := by
    rcases hl with h | h | h
    · exact (EuclidShape.ev_gt (sphContAt_hlam hs hv2) h).mono fun u hu => Or.inl hu
    · exact (EuclidShape.ev_lt (sphContAt_side hs hv2) h).mono fun u hu => Or.inr (Or.inl hu)
    · exact (EuclidShape.ev_gt (sphContAt_side hs hv2) h).mono fun u hu => Or.inr (Or.inr hu)
  filter_upwards [EuclidShape.ev_lt (continuousAt_normRotOne_sph hs hv1) a1,
    EuclidShape.ev_gt (continuousAt_normRotOne_sph hs hv1) a2,
    EuclidShape.ev_lt (continuousAt_normRotTwo_sph hs hv2) a3,
    EuclidShape.ev_lt continuous_norm.continuousAt a4, isOpen_sphDomOne.mem_nhds h1,
    (isOpen_sphDomTwo hs).mem_nhds h2, EuclidShape.ev_lt (sphContAt_psiOne hs hv1) hψ,
    EuclidShape.ev_lt (sphContAt_reBridgeOne hs h1) b1,
    EuclidShape.ev_gt (sphContAt_reBridgeTwo hs h2) b2, hl'] with
    u c1 c2 c3 c4 c5 c6 c7 c8 c9 c10
  exact ⟨⟨c1, c2, c3, c4⟩, c5, c6, c7, c8, c9, c10⟩

theorem isOpen_sphPieceCornerTwo : IsOpen σ.sphPieceCornerTwo := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨⟨a1, a2, a3, a4⟩, h2, h0, b1, b2, hl⟩ := hz
  have hv1 : 1 + conj σ.vertexOne * z ≠ 0 := h2.2.1
  have hv2 : 1 + σ.vertexTwo * z ≠ 0 := h2.1
  have hl' : ∀ᶠ u in 𝓝 z, 0 < (σ.rotTwo u).re ∨
      σ.sphSwitchTop < σ.sphSideTwo u ∨ σ.sphSideTwo u < σ.sphLensWidth := by
    rcases hl with h | h | h
    · exact (EuclidShape.ev_lt (sphContAt_reRotTwo hs hv2) h).mono fun u hu => Or.inl hu
    · exact (EuclidShape.ev_lt (sphContAt_side hs hv2) h).mono fun u hu => Or.inr (Or.inl hu)
    · exact (EuclidShape.ev_gt (sphContAt_side hs hv2) h).mono fun u hu => Or.inr (Or.inr hu)
  filter_upwards [EuclidShape.ev_lt (continuousAt_normRotTwo_sph hs hv2) a1,
    EuclidShape.ev_gt (continuousAt_normRotTwo_sph hs hv2) a2,
    EuclidShape.ev_lt (continuousAt_normRotOne_sph hs hv1) a3,
    EuclidShape.ev_lt continuous_norm.continuousAt a4, (isOpen_sphDomTwo hs).mem_nhds h2,
    isOpen_sphDomZero.mem_nhds h0, EuclidShape.ev_lt (sphContAt_reBridgeTwo hs h2) b1,
    EuclidShape.ev_gt (sphContAt_reBridgeZero hs h0) b2, hl'] with
    u c1 c2 c3 c4 c5 c6 c7 c8 c9
  exact ⟨⟨c1, c2, c3, c4⟩, c5, c6, c7, c8, c9⟩

theorem isOpen_sphPieceLens : IsOpen σ.sphPieceLens := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨⟨a1, a2, a3, a4⟩, h2, b1, b2⟩ := hz
  have hv1 : 1 + conj σ.vertexOne * z ≠ 0 := h2.2.1
  have hv2 : 1 + σ.vertexTwo * z ≠ 0 := h2.1
  filter_upwards [EuclidShape.ev_lt (continuousAt_normRotOne_sph hs hv1) a1,
    EuclidShape.ev_lt (continuousAt_normRotTwo_sph hs hv2) a2,
    EuclidShape.ev_gt (sphContAt_absSide hs hv2) a3,
    EuclidShape.ev_lt continuous_norm.continuousAt a4, (isOpen_sphDomTwo hs).mem_nhds h2,
    EuclidShape.ev_lt (sphContAt_reBridgeTwo hs h2) b1,
    EuclidShape.ev_gt (sphContAt_reBridgeTwo hs h2) b2] with u c1 c2 c3 c4 c5 c6 c7
  exact ⟨⟨c1, c2, c3, c4⟩, c5, c6, c7⟩

theorem isOpen_sphPieceCornerThree : IsOpen σ.sphPieceCornerThree := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨⟨a1, a2, a3, a4⟩, h1, h0, b1, b2, hside⟩ := hz
  have hv1 : 1 + conj σ.vertexOne * z ≠ 0 := one_add_conj_vertexOne_ne_of_domOne h1
  have hv2 : 1 + σ.vertexTwo * z ≠ 0 := by
    have := one_add_vertexTwo_ne_of_domZero h0
    rwa [conj_vertexTwo_sph] at this
  have hb := sphContAt_blend hs h0.1 hv1 hv2
  have hside' : ∀ᶠ u in 𝓝 z, (0 < σ.wallSide 0 u ∧ 0 < σ.wallSide 1 u) ∨
      1 < σ.sphFoldBlend u ∨ σ.sphFoldBlend u < -1 := by
    rcases hside with ⟨p, q⟩ | h | h
    · filter_upwards [EuclidShape.ev_lt (continuous_wallSide_sph hs 0).continuousAt p,
        EuclidShape.ev_lt (continuous_wallSide_sph hs 1).continuousAt q] with u hp hq
      exact Or.inl ⟨hp, hq⟩
    · exact (EuclidShape.ev_lt hb h).mono fun u hu => Or.inr (Or.inl hu)
    · exact (EuclidShape.ev_gt hb h).mono fun u hu => Or.inr (Or.inr hu)
  filter_upwards [EuclidShape.ev_lt (continuousAt_normRotOne_sph hs hv1) a1,
    EuclidShape.ev_lt (continuousAt_normRotTwo_sph hs hv2) a2,
    EuclidShape.ev_lt (sphContAt_absSide hs hv2) a3,
    EuclidShape.ev_lt continuous_norm.continuousAt a4, isOpen_sphDomOne.mem_nhds h1,
    isOpen_sphDomZero.mem_nhds h0, EuclidShape.ev_lt (sphContAt_reBridgeOne hs h1) b1,
    EuclidShape.ev_gt (sphContAt_reBridgeZero hs h0) b2, hside'] with
    u c1 c2 c3 c4 c5 c6 c7 c8 c9
  exact ⟨⟨c1, c2, c3, c4⟩, c5, c6, c7, c8, c9⟩

theorem isOpen_sphPieceJunctionOne : IsOpen σ.sphPieceJunctionOne := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨⟨a1, a2, a3, a4, a5⟩, h1, hψ, hv2, b1⟩ := hz
  have hv1 : 1 + conj σ.vertexOne * z ≠ 0 := one_add_conj_vertexOne_ne_of_domOne h1
  filter_upwards [EuclidShape.ev_lt (continuousAt_normRotOne_sph hs hv1) a1,
    EuclidShape.ev_lt (continuousAt_normRotTwo_sph hs hv2) a2,
    EuclidShape.ev_lt (sphContAt_side hs hv2) a3,
    EuclidShape.ev_lt continuous_norm.continuousAt a4,
    EuclidShape.ev_lt (sphContAt_blend hs hψ hv1 hv2) a5, isOpen_sphDomOne.mem_nhds h1,
    EuclidShape.ev_lt (sphContAt_normAddRe z) hψ, ev_chartTwo_sph hv2,
    EuclidShape.ev_lt (sphContAt_reBridgeOne hs h1) b1] with u c1 c2 c3 c4 c5 c6 c7 c8 c9
  exact ⟨⟨c1, c2, c3, c4, c5⟩, c6, c7, c8, c9⟩

theorem isOpen_sphPieceJunctionTwo : IsOpen σ.sphPieceJunctionTwo := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨⟨a1, a2, a3, a4, a5⟩, h0, hv1, b1⟩ := hz
  have hv2 : 1 + σ.vertexTwo * z ≠ 0 := by
    have := one_add_vertexTwo_ne_of_domZero h0
    rwa [conj_vertexTwo_sph] at this
  filter_upwards [EuclidShape.ev_lt (continuousAt_normRotTwo_sph hs hv2) a1,
    EuclidShape.ev_lt (continuousAt_normRotOne_sph hs hv1) a2,
    EuclidShape.ev_lt (sphContAt_side hs hv2) a3,
    EuclidShape.ev_lt continuous_norm.continuousAt a4,
    EuclidShape.ev_gt (sphContAt_blend hs h0.1 hv1 hv2) a5, isOpen_sphDomZero.mem_nhds h0,
    ev_chartOne_sph hv1, EuclidShape.ev_gt (sphContAt_reBridgeZero hs h0) b1] with
    u c1 c2 c3 c4 c5 c6 c7 c8
  exact ⟨⟨c1, c2, c3, c4, c5⟩, c6, c7, c8⟩

theorem isOpen_sphGoodSet : IsOpen σ.sphGoodSet :=
  (((((((((isOpen_sphPieceApexOne hs).union (isOpen_sphPieceApexTwo hs)).union
    (isOpen_sphPieceOuter hs)).union (isOpen_sphPieceCornerOne hs)).union
      (isOpen_sphPieceCornerTwo hs)).union (isOpen_sphPieceLens hs)).union
        (isOpen_sphPieceCornerThree hs)).union (isOpen_sphPieceJunctionOne hs)).union
          (isOpen_sphPieceJunctionTwo hs))

omit hs in
theorem sphGood_of_piece {s : Set ℂ} (hso : IsOpen s) {g : ℂ → ℂ}
    (heq : ∀ u ∈ s, σ.sphPreFold u = g u) {z : ℂ} (hz : z ∈ s)
    (hg : ContDiffAt ℝ ∞ g z ∧ 0 < (fderiv ℝ g z).det) :
    ContDiffAt ℝ ∞ σ.sphPreFold z ∧ 0 < (fderiv ℝ σ.sphPreFold z).det := by
  have hev : σ.sphPreFold =ᶠ[𝓝 z] g := Filter.eventually_of_mem (hso.mem_nhds hz) heq
  exact ⟨hg.1.congr_of_eventuallyEq hev, by rw [hev.fderiv_eq]; exact hg.2⟩

theorem sphGood_sphPreFold {z : ℂ} (hz : z ∈ σ.sphGoodSet) (h1 : z ≠ σ.vertexOne)
    (h2 : z ≠ σ.vertexTwo) :
    ContDiffAt ℝ ∞ σ.sphPreFold z ∧ 0 < (fderiv ℝ σ.sphPreFold z).det := by
  rcases hz with (((((((hz | hz) | hz) | hz) | hz) | hz) | hz) | hz) | hz
  · exact sphGood_of_piece (isOpen_sphPieceApexOne hs) (fun _ hu => sphPreFold_eq_apexOne hu)
      hz (sphGood_apexOne hs hz h1)
  · exact sphGood_of_piece (isOpen_sphPieceApexTwo hs) (fun _ hu => sphPreFold_eq_apexTwo hu)
      hz (sphGood_apexTwo hs hz h2)
  · exact sphGood_of_piece (isOpen_sphPieceOuter hs) (fun _ hu => sphPreFold_eq_outer hu) hz
      (sphGood_outer hs hz)
  · exact sphGood_of_piece (isOpen_sphPieceCornerOne hs)
      (fun _ hu => sphPreFold_eq_cornerOne hs hu) hz (sphGood_cornerOne hs hz)
  · exact sphGood_of_piece (isOpen_sphPieceCornerTwo hs)
      (fun _ hu => sphPreFold_eq_cornerTwo hs hu) hz (sphGood_cornerTwo hs hz)
  · exact sphGood_of_piece (isOpen_sphPieceLens hs) (fun _ hu => sphPreFold_eq_lens hs hu) hz
      (sphGood_lens hs hz)
  · exact sphGood_of_piece (isOpen_sphPieceCornerThree hs)
      (fun _ hu => sphPreFold_eq_cornerThree hs hu) hz (sphGood_cornerThree hs hz)
  · exact sphGood_of_piece (isOpen_sphPieceJunctionOne hs)
      (fun _ hu => sphPreFold_eq_junctionOne hs hu) hz (sphGood_junctionOne hs hz)
  · exact sphGood_of_piece (isOpen_sphPieceJunctionTwo hs)
      (fun _ hu => sphPreFold_eq_junctionTwo hs hu) hz (sphGood_junctionTwo hs hz)

theorem vertexOne_mem_sphPieceApexOne : σ.vertexOne ∈ σ.sphPieceApexOne := by
  refine ⟨one_add_conj_mul_self_ne_sph _, ?_⟩
  rw [rotOne_vertexOne_sph hs, norm_zero]
  exact (sphParams hs).2.2.2.1

theorem vertexTwo_mem_sphPieceApexTwo : σ.vertexTwo ∈ σ.sphPieceApexTwo := by
  have hg0 := (sphParams hs).2.2.2.1
  have ht : σ.sphGermRadius < σ.sphTOneTwo := by
    have hplus := sphTau_oplus_onetwo hs
    have t0 := sphTau_pos hs 0
    have t1 := sphTau_pos hs 1
    have hm := sphTau_mul_lt_one hs 0 1
    have ht1 : σ.sphTau 0 + σ.sphTau 1 ≤ σ.sphTOneTwo := by
      have := mul_pos (mul_pos t0 t1) (tOneTwo_pos_sph hs)
      nlinarith only [hplus, this]
    have m0 : σ.sphInnerScale ≤ σ.sphTau 0 := min_le_left _ _
    unfold sphGermRadius
    linarith
  refine ⟨one_add_vertexTwo_mul_self_ne_sph, ?_, one_add_conj_vertexOne_mul_vertexTwo_ne_sph hs, ?_⟩
  · rw [rotTwo_vertexTwo_sph hs, norm_zero]
    exact hg0
  · rw [norm_rotOne_vertexTwo_sph hs]
    exact ht

theorem contDiffAt_sphPreFold_of_good {z : ℂ} (hz : z ∈ σ.sphGoodSet) :
    ContDiffAt ℝ ∞ σ.sphPreFold z := by
  by_cases h1 : z = σ.vertexOne
  · subst h1
    have hp := vertexOne_mem_sphPieceApexOne hs
    exact (contDiffAt_sphApexOne hs hp.1).congr_of_eventuallyEq
      (Filter.eventually_of_mem ((isOpen_sphPieceApexOne hs).mem_nhds hp)
        fun _ hu => sphPreFold_eq_apexOne hu)
  by_cases h2 : z = σ.vertexTwo
  · subst h2
    have hp := vertexTwo_mem_sphPieceApexTwo hs
    exact (contDiffAt_sphApexTwo hs hp.1).congr_of_eventuallyEq
      (Filter.eventually_of_mem ((isOpen_sphPieceApexTwo hs).mem_nhds hp)
        fun _ hu => sphPreFold_eq_apexTwo hu)
  exact (sphGood_sphPreFold hs hz h1 h2).1

end Spherical

end CompactShape

end GC.Seifert
