import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldEuclidLayout

/-!
# The pieces of the flat compact fold

Lane CF, tier 3, curvature `0` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §5, with review 23 §6.1: a gluing certificate made
of open sets on which the fold is given by one smooth formula with positive Jacobian).

The bridges are polar maps about one of their centres with a radius depending on the distance to
one vertex only, so the polar Jacobian formula along the circles about that vertex gives positive
Jacobians (`det_fderiv_bridgeOne_pos`, `det_fderiv_bridgeTwo_pos`, `det_fderiv_bridgeZero_pos`).
The angle order needed by the corner Jacobians follows from the signs of the real parts of the two
bridge points relative to the centre (`halfArg_lt_negHalfArg_of_re`).

The fold before the core replacement is the piecewise map `preFold`: the apex models on the germ
discs about `v₁`, `v₂` (radius `germRadius = ρ/3`) and the outer germ on the punctured disc about
`v₃ = 0` (radius `outerGermRadius = ρ/16`), the corners `cornerOne`, `cornerTwo` on the corner discs
`dⱼ < rⱼ - δ`, the bridge `bridgeTwo` on the lens `|wallSide 2| < β`, and `cornerThree` elsewhere,
with radial blends on `[ρ/2, 3ρ/4]` (inner) and `[ρ/8, ρ/4]` (outer), lens switch `[β, β']` and the
outer weight `nuThree 1 δ`. Nine open pieces (`pieceApexOne`, …, `pieceJunctionTwo`) carry one
formula each: on each piece `preFold` equals the formula (`preFold_eq_*`), the formula is smooth
and has positive Jacobian off `v₁, v₂` (`contDiffAt_*`, `det_*`).
-/

set_option autoImplicit false

noncomputable section

open Complex Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

theorem halfArg_lt_negHalfArg_of_re {S R J R' J' : ℝ} (hS : 0 < S) (hR : 0 < R) (hR' : R' < 0)
    (h : R ^ 2 + J ^ 2 = S ^ 2) (h' : R' ^ 2 + J' ^ 2 = S ^ 2) :
    halfArg S R J < negHalfArg S R' J' := by
  have hJ : J ^ 2 ≤ S ^ 2 := by nlinarith [sq_nonneg R]
  have hJ' : J' ^ 2 ≤ S ^ 2 := by nlinarith [sq_nonneg R']
  have hq : J / (S + R) < 1 := by
    rw [div_lt_one (by linarith)]
    nlinarith [sq_nonneg (J - S)]
  have hq' : J' / (S - R') < 1 := by
    rw [div_lt_one (by linarith)]
    nlinarith [sq_nonneg (J' - S)]
  have a1 : Real.arctan (J / (S + R)) < Real.pi / 4 := by
    rw [← Real.arctan_one]
    exact Real.arctan_strictMono hq
  have a2 : Real.arctan (J' / (S - R')) < Real.pi / 4 := by
    rw [← Real.arctan_one]
    exact Real.arctan_strictMono hq'
  unfold halfArg negHalfArg
  linarith

namespace EuclidShape

variable (σ : EuclidShape)

theorem eventually_mem_and_pos {s : Set ℂ} (hs : IsOpen s) {z : ℂ} (hz : z ∈ s) {g : ℂ → ℝ}
    (hg : ContinuousAt g z) (hpos : 0 < g z) : ∀ᶠ u in 𝓝 z, u ∈ s ∧ 0 < g u :=
  Filter.Eventually.and (hs.mem_nhds hz) (hg.eventually (lt_mem_nhds hpos))

theorem psiOne_pos_of_domOne {z : ℂ} (hz : z ∈ σ.domOne) :
    0 < ‖σ.rotOne z‖ + (σ.rotOne z).re := by
  have h := hz.2.1
  rw [σ.norm_rotOne]
  have e : (σ.rotOne z).re = Real.sin σ.θ₂ - (exp (-((σ.θ₃ : ℂ) * I)) * z).re := by
    simp only [rotOne, mul_sub, neg_sub, sub_re, exp_neg_mul_vertexOne, ofReal_re]
  rw [e]
  exact h

theorem psiTwo_pos_of_domTwo {z : ℂ} (hz : z ∈ σ.domTwo) :
    0 < ‖σ.rotTwo z‖ + (σ.rotTwo z).re := by
  rw [σ.norm_rotTwo]
  exact hz.1

theorem psiThree_pos_of_domZero {z : ℂ} (hz : z ∈ σ.domZero) : 0 < ‖z‖ + z.re := hz.1

theorem det_polar_bridge {c : ℝ} {v z : ℂ} {r₀ : ℝ} {Θ : ℂ → ℝ} {g : ℂ → ℂ} (hzv : z ≠ v)
    (hev : g =ᶠ[𝓝 z] fun u => (c : ℂ) +
      ((3 / 2 + profileSlope * (‖u - v‖ - r₀) : ℝ) : ℂ) * exp ((Θ u : ℂ) * I))
    (hS : 0 < 3 / 2 + profileSlope * (‖z - v‖ - r₀)) (hΘ : DifferentiableAt ℝ Θ z)
    {D : ℝ} (hD : 0 < D) (hΘγ : HasDerivAt (fun t => Θ (circ v z t)) D 0) :
    0 < (fderiv ℝ g z).det := by
  have hd : 0 < ‖z - v‖ := norm_pos_iff.2 (sub_ne_zero.2 hzv)
  rw [hev.fderiv_eq]
  have hSd : HasDerivAt (fun d : ℝ => 3 / 2 + profileSlope * (d - r₀)) profileSlope ‖z - v‖ := by
    simpa using (((hasDerivAt_id' ‖z - v‖).sub_const r₀).const_mul profileSlope).const_add
      (3 / 2 : ℝ)
  have hρ : DifferentiableAt ℝ (fun u => ‖u - v‖) z :=
    ((contDiffAt_id.sub contDiffAt_const).norm ℝ (sub_ne_zero.2 hzv) :
      ContDiffAt ℝ ∞ (fun u => ‖u - v‖) z).differentiableAt (by simp)
  have hργ : ∀ᶠ t in 𝓝 (0 : ℝ), ‖circ v z t - v‖ = ‖z - v‖ :=
    Eventually.of_forall fun t => norm_circ_sub _ _ _
  have key := det_fderiv_polar (c := (c : ℂ)) (S := fun d : ℝ => 3 / 2 + profileSlope * (d - r₀))
    (ρ := fun u => ‖u - v‖) (Θ := Θ) (N := z - v) hSd hρ hΘ (hasDerivAt_circ v z)
    (circ_zero _ _) hργ hΘγ (hasDerivAt_norm_ray z v) (hasDerivAt_comp_ray hΘ)
  rw [cross_mul_I] at key
  have hκ : (0 : ℝ) < profileSlope := by unfold profileSlope; norm_num
  exact det_pos_of_polar (by positivity) key (by positivity)

theorem det_fderiv_bridgeOne_pos {z : ℂ} (hz : z ∈ σ.domOne)
    (hpos : 0 < σ.modOne z + ((σ.bridgeOne z).re - 3 / 2)) :
    0 < (fderiv ℝ σ.bridgeOne z).det := by
  have h1 := σ.ne_vertexOne_of_mem_domOne hz
  have hcont : ContinuousAt (fun u => σ.modOne u + ((σ.bridgeOne u).re - 3 / 2)) z :=
    ((σ.contDiffAt_modOne h1).continuousAt).add
      ((contDiffAt_re_comp (σ.contDiffAt_bridgeOne hz)).continuousAt.sub continuousAt_const)
  have hev : σ.bridgeOne =ᶠ[𝓝 z] fun u => ((3 / 2 : ℝ) : ℂ) +
      ((3 / 2 + profileSlope * (‖u - σ.vertexOne‖ - σ.radOne) : ℝ) : ℂ) *
        exp ((σ.angleOneAtOne u : ℂ) * I) := by
    filter_upwards [eventually_mem_and_pos σ.isOpen_domOne hz hcont hpos] with u hu
    exact σ.bridgeOne_eq_polar_one hu.1 hu.2
  obtain ⟨D, hD, hΘγ⟩ := σ.exists_hasDerivAt_angleOneAtOne hz hpos (σ.psiOne_pos_of_domOne hz)
  exact det_polar_bridge h1 hev (σ.modOne_pos z)
    ((σ.contDiffAt_angleOneAtOne hz hpos).differentiableAt (by simp)) hD hΘγ

theorem det_fderiv_bridgeTwo_pos {z : ℂ} (hz : z ∈ σ.domTwo)
    (hpos : 0 < σ.modOne z - ((σ.bridgeTwo z).re - 3 / 2)) :
    0 < (fderiv ℝ σ.bridgeTwo z).det := by
  have h1 := σ.ne_vertexOne_of_mem_domTwo hz
  have hcont : ContinuousAt (fun u => σ.modOne u - ((σ.bridgeTwo u).re - 3 / 2)) z :=
    ((σ.contDiffAt_modOne h1).continuousAt).sub
      ((contDiffAt_re_comp (σ.contDiffAt_bridgeTwo hz)).continuousAt.sub continuousAt_const)
  have hev : σ.bridgeTwo =ᶠ[𝓝 z] fun u => ((3 / 2 : ℝ) : ℂ) +
      ((3 / 2 + profileSlope * (‖u - σ.vertexOne‖ - σ.radOne) : ℝ) : ℂ) *
        exp ((σ.angleTwoAtOne u : ℂ) * I) := by
    filter_upwards [eventually_mem_and_pos σ.isOpen_domTwo hz hcont hpos] with u hu
    exact σ.bridgeTwo_eq_polar_one hu.1 hu.2
  obtain ⟨D, hD, hΘγ⟩ := σ.exists_hasDerivAt_angleTwoAtOne hz hpos
  exact det_polar_bridge h1 hev (σ.modOne_pos z)
    ((σ.contDiffAt_angleTwoAtOne hz hpos).differentiableAt (by simp)) hD hΘγ

theorem det_fderiv_bridgeZero_pos {z : ℂ} (hz : z ∈ σ.domZero)
    (hpos : 0 < σ.modTwo z - ((σ.bridgeZero z).re + 3 / 2)) :
    0 < (fderiv ℝ σ.bridgeZero z).det := by
  have h2 := σ.ne_vertexTwo_of_mem_domZero hz
  have hcont : ContinuousAt (fun u => σ.modTwo u - ((σ.bridgeZero u).re + 3 / 2)) z :=
    ((σ.contDiffAt_modTwo h2).continuousAt).sub
      ((contDiffAt_re_comp (σ.contDiffAt_bridgeZero hz)).continuousAt.add continuousAt_const)
  have hev : σ.bridgeZero =ᶠ[𝓝 z] fun u => ((-(3 / 2) : ℝ) : ℂ) +
      ((3 / 2 + profileSlope * (‖u - σ.vertexTwo‖ - σ.radTwo) : ℝ) : ℂ) *
        exp ((σ.angleZeroAtTwo u : ℂ) * I) := by
    filter_upwards [eventually_mem_and_pos σ.isOpen_domZero hz hcont hpos] with u hu
    exact σ.bridgeZero_eq_polar_two hu.1 hu.2
  obtain ⟨D, hD, hΘγ⟩ := σ.exists_hasDerivAt_angleZeroAtTwo hz hpos
  exact det_polar_bridge h2 hev (σ.modTwo_pos z)
    ((σ.contDiffAt_angleZeroAtTwo hz hpos).differentiableAt (by simp)) hD hΘγ


def germRadius : ℝ := σ.inradius / 3

def blendStart : ℝ := σ.inradius / 2

def blendEnd : ℝ := 3 * σ.inradius / 4

def outerGermRadius : ℝ := σ.inradius / 16

def outerBlendStart : ℝ := σ.inradius / 8

def outerBlendEnd : ℝ := σ.inradius / 4

def foldCornerOne : ℂ → ℂ := σ.cornerOne σ.blendStart σ.blendEnd σ.lensWidth σ.switchTop

def foldCornerTwo : ℂ → ℂ := σ.cornerTwo σ.blendStart σ.blendEnd σ.lensWidth σ.switchTop

def foldCornerThree : ℂ → ℂ := σ.cornerThree σ.outerBlendStart σ.outerBlendEnd 1 σ.cornerShrink

def foldBlend : ℂ → ℝ := σ.blendThree 1 σ.cornerShrink

def preFold (z : ℂ) : ℂ :=
  if ‖z - σ.vertexOne‖ < σ.germRadius then σ.apexOne z
  else if ‖z - σ.vertexTwo‖ < σ.germRadius then σ.apexTwo z
  else if ‖z‖ < σ.outerGermRadius then compactOuterGerm σ.p₃ z
  else if ‖z - σ.vertexOne‖ < σ.radOne - σ.cornerShrink then σ.foldCornerOne z
  else if ‖z - σ.vertexTwo‖ < σ.radTwo - σ.cornerShrink then σ.foldCornerTwo z
  else if |σ.wallSide 2 z| < σ.lensWidth then σ.bridgeTwo z
  else σ.foldCornerThree z

def validOne : Set ℂ :=
  {z | z ∈ σ.domOne ∧ z ∈ σ.domTwo ∧ 3 / 2 < (σ.bridgeOne z).re ∧ (σ.bridgeTwo z).re < 3 / 2 ∧
    ((σ.rotTwo z).re - Real.sin σ.θ₃ < 0 ∨ σ.switchTop < σ.wallSide 2 z ∨
      σ.wallSide 2 z < σ.lensWidth)}

def validTwo : Set ℂ :=
  {z | z ∈ σ.domTwo ∧ z ∈ σ.domZero ∧ -(3 / 2) < (σ.bridgeTwo z).re ∧
    (σ.bridgeZero z).re < -(3 / 2) ∧
    (0 < (σ.rotTwo z).re ∨ σ.switchTop < σ.wallSide 2 z ∨ σ.wallSide 2 z < σ.lensWidth)}

def validThree : Set ℂ :=
  {z | z ∈ σ.domOne ∧ z ∈ σ.domZero ∧ 0 < (σ.bridgeOne z).re ∧ (σ.bridgeZero z).re < 0 ∧
    ((0 < σ.wallSide 0 z ∧ 0 < σ.wallSide 1 z) ∨ 1 < σ.foldBlend z ∨ σ.foldBlend z < -1)}

def validLens : Set ℂ :=
  {z | z ∈ σ.domTwo ∧ -(3 / 2) < (σ.bridgeTwo z).re ∧ (σ.bridgeTwo z).re < 3 / 2}

def validJunctionOne : Set ℂ :=
  {z | z ∈ σ.domOne ∧ 0 < ‖z‖ + z.re ∧ 3 / 2 < (σ.bridgeOne z).re}

def validJunctionTwo : Set ℂ := {z | z ∈ σ.domZero ∧ (σ.bridgeZero z).re < -(3 / 2)}

def pieceApexOne : Set ℂ := {z | ‖z - σ.vertexOne‖ < σ.germRadius}

def pieceApexTwo : Set ℂ := {z | ‖z - σ.vertexTwo‖ < σ.germRadius}

def pieceOuter : Set ℂ := {z | 0 < ‖z‖ ∧ ‖z‖ < σ.outerGermRadius}

def pieceCornerOne : Set ℂ :=
  {z | σ.germRadius / 2 < ‖z - σ.vertexOne‖ ∧ ‖z - σ.vertexOne‖ < σ.radOne - σ.cornerShrink} ∩
    σ.validOne

def pieceCornerTwo : Set ℂ :=
  {z | σ.germRadius / 2 < ‖z - σ.vertexTwo‖ ∧ ‖z - σ.vertexTwo‖ < σ.radTwo - σ.cornerShrink} ∩
    σ.validTwo

def pieceLens : Set ℂ :=
  {z | σ.blendEnd < ‖z - σ.vertexOne‖ ∧ σ.blendEnd < ‖z - σ.vertexTwo‖ ∧
    |σ.wallSide 2 z| < σ.lensWidth} ∩ σ.validLens

def pieceCornerThree : Set ℂ :=
  {z | σ.radOne - σ.cornerShrink < ‖z - σ.vertexOne‖ ∧
    σ.radTwo - σ.cornerShrink < ‖z - σ.vertexTwo‖ ∧ σ.lensWidth < |σ.wallSide 2 z| ∧
    σ.outerGermRadius / 2 < ‖z‖} ∩ σ.validThree

def pieceJunctionOne : Set ℂ :=
  {z | σ.blendEnd < ‖z - σ.vertexOne‖ ∧ σ.radTwo - σ.cornerShrink < ‖z - σ.vertexTwo‖ ∧
    σ.switchTop < σ.wallSide 2 z ∧ σ.outerBlendEnd < ‖z‖ ∧ 1 < σ.foldBlend z} ∩
    σ.validJunctionOne

def pieceJunctionTwo : Set ℂ :=
  {z | σ.blendEnd < ‖z - σ.vertexTwo‖ ∧ σ.radOne - σ.cornerShrink < ‖z - σ.vertexOne‖ ∧
    σ.switchTop < σ.wallSide 2 z ∧ σ.outerBlendEnd < ‖z‖ ∧ σ.foldBlend z < -1} ∩
    σ.validJunctionTwo


theorem params :
    0 < σ.inradius ∧ σ.germRadius < σ.blendStart ∧ σ.blendStart < σ.blendEnd ∧
      σ.blendEnd < σ.radOne - σ.cornerShrink ∧ σ.blendEnd < σ.radTwo - σ.cornerShrink ∧
      σ.blendEnd ≤ 1 ∧ 0 < σ.outerGermRadius ∧ σ.outerGermRadius < σ.outerBlendStart ∧
      σ.outerBlendStart < σ.outerBlendEnd ∧ σ.outerBlendEnd ≤ 1 / 5 ∧
      σ.lensWidth < σ.switchTop ∧ 0 < σ.cornerShrink ∧ 0 < σ.germRadius ∧
      σ.outerBlendEnd < σ.radThree ∧ 0 < σ.lensWidth := by
  have hρ := σ.inradius_pos
  have h1 := σ.inradius_le_radOne
  have h2 := σ.inradius_le_radTwo
  have h3 := σ.inradius_le_radThree
  have hh := σ.inradius_lt_half
  unfold germRadius blendStart blendEnd outerGermRadius outerBlendStart outerBlendEnd lensWidth
    switchTop cornerShrink
  refine ⟨hρ, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> linarith

theorem triangle_vertexOne_vertexTwo (z : ℂ) :
    Real.sin σ.θ₃ ≤ ‖z - σ.vertexOne‖ + ‖z - σ.vertexTwo‖ := by
  have h := norm_sub_le_norm_sub_add_norm_sub σ.vertexOne z σ.vertexTwo
  rw [norm_vertexOne_sub_vertexTwo, ← norm_neg (σ.vertexOne - z), neg_sub] at h
  exact h

theorem norm_sub_vertexTwo_ge (z : ℂ) :
    Real.sin σ.θ₃ - ‖z - σ.vertexOne‖ ≤ ‖z - σ.vertexTwo‖ := by
  linarith [σ.triangle_vertexOne_vertexTwo z]

theorem norm_sub_vertexOne_ge (z : ℂ) :
    Real.sin σ.θ₃ - ‖z - σ.vertexTwo‖ ≤ ‖z - σ.vertexOne‖ := by
  linarith [σ.triangle_vertexOne_vertexTwo z]

theorem norm_ge_of_vertexOne (z : ℂ) : Real.sin σ.θ₂ - ‖z - σ.vertexOne‖ ≤ ‖z‖ := by
  have h := norm_sub_le_norm_sub_add_norm_sub σ.vertexOne z 0
  rw [sub_zero, sub_zero, norm_vertexOne, ← norm_neg (σ.vertexOne - z), neg_sub] at h
  linarith

theorem norm_ge_of_vertexTwo (z : ℂ) : Real.sin σ.θ₁ - ‖z - σ.vertexTwo‖ ≤ ‖z‖ := by
  have h := norm_sub_le_norm_sub_add_norm_sub σ.vertexTwo z 0
  rw [sub_zero, sub_zero, norm_vertexTwo, ← norm_neg (σ.vertexTwo - z), neg_sub] at h
  linarith

theorem abs_wallSide_two_sub_le (z w : ℂ) : |σ.wallSide 2 z - σ.wallSide 2 w| ≤ ‖z - w‖ := by
  change |(σ.rotTwo z).im - (σ.rotTwo w).im| ≤ _
  rw [σ.norm_sub_eq_rotTwo, ← sub_im]
  exact Complex.abs_im_le_norm _

theorem norm_ge_of_lens {z : ℂ} (h : |σ.wallSide 2 z| < σ.lensWidth) :
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
  unfold lensWidth at h
  linarith [hl.1]


theorem radThree_add : σ.radTwo + σ.radThree = Real.sin σ.θ₁ := σ.radTwo_add_radThree

theorem far_of_cornerOne {z : ℂ} (h : ‖z - σ.vertexOne‖ < σ.radOne - σ.cornerShrink) :
    σ.radTwo + σ.cornerShrink < ‖z - σ.vertexTwo‖ ∧ σ.radThree + σ.cornerShrink < ‖z‖ := by
  have a := σ.norm_sub_vertexTwo_ge z
  have b := σ.norm_ge_of_vertexOne z
  have h12 := σ.radOne_add_radTwo
  have h13 := σ.radOne_add_radThree
  constructor <;> linarith

theorem far_of_cornerTwo {z : ℂ} (h : ‖z - σ.vertexTwo‖ < σ.radTwo - σ.cornerShrink) :
    σ.radOne + σ.cornerShrink < ‖z - σ.vertexOne‖ ∧ σ.radThree + σ.cornerShrink < ‖z‖ := by
  have a := σ.norm_sub_vertexOne_ge z
  have b := σ.norm_ge_of_vertexTwo z
  have h12 := σ.radOne_add_radTwo
  have h23 := σ.radTwo_add_radThree
  constructor <;> linarith

theorem preFold_eq_apexOne {z : ℂ} (hz : z ∈ σ.pieceApexOne) : σ.preFold z = σ.apexOne z := by
  change ‖z - σ.vertexOne‖ < σ.germRadius at hz
  simp only [preFold, hz, ↓reduceIte]

theorem preFold_eq_apexTwo {z : ℂ} (hz : z ∈ σ.pieceApexTwo) : σ.preFold z = σ.apexTwo z := by
  change ‖z - σ.vertexTwo‖ < σ.germRadius at hz
  have hp := σ.params
  have h1 : ¬ ‖z - σ.vertexOne‖ < σ.germRadius := by
    have := σ.far_of_cornerTwo (lt_trans hz (by linarith [hp.2.1, hp.2.2.1, hp.2.2.2.2.1]))
    have := σ.inradius_le_radOne
    unfold germRadius at hz ⊢
    linarith
  simp only [preFold, h1, hz, ↓reduceIte]

theorem preFold_eq_outer {z : ℂ} (hz : z ∈ σ.pieceOuter) :
    σ.preFold z = compactOuterGerm σ.p₃ z := by
  change 0 < ‖z‖ ∧ ‖z‖ < σ.outerGermRadius at hz
  have hp := σ.params
  have h3 := σ.inradius_le_radThree
  have hc1 : ¬ ‖z - σ.vertexOne‖ < σ.germRadius := by
    intro h
    have := (σ.far_of_cornerOne (lt_trans h (by linarith [hp.2.1, hp.2.2.1, hp.2.2.2.1]))).2
    unfold outerGermRadius at hz
    linarith [hz.2]
  have hc2 : ¬ ‖z - σ.vertexTwo‖ < σ.germRadius := by
    intro h
    have := (σ.far_of_cornerTwo (lt_trans h (by linarith [hp.2.1, hp.2.2.1,
      hp.2.2.2.2.1]))).2
    unfold outerGermRadius at hz
    linarith [hz.2]
  simp only [preFold, hc1, hc2, hz.2, ↓reduceIte]

theorem preFold_eq_cornerOne {z : ℂ} (hz : z ∈ σ.pieceCornerOne) :
    σ.preFold z = σ.foldCornerOne z := by
  have hp := σ.params
  obtain ⟨⟨hg, hr⟩, hv⟩ := hz
  have hfar := σ.far_of_cornerOne hr
  have h2 := σ.inradius_le_radTwo
  have h3 := σ.inradius_le_radThree
  have hc2 : ¬ ‖z - σ.vertexTwo‖ < σ.germRadius := by
    unfold germRadius cornerShrink at *
    linarith [hfar.1]
  have hc3 : ¬ ‖z‖ < σ.outerGermRadius := by
    unfold outerGermRadius cornerShrink at *
    linarith [hfar.2]
  rcases lt_or_ge ‖z - σ.vertexOne‖ σ.germRadius with h1 | h1
  · simp only [preFold, h1, ↓reduceIte, foldCornerOne]
    exact (σ.cornerOne_eq_apexOne hp.2.2.1 (by unfold blendStart; linarith [hp.1])
      (by linarith [hp.2.1]) (Or.inr (σ.psiOne_pos_of_domOne hv.1))).symm
  · have h1' : ¬ ‖z - σ.vertexOne‖ < σ.germRadius := not_lt.2 h1
    simp only [preFold, h1', hc2, hc3, hr, ↓reduceIte]

theorem preFold_eq_cornerTwo {z : ℂ} (hz : z ∈ σ.pieceCornerTwo) :
    σ.preFold z = σ.foldCornerTwo z := by
  have hp := σ.params
  obtain ⟨⟨hg, hr⟩, hv⟩ := hz
  have hfar := σ.far_of_cornerTwo hr
  have h1' := σ.inradius_le_radOne
  have h3 := σ.inradius_le_radThree
  have hc1 : ¬ ‖z - σ.vertexOne‖ < σ.germRadius := by
    unfold germRadius cornerShrink at *
    linarith [hfar.1]
  have hc3 : ¬ ‖z‖ < σ.outerGermRadius := by
    unfold outerGermRadius cornerShrink at *
    linarith [hfar.2]
  have hc4 : ¬ ‖z - σ.vertexOne‖ < σ.radOne - σ.cornerShrink := by
    linarith [hfar.1, hp.2.2.2.2.2.2.2.2.2.2.2.1]
  rcases lt_or_ge ‖z - σ.vertexTwo‖ σ.germRadius with h2 | h2
  · simp only [preFold, hc1, h2, ↓reduceIte, foldCornerTwo]
    exact (σ.cornerTwo_eq_apexTwo hp.2.2.1 (by unfold blendStart; linarith [hp.1])
      (by linarith [hp.2.1]) (Or.inr (σ.psiTwo_pos_of_domTwo hv.1))).symm
  · have h2' : ¬ ‖z - σ.vertexTwo‖ < σ.germRadius := not_lt.2 h2
    simp only [preFold, hc1, h2', hc3, hc4, hr, ↓reduceIte]


theorem germ_lt_blendEnd : σ.germRadius < σ.blendEnd := by
  have hp := σ.params
  linarith [hp.2.1, hp.2.2.1]

theorem not_germOne_of_gt {z : ℂ} (h : σ.blendEnd < ‖z - σ.vertexOne‖) :
    ¬ ‖z - σ.vertexOne‖ < σ.germRadius := by
  have := σ.germ_lt_blendEnd
  intro h'
  linarith

theorem not_germTwo_of_gt {z : ℂ} (h : σ.blendEnd < ‖z - σ.vertexTwo‖) :
    ¬ ‖z - σ.vertexTwo‖ < σ.germRadius := by
  have := σ.germ_lt_blendEnd
  intro h'
  linarith

theorem preFold_eq_lens {z : ℂ} (hz : z ∈ σ.pieceLens) : σ.preFold z = σ.bridgeTwo z := by
  have hp := σ.params
  obtain ⟨⟨h1, h2, hw⟩, hv⟩ := hz
  have hn := σ.norm_ge_of_lens hw
  have hc3 : ¬ ‖z‖ < σ.outerGermRadius := not_lt.2 hn.le
  have hw' : σ.wallSide 2 z ≤ σ.lensWidth := le_trans (le_abs_self _) hw.le
  by_cases hr1 : ‖z - σ.vertexOne‖ < σ.radOne - σ.cornerShrink
  · simp only [preFold, σ.not_germOne_of_gt h1, σ.not_germTwo_of_gt h2, hc3, hr1, ↓reduceIte,
      foldCornerOne]
    exact σ.cornerOne_eq_bridgeTwo hp.2.2.1 hp.2.2.2.2.2.2.2.2.2.2.1 hv.1
      (by linarith [hv.2.2, σ.modOne_pos z]) h1.le hw'
  by_cases hr2 : ‖z - σ.vertexTwo‖ < σ.radTwo - σ.cornerShrink
  · simp only [preFold, σ.not_germOne_of_gt h1, σ.not_germTwo_of_gt h2, hc3, hr1, hr2,
      ↓reduceIte, foldCornerTwo]
    exact σ.cornerTwo_eq_bridgeTwo hp.2.2.1 hp.2.2.2.2.2.2.2.2.2.2.1 hv.1
      (by linarith [hv.2.1, σ.modTwo_pos z]) h2.le hw'
  simp only [preFold, σ.not_germOne_of_gt h1, σ.not_germTwo_of_gt h2, hc3, hr1, hr2, hw,
    ↓reduceIte]

theorem preFold_eq_cornerThree {z : ℂ} (hz : z ∈ σ.pieceCornerThree) :
    σ.preFold z = σ.foldCornerThree z := by
  have hp := σ.params
  obtain ⟨⟨h1, h2, hw, hn⟩, hv⟩ := hz
  have hc1 : ¬ ‖z - σ.vertexOne‖ < σ.germRadius :=
    σ.not_germOne_of_gt (lt_trans hp.2.2.2.1 h1)
  have hc2 : ¬ ‖z - σ.vertexTwo‖ < σ.germRadius :=
    σ.not_germTwo_of_gt (lt_trans hp.2.2.2.2.1 h2)
  have hr1 : ¬ ‖z - σ.vertexOne‖ < σ.radOne - σ.cornerShrink := not_lt.2 h1.le
  have hr2 : ¬ ‖z - σ.vertexTwo‖ < σ.radTwo - σ.cornerShrink := not_lt.2 h2.le
  have hl : ¬ |σ.wallSide 2 z| < σ.lensWidth := not_lt.2 hw.le
  by_cases h3 : ‖z‖ < σ.outerGermRadius
  · simp only [preFold, hc1, hc2, h3, ↓reduceIte, foldCornerThree]
    exact (σ.cornerThree_eq_outerGerm hp.2.2.2.2.2.2.2.2.1
      (by linarith [hp.2.2.2.2.2.2.2.1]) (σ.psiThree_pos_of_domZero hv.2.1)).symm
  · simp only [preFold, hc1, hc2, h3, hr1, hr2, hl, ↓reduceIte]

theorem preFold_eq_junctionOne {z : ℂ} (hz : z ∈ σ.pieceJunctionOne) :
    σ.preFold z = σ.bridgeOne z := by
  have hp := σ.params
  obtain ⟨⟨h1, h2, hw, hn, hb⟩, hv⟩ := hz
  have hc2 : ¬ ‖z - σ.vertexTwo‖ < σ.germRadius :=
    σ.not_germTwo_of_gt (lt_trans hp.2.2.2.2.1 h2)
  have hc3 : ¬ ‖z‖ < σ.outerGermRadius := by
    have := hp.2.2.2.2.2.2.2.1
    have := hp.2.2.2.2.2.2.2.2.1
    intro h
    linarith
  have hr2 : ¬ ‖z - σ.vertexTwo‖ < σ.radTwo - σ.cornerShrink := not_lt.2 h2.le
  have hwβ : σ.lensWidth < σ.wallSide 2 z := lt_trans hp.2.2.2.2.2.2.2.2.2.2.1 hw
  have hl : ¬ |σ.wallSide 2 z| < σ.lensWidth := not_lt.2 (le_trans hwβ.le (le_abs_self _))
  by_cases hr1 : ‖z - σ.vertexOne‖ < σ.radOne - σ.cornerShrink
  · simp only [preFold, σ.not_germOne_of_gt h1, hc2, hc3, hr1, ↓reduceIte, foldCornerOne]
    exact σ.cornerOne_eq_bridgeOne hp.2.2.1 hp.2.2.2.2.2.2.2.2.2.2.1 hv.1
      (by linarith [hv.2.2, σ.modOne_pos z]) h1.le hw.le
  · simp only [preFold, σ.not_germOne_of_gt h1, hc2, hc3, hr1, hr2, hl, ↓reduceIte,
      foldCornerThree]
    exact σ.cornerThree_eq_bridgeOne hp.2.2.2.2.2.2.2.2.1 one_pos hv.1
      (by linarith [hv.2.2, σ.modThree_pos hv.1.2.2]) hn.le hb.le

theorem preFold_eq_junctionTwo {z : ℂ} (hz : z ∈ σ.pieceJunctionTwo) :
    σ.preFold z = σ.bridgeZero z := by
  have hp := σ.params
  obtain ⟨⟨h2, h1, hw, hn, hb⟩, hv⟩ := hz
  have hc1 : ¬ ‖z - σ.vertexOne‖ < σ.germRadius :=
    σ.not_germOne_of_gt (lt_trans hp.2.2.2.1 h1)
  have hc3 : ¬ ‖z‖ < σ.outerGermRadius := by
    have := hp.2.2.2.2.2.2.2.1
    have := hp.2.2.2.2.2.2.2.2.1
    intro h
    linarith
  have hr1 : ¬ ‖z - σ.vertexOne‖ < σ.radOne - σ.cornerShrink := not_lt.2 h1.le
  have hwβ : σ.lensWidth < σ.wallSide 2 z := lt_trans hp.2.2.2.2.2.2.2.2.2.2.1 hw
  have hl : ¬ |σ.wallSide 2 z| < σ.lensWidth := not_lt.2 (le_trans hwβ.le (le_abs_self _))
  by_cases hr2 : ‖z - σ.vertexTwo‖ < σ.radTwo - σ.cornerShrink
  · simp only [preFold, hc1, σ.not_germTwo_of_gt h2, hc3, hr1, hr2, ↓reduceIte, foldCornerTwo]
    exact σ.cornerTwo_eq_bridgeZero hp.2.2.1 hp.2.2.2.2.2.2.2.2.2.2.1 hv.1
      (by linarith [hv.2, σ.modTwo_pos z]) h2.le hw.le
  · simp only [preFold, hc1, σ.not_germTwo_of_gt h2, hc3, hr1, hr2, hl, ↓reduceIte,
      foldCornerThree]
    exact σ.cornerThree_eq_bridgeZero hp.2.2.2.2.2.2.2.2.1 one_pos hv.1
      (by linarith [hv.2, σ.modThree_pos hv.1.2.2]) hn.le hb.le


theorem sq_of_bridgeOne_one {z : ℂ} (hz : z ∈ σ.domOne) :
    ((σ.bridgeOne z).re - 3 / 2) ^ 2 + (σ.bridgeOne z).im ^ 2 = σ.modOne z ^ 2 := by
  have h := polar_of_norm_sub (σ.bridgeOne z) (3 / 2) (by simp) (σ.norm_bridgeOne hz).2
  simpa using h

theorem sq_of_bridgeTwo_one {z : ℂ} (hz : z ∈ σ.domTwo) :
    ((σ.bridgeTwo z).re - 3 / 2) ^ 2 + (σ.bridgeTwo z).im ^ 2 = σ.modOne z ^ 2 := by
  have h := polar_of_norm_sub (σ.bridgeTwo z) (3 / 2) (by simp) (σ.norm_bridgeTwo hz).1
  simpa using h

theorem sq_of_bridgeTwo_two {z : ℂ} (hz : z ∈ σ.domTwo) :
    ((σ.bridgeTwo z).re + 3 / 2) ^ 2 + (σ.bridgeTwo z).im ^ 2 = σ.modTwo z ^ 2 := by
  have e : ‖σ.bridgeTwo z - -(3 / 2)‖ = σ.modTwo z := by
    rw [sub_neg_eq_add]; exact (σ.norm_bridgeTwo hz).2
  have h := polar_of_norm_sub (σ.bridgeTwo z) (-(3 / 2)) (by simp) e
  simpa using h

theorem sq_of_bridgeZero_two {z : ℂ} (hz : z ∈ σ.domZero) :
    ((σ.bridgeZero z).re + 3 / 2) ^ 2 + (σ.bridgeZero z).im ^ 2 = σ.modTwo z ^ 2 := by
  have e : ‖σ.bridgeZero z - -(3 / 2)‖ = σ.modTwo z := by
    rw [sub_neg_eq_add]; exact (σ.norm_bridgeZero hz).2
  have h := polar_of_norm_sub (σ.bridgeZero z) (-(3 / 2)) (by simp) e
  simpa using h

theorem sq_of_bridgeOne_three {z : ℂ} (hz : z ∈ σ.domOne) :
    (σ.bridgeOne z).re ^ 2 + (σ.bridgeOne z).im ^ 2 = σ.modThree z ^ 2 := by
  have e : ‖σ.bridgeOne z - 0‖ = σ.modThree z := by
    rw [sub_zero]; exact (σ.norm_bridgeOne hz).1
  have h := polar_of_norm_sub (σ.bridgeOne z) 0 (by simp) e
  simpa using h

theorem sq_of_bridgeZero_three {z : ℂ} (hz : z ∈ σ.domZero) :
    (σ.bridgeZero z).re ^ 2 + (σ.bridgeZero z).im ^ 2 = σ.modThree z ^ 2 := by
  have e : ‖σ.bridgeZero z - 0‖ = σ.modThree z := by
    rw [sub_zero]; exact (σ.norm_bridgeZero hz).1
  have h := polar_of_norm_sub (σ.bridgeZero z) 0 (by simp) e
  simpa using h

theorem good_cornerOne {z : ℂ} (hz : z ∈ σ.pieceCornerOne) :
    ContDiffAt ℝ ∞ σ.foldCornerOne z ∧ 0 < (fderiv ℝ σ.foldCornerOne z).det := by
  have hp := σ.params
  obtain ⟨-, h1, h2, hr1, hr2, hlam⟩ := hz
  have hψ := σ.psiOne_pos_of_domOne h1
  have hpos1 : 0 < σ.modOne z + ((σ.bridgeOne z).re - 3 / 2) := by
    linarith [σ.modOne_pos z]
  have hpos2 : 0 < σ.modOne z - ((σ.bridgeTwo z).re - 3 / 2) := by
    linarith [σ.modOne_pos z]
  have hord : σ.angleOneAtOne z ≤ σ.angleTwoAtOne z :=
    (halfArg_lt_negHalfArg_of_re (σ.modOne_pos z) (by linarith) (by linarith)
      (σ.sq_of_bridgeOne_one h1) (σ.sq_of_bridgeTwo_one h2)).le
  refine ⟨σ.contDiffAt_cornerOne _ _ _ _ h1 h2 hψ hpos1 hpos2, ?_⟩
  exact σ.det_fderiv_cornerOne_pos hp.2.2.1 hp.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.2.2.1 h1 h2 hψ
    hpos1 hpos2 hord (hlam.imp_left le_of_lt)

theorem good_cornerTwo {z : ℂ} (hz : z ∈ σ.pieceCornerTwo) :
    ContDiffAt ℝ ∞ σ.foldCornerTwo z ∧ 0 < (fderiv ℝ σ.foldCornerTwo z).det := by
  have hp := σ.params
  obtain ⟨-, h2, h0, hr2, hr0, hlam⟩ := hz
  have hψ := σ.psiTwo_pos_of_domTwo h2
  have hpos2 : 0 < σ.modTwo z + ((σ.bridgeTwo z).re + 3 / 2) := by
    linarith [σ.modTwo_pos z]
  have hpos0 : 0 < σ.modTwo z - ((σ.bridgeZero z).re + 3 / 2) := by
    linarith [σ.modTwo_pos z]
  have hord : σ.angleTwoAtTwo z ≤ σ.angleZeroAtTwo z :=
    (halfArg_lt_negHalfArg_of_re (σ.modTwo_pos z) (by linarith) (by linarith)
      (σ.sq_of_bridgeTwo_two h2) (σ.sq_of_bridgeZero_two h0)).le
  refine ⟨σ.contDiffAt_cornerTwo _ _ _ _ h2 h0 hψ hpos2 hpos0, ?_⟩
  exact σ.det_fderiv_cornerTwo_pos hp.2.2.1 hp.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.2.2.1 h2 h0 hψ
    hpos2 hpos0 hord (hlam.imp_left le_of_lt)

theorem good_cornerThree {z : ℂ} (hz : z ∈ σ.pieceCornerThree) :
    ContDiffAt ℝ ∞ σ.foldCornerThree z ∧ 0 < (fderiv ℝ σ.foldCornerThree z).det := by
  have hp := σ.params
  obtain ⟨-, h1, h0, hr1, hr0, hside⟩ := hz
  have hψ := σ.psiThree_pos_of_domZero h0
  have hpos1 : 0 < σ.modThree z + (σ.bridgeOne z).re := by
    linarith [σ.modThree_pos h1.2.2]
  have hpos0 : 0 < σ.modThree z - (σ.bridgeZero z).re := by
    linarith [σ.modThree_pos h1.2.2]
  have hord : σ.angleOneAtThree z ≤ σ.angleZeroAtThree z :=
    (halfArg_lt_negHalfArg_of_re (σ.modThree_pos h1.2.2) hr1 hr0
      (σ.sq_of_bridgeOne_three h1) (σ.sq_of_bridgeZero_three h0)).le
  refine ⟨σ.contDiffAt_cornerThree _ _ _ _ h1 h0 hψ hpos1 hpos0, ?_⟩
  refine σ.det_fderiv_cornerThree_pos hp.2.2.2.2.2.2.2.2.1 hp.2.2.2.2.2.2.2.2.2.1 one_pos
    hp.2.2.2.2.2.2.2.2.2.2.2.1 h1 h0 hψ hpos1 hpos0 hord ?_
  rcases hside with ⟨a, b⟩ | h | h
  · exact Or.inl ⟨a.le, b.le⟩
  · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr h)


theorem ev_lt {f : ℂ → ℝ} {z : ℂ} {a : ℝ} (hf : ContinuousAt f z) (h : a < f z) :
    ∀ᶠ u in 𝓝 z, a < f u := hf.eventually (lt_mem_nhds h)

theorem ev_gt {f : ℂ → ℝ} {z : ℂ} {a : ℝ} (hf : ContinuousAt f z) (h : f z < a) :
    ∀ᶠ u in 𝓝 z, f u < a := hf.eventually (gt_mem_nhds h)

theorem contAt_dist (c z : ℂ) : ContinuousAt (fun u => ‖u - c‖) z :=
  (continuous_norm.comp (continuous_id.sub continuous_const)).continuousAt

theorem contAt_norm (z : ℂ) : ContinuousAt (fun u : ℂ => ‖u‖) z := continuous_norm.continuousAt

theorem contAt_wallSide (i : Fin 3) (z : ℂ) : ContinuousAt (σ.wallSide i) z :=
  (σ.contDiff_wallSide i).continuous.continuousAt

theorem contAt_abs_wallSide (z : ℂ) : ContinuousAt (fun u => |σ.wallSide 2 u|) z :=
  ((σ.contDiff_wallSide 2).continuous.abs).continuousAt

theorem contAt_re_rotTwo (z : ℂ) : ContinuousAt (fun u => (σ.rotTwo u).re) z :=
  (contDiff_re_aux.comp σ.contDiff_rotTwo).continuous.continuousAt

theorem contAt_reBridgeOne {z : ℂ} (hz : z ∈ σ.domOne) :
    ContinuousAt (fun u => (σ.bridgeOne u).re) z :=
  (contDiffAt_re_comp (σ.contDiffAt_bridgeOne hz)).continuousAt

theorem contAt_reBridgeTwo {z : ℂ} (hz : z ∈ σ.domTwo) :
    ContinuousAt (fun u => (σ.bridgeTwo u).re) z :=
  (contDiffAt_re_comp (σ.contDiffAt_bridgeTwo hz)).continuousAt

theorem contAt_reBridgeZero {z : ℂ} (hz : z ∈ σ.domZero) :
    ContinuousAt (fun u => (σ.bridgeZero u).re) z :=
  (contDiffAt_re_comp (σ.contDiffAt_bridgeZero hz)).continuousAt

theorem contAt_foldBlend {z : ℂ} (hψ : 0 < ‖z‖ + z.re) (h1 : z ≠ σ.vertexOne)
    (h2 : z ≠ σ.vertexTwo) : ContinuousAt σ.foldBlend z :=
  (σ.contDiffAt_blendThree 1 σ.cornerShrink hψ h1 h2).continuousAt

theorem contAt_normAddRe (z : ℂ) : ContinuousAt (fun u : ℂ => ‖u‖ + u.re) z :=
  (continuous_norm.add Complex.continuous_re).continuousAt

theorem isOpen_pieceApexOne : IsOpen σ.pieceApexOne :=
  isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const

theorem isOpen_pieceApexTwo : IsOpen σ.pieceApexTwo :=
  isOpen_lt (continuous_norm.comp (continuous_id.sub continuous_const)) continuous_const

theorem isOpen_pieceOuter : IsOpen σ.pieceOuter :=
  (isOpen_lt continuous_const continuous_norm).inter (isOpen_lt continuous_norm continuous_const)

theorem isOpen_pieceCornerOne : IsOpen σ.pieceCornerOne := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨⟨a1, a2⟩, h1, h2, b1, b2, hl⟩ := hz
  have hl' : ∀ᶠ u in 𝓝 z, (σ.rotTwo u).re - Real.sin σ.θ₃ < 0 ∨
      σ.switchTop < σ.wallSide 2 u ∨ σ.wallSide 2 u < σ.lensWidth := by
    rcases hl with h | h | h
    · exact (ev_gt ((σ.contAt_re_rotTwo z).sub continuousAt_const) h).mono fun u hu => Or.inl hu
    · exact (ev_lt (σ.contAt_wallSide 2 z) h).mono fun u hu => Or.inr (Or.inl hu)
    · exact (ev_gt (σ.contAt_wallSide 2 z) h).mono fun u hu => Or.inr (Or.inr hu)
  filter_upwards [ev_lt (contAt_dist σ.vertexOne z) a1, ev_gt (contAt_dist σ.vertexOne z) a2,
    σ.isOpen_domOne.mem_nhds h1, σ.isOpen_domTwo.mem_nhds h2,
    ev_lt (σ.contAt_reBridgeOne h1) b1, ev_gt (σ.contAt_reBridgeTwo h2) b2, hl'] with
    u c1 c2 c3 c4 c5 c6 c7
  exact ⟨⟨c1, c2⟩, c3, c4, c5, c6, c7⟩

theorem isOpen_pieceCornerTwo : IsOpen σ.pieceCornerTwo := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨⟨a1, a2⟩, h2, h0, b1, b2, hl⟩ := hz
  have hl' : ∀ᶠ u in 𝓝 z, 0 < (σ.rotTwo u).re ∨
      σ.switchTop < σ.wallSide 2 u ∨ σ.wallSide 2 u < σ.lensWidth := by
    rcases hl with h | h | h
    · exact (ev_lt (σ.contAt_re_rotTwo z) h).mono fun u hu => Or.inl hu
    · exact (ev_lt (σ.contAt_wallSide 2 z) h).mono fun u hu => Or.inr (Or.inl hu)
    · exact (ev_gt (σ.contAt_wallSide 2 z) h).mono fun u hu => Or.inr (Or.inr hu)
  filter_upwards [ev_lt (contAt_dist σ.vertexTwo z) a1, ev_gt (contAt_dist σ.vertexTwo z) a2,
    σ.isOpen_domTwo.mem_nhds h2, σ.isOpen_domZero.mem_nhds h0,
    ev_lt (σ.contAt_reBridgeTwo h2) b1, ev_gt (σ.contAt_reBridgeZero h0) b2, hl'] with
    u c1 c2 c3 c4 c5 c6 c7
  exact ⟨⟨c1, c2⟩, c3, c4, c5, c6, c7⟩

theorem isOpen_pieceLens : IsOpen σ.pieceLens := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨⟨a1, a2, a3⟩, h2, b1, b2⟩ := hz
  filter_upwards [ev_lt (contAt_dist σ.vertexOne z) a1, ev_lt (contAt_dist σ.vertexTwo z) a2,
    ev_gt (σ.contAt_abs_wallSide z) a3, σ.isOpen_domTwo.mem_nhds h2,
    ev_lt (σ.contAt_reBridgeTwo h2) b1, ev_gt (σ.contAt_reBridgeTwo h2) b2] with
    u c1 c2 c3 c4 c5 c6
  exact ⟨⟨c1, c2, c3⟩, c4, c5, c6⟩

theorem isOpen_pieceCornerThree : IsOpen σ.pieceCornerThree := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨⟨a1, a2, a3, a4⟩, h1, h0, b1, b2, hs⟩ := hz
  have hb := σ.contAt_foldBlend h0.1 (σ.ne_vertexOne_of_mem_domOne h1)
    (σ.ne_vertexTwo_of_mem_domZero h0)
  have hs' : ∀ᶠ u in 𝓝 z, (0 < σ.wallSide 0 u ∧ 0 < σ.wallSide 1 u) ∨ 1 < σ.foldBlend u ∨
      σ.foldBlend u < -1 := by
    rcases hs with ⟨p, q⟩ | h | h
    · filter_upwards [ev_lt (σ.contAt_wallSide 0 z) p, ev_lt (σ.contAt_wallSide 1 z) q] with
        u hp hq
      exact Or.inl ⟨hp, hq⟩
    · exact (ev_lt hb h).mono fun u hu => Or.inr (Or.inl hu)
    · exact (ev_gt hb h).mono fun u hu => Or.inr (Or.inr hu)
  filter_upwards [ev_lt (contAt_dist σ.vertexOne z) a1, ev_lt (contAt_dist σ.vertexTwo z) a2,
    ev_lt (σ.contAt_abs_wallSide z) a3, ev_lt (contAt_norm z) a4,
    σ.isOpen_domOne.mem_nhds h1, σ.isOpen_domZero.mem_nhds h0,
    ev_lt (σ.contAt_reBridgeOne h1) b1, ev_gt (σ.contAt_reBridgeZero h0) b2, hs'] with
    u c1 c2 c3 c4 c5 c6 c7 c8 c9
  exact ⟨⟨c1, c2, c3, c4⟩, c5, c6, c7, c8, c9⟩

theorem isOpen_pieceJunctionOne : IsOpen σ.pieceJunctionOne := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨⟨a1, a2, a3, a4, a5⟩, h1, hψ, b1⟩ := hz
  have hp := σ.params
  have h2 : z ≠ σ.vertexTwo := by
    rintro rfl
    rw [sub_self, norm_zero] at a2
    linarith [hp.2.2.2.2.1, hp.2.2.1, hp.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.2.1]
  have hb := σ.contAt_foldBlend hψ (σ.ne_vertexOne_of_mem_domOne h1) h2
  filter_upwards [ev_lt (contAt_dist σ.vertexOne z) a1, ev_lt (contAt_dist σ.vertexTwo z) a2,
    ev_lt (σ.contAt_wallSide 2 z) a3, ev_lt (contAt_norm z) a4, ev_lt hb a5,
    σ.isOpen_domOne.mem_nhds h1, ev_lt (contAt_normAddRe z) hψ,
    ev_lt (σ.contAt_reBridgeOne h1) b1] with u c1 c2 c3 c4 c5 c6 c7 c8
  exact ⟨⟨c1, c2, c3, c4, c5⟩, c6, c7, c8⟩

theorem isOpen_pieceJunctionTwo : IsOpen σ.pieceJunctionTwo := by
  refine isOpen_iff_mem_nhds.2 fun z hz => ?_
  obtain ⟨⟨a1, a2, a3, a4, a5⟩, h0, b1⟩ := hz
  have hp := σ.params
  have h1 : z ≠ σ.vertexOne := by
    rintro rfl
    rw [sub_self, norm_zero] at a2
    linarith [hp.2.2.2.1, hp.2.2.1, hp.2.1, hp.2.2.2.2.2.2.2.2.2.2.2.2.1]
  have hb := σ.contAt_foldBlend h0.1 h1 (σ.ne_vertexTwo_of_mem_domZero h0)
  filter_upwards [ev_lt (contAt_dist σ.vertexTwo z) a1, ev_lt (contAt_dist σ.vertexOne z) a2,
    ev_lt (σ.contAt_wallSide 2 z) a3, ev_lt (contAt_norm z) a4, ev_gt hb a5,
    σ.isOpen_domZero.mem_nhds h0, ev_gt (σ.contAt_reBridgeZero h0) b1] with
    u c1 c2 c3 c4 c5 c6 c7
  exact ⟨⟨c1, c2, c3, c4, c5⟩, c6, c7⟩


theorem good_apexOne {z : ℂ} (hz : z ≠ σ.vertexOne) :
    ContDiffAt ℝ ∞ σ.apexOne z ∧ 0 < (fderiv ℝ σ.apexOne z).det :=
  ⟨σ.contDiff_apexOne.contDiffAt, σ.det_fderiv_apexOne_pos hz⟩

theorem good_apexTwo {z : ℂ} (hz : z ≠ σ.vertexTwo) :
    ContDiffAt ℝ ∞ σ.apexTwo z ∧ 0 < (fderiv ℝ σ.apexTwo z).det :=
  ⟨σ.contDiff_apexTwo.contDiffAt, σ.det_fderiv_apexTwo_pos hz⟩

theorem good_outer {z : ℂ} (hz : z ∈ σ.pieceOuter) :
    ContDiffAt ℝ ∞ (compactOuterGerm σ.p₃) z ∧
      0 < (fderiv ℝ (compactOuterGerm σ.p₃) z).det := by
  have hp := σ.params
  have hz0 : z ≠ 0 := norm_pos_iff.1 hz.1
  have h1 : ‖z‖ ≤ 1 := by linarith [hz.2, hp.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.1,
    hp.2.2.2.2.2.2.2.2.2.1, hp.2.2.2.2.2.2.2.2.2.2.1]
  refine ⟨contDiffAt_compactOuterGerm _ hz0, det_fderiv_compactOuterGerm_pos σ.one_le_p₃ hz0 ?_⟩
  have := pow_le_one₀ (norm_nonneg z) h1 (n := σ.p₃)
  linarith

theorem good_lens {z : ℂ} (hz : z ∈ σ.pieceLens) :
    ContDiffAt ℝ ∞ σ.bridgeTwo z ∧ 0 < (fderiv ℝ σ.bridgeTwo z).det := by
  obtain ⟨-, h2, -, hb⟩ := hz
  exact ⟨σ.contDiffAt_bridgeTwo h2,
    σ.det_fderiv_bridgeTwo_pos h2 (by linarith [σ.modOne_pos z])⟩

theorem good_junctionOne {z : ℂ} (hz : z ∈ σ.pieceJunctionOne) :
    ContDiffAt ℝ ∞ σ.bridgeOne z ∧ 0 < (fderiv ℝ σ.bridgeOne z).det := by
  obtain ⟨-, h1, -, hb⟩ := hz
  exact ⟨σ.contDiffAt_bridgeOne h1,
    σ.det_fderiv_bridgeOne_pos h1 (by linarith [σ.modOne_pos z])⟩

theorem good_junctionTwo {z : ℂ} (hz : z ∈ σ.pieceJunctionTwo) :
    ContDiffAt ℝ ∞ σ.bridgeZero z ∧ 0 < (fderiv ℝ σ.bridgeZero z).det := by
  obtain ⟨-, h0, hb⟩ := hz
  exact ⟨σ.contDiffAt_bridgeZero h0,
    σ.det_fderiv_bridgeZero_pos h0 (by linarith [σ.modTwo_pos z])⟩

theorem good_of_piece {s : Set ℂ} (hs : IsOpen s) {g : ℂ → ℂ}
    (heq : ∀ u ∈ s, σ.preFold u = g u) {z : ℂ} (hz : z ∈ s)
    (hg : ContDiffAt ℝ ∞ g z ∧ 0 < (fderiv ℝ g z).det) :
    ContDiffAt ℝ ∞ σ.preFold z ∧ 0 < (fderiv ℝ σ.preFold z).det := by
  have hev : σ.preFold =ᶠ[𝓝 z] g := Filter.eventually_of_mem (hs.mem_nhds hz) heq
  exact ⟨hg.1.congr_of_eventuallyEq hev, by rw [hev.fderiv_eq]; exact hg.2⟩

def goodSet : Set ℂ :=
  σ.pieceApexOne ∪ σ.pieceApexTwo ∪ σ.pieceOuter ∪ σ.pieceCornerOne ∪ σ.pieceCornerTwo ∪
    σ.pieceLens ∪ σ.pieceCornerThree ∪ σ.pieceJunctionOne ∪ σ.pieceJunctionTwo

theorem isOpen_goodSet : IsOpen σ.goodSet :=
  (((((((σ.isOpen_pieceApexOne.union σ.isOpen_pieceApexTwo).union σ.isOpen_pieceOuter).union
    σ.isOpen_pieceCornerOne).union σ.isOpen_pieceCornerTwo).union σ.isOpen_pieceLens).union
      σ.isOpen_pieceCornerThree).union σ.isOpen_pieceJunctionOne).union
        σ.isOpen_pieceJunctionTwo

theorem good_preFold {z : ℂ} (hz : z ∈ σ.goodSet) (h1 : z ≠ σ.vertexOne)
    (h2 : z ≠ σ.vertexTwo) :
    ContDiffAt ℝ ∞ σ.preFold z ∧ 0 < (fderiv ℝ σ.preFold z).det := by
  rcases hz with (((((((hz | hz) | hz) | hz) | hz) | hz) | hz) | hz) | hz
  · exact σ.good_of_piece σ.isOpen_pieceApexOne (fun _ hu => σ.preFold_eq_apexOne hu) hz
      (σ.good_apexOne h1)
  · exact σ.good_of_piece σ.isOpen_pieceApexTwo (fun _ hu => σ.preFold_eq_apexTwo hu) hz
      (σ.good_apexTwo h2)
  · exact σ.good_of_piece σ.isOpen_pieceOuter (fun _ hu => σ.preFold_eq_outer hu) hz
      (σ.good_outer hz)
  · exact σ.good_of_piece σ.isOpen_pieceCornerOne (fun _ hu => σ.preFold_eq_cornerOne hu) hz
      (σ.good_cornerOne hz)
  · exact σ.good_of_piece σ.isOpen_pieceCornerTwo (fun _ hu => σ.preFold_eq_cornerTwo hu) hz
      (σ.good_cornerTwo hz)
  · exact σ.good_of_piece σ.isOpen_pieceLens (fun _ hu => σ.preFold_eq_lens hu) hz
      (σ.good_lens hz)
  · exact σ.good_of_piece σ.isOpen_pieceCornerThree (fun _ hu => σ.preFold_eq_cornerThree hu)
      hz (σ.good_cornerThree hz)
  · exact σ.good_of_piece σ.isOpen_pieceJunctionOne (fun _ hu => σ.preFold_eq_junctionOne hu)
      hz (σ.good_junctionOne hz)
  · exact σ.good_of_piece σ.isOpen_pieceJunctionTwo (fun _ hu => σ.preFold_eq_junctionTwo hu)
      hz (σ.good_junctionTwo hz)

theorem contDiffAt_preFold_of_vertexOne {z : ℂ} (hz : z ∈ σ.pieceApexOne) :
    ContDiffAt ℝ ∞ σ.preFold z :=
  σ.contDiff_apexOne.contDiffAt.congr_of_eventuallyEq
    (Filter.eventually_of_mem (σ.isOpen_pieceApexOne.mem_nhds hz)
      fun _ hu => σ.preFold_eq_apexOne hu)

theorem contDiffAt_preFold_of_vertexTwo {z : ℂ} (hz : z ∈ σ.pieceApexTwo) :
    ContDiffAt ℝ ∞ σ.preFold z :=
  σ.contDiff_apexTwo.contDiffAt.congr_of_eventuallyEq
    (Filter.eventually_of_mem (σ.isOpen_pieceApexTwo.mem_nhds hz)
      fun _ hu => σ.preFold_eq_apexTwo hu)

theorem contDiffAt_preFold {z : ℂ} (hz : z ∈ σ.goodSet) : ContDiffAt ℝ ∞ σ.preFold z := by
  by_cases h1 : z = σ.vertexOne
  · subst h1
    exact σ.contDiffAt_preFold_of_vertexOne (by
      change ‖_ - _‖ < _
      rw [sub_self, norm_zero]
      exact σ.params.2.2.2.2.2.2.2.2.2.2.2.2.1)
  by_cases h2 : z = σ.vertexTwo
  · subst h2
    exact σ.contDiffAt_preFold_of_vertexTwo (by
      change ‖_ - _‖ < _
      rw [sub_self, norm_zero]
      exact σ.params.2.2.2.2.2.2.2.2.2.2.2.2.1)
  exact (σ.good_preFold hz h1 h2).1

end EuclidShape

end GC.Seifert
