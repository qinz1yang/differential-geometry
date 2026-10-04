import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.CompactFoldSphGerms

/-!
# The piecewise spherical fold before the core replacement

Lane CF-S, tier 3, curvature `+4` (design `docs/geometrization/handoffs/
20261004-design-cf-compact-triangle-fold.md`, §5). All layout parameters are multiples of the scale
`sphScale = τ₁ τ₂ τ₃ sin θ₁ sin θ₂ sin θ₃ / 16` (the `τⱼ = sphTau` are the half-tangents of the
canonical radii) or of the canonical half-tangents themselves:
* lens half-width `sphLensWidth = s/16` and switch top `sphSwitchTop = s/8` in the side coordinate
  `Im rotTwo` of wall 2;
* corner shrink `sphCornerShrink = s/256` in tangent units, so that the corner discs are
  `‖rotⱼ‖ < sphCornerRad j = τⱼ ⊖ shrink` (inside the canonical discs);
* inner apex germ radius `m/8`, radial bend `[3m/8, m/2]`, `m = min τ₁ τ₂` (in `‖rotⱼ‖`);
* outer germ radius `τ₃/20`, outer bend `[τ₃/10, τ₃/5]` (in `‖z‖`), outer weight `ν` with
  `w = 1`, `δ = sphCornerShrink`;
* the core disc, in the coordinate `ζ = rotTwo z`, has centre `τ₂ + i s/2` and radius
  `s/2 - sphLensWidth/2`, with margin `sphLensWidth/8`.

The map `sphPreFold` takes, in this order, the apex model at `v₁`, at `v₂`, the outer germ at
`v₃ = 0`, the corner at `v₁` on its corner disc, the corner at `v₂` on its corner disc, the bridge
of wall 2 on the lens `|Im rotTwo| < sphLensWidth`, and the outer corner elsewhere. The parameter
inequalities are collected in `sphParams`.
-/

set_option autoImplicit false

noncomputable section

open Complex Set Filter
open scoped ComplexConjugate ContDiff Topology

namespace GC.Seifert

namespace CompactShape

variable {σ : CompactShape}

def sphScale (σ : CompactShape) : ℝ :=
  σ.sphTau 0 * σ.sphTau 1 * σ.sphTau 2 *
    (Real.sin σ.θ₁ * Real.sin σ.θ₂ * Real.sin σ.θ₃) / 16

def sphLensWidth (σ : CompactShape) : ℝ := σ.sphScale / 16

def sphSwitchTop (σ : CompactShape) : ℝ := σ.sphScale / 8

def sphCornerShrink (σ : CompactShape) : ℝ := σ.sphScale / 256

def sphCornerRad (σ : CompactShape) (j : Fin 3) : ℝ :=
  (σ.sphTau j - σ.sphCornerShrink) / (1 + σ.sphTau j * σ.sphCornerShrink)

def sphInnerScale (σ : CompactShape) : ℝ := min (σ.sphTau 0) (σ.sphTau 1)

def sphGermRadius (σ : CompactShape) : ℝ := σ.sphInnerScale / 8

def sphBlendStart (σ : CompactShape) : ℝ := 3 * σ.sphInnerScale / 8

def sphBlendEnd (σ : CompactShape) : ℝ := σ.sphInnerScale / 2

def sphOuterGermRadius (σ : CompactShape) : ℝ := σ.sphTau 2 / 20

def sphOuterBlendStart (σ : CompactShape) : ℝ := σ.sphTau 2 / 10

def sphOuterBlendEnd (σ : CompactShape) : ℝ := σ.sphTau 2 / 5

def sphCoreCenter (σ : CompactShape) : ℂ := (σ.sphTau 1 : ℂ) + ((σ.sphScale / 2 : ℝ) : ℂ) * I

def sphCoreRadius (σ : CompactShape) : ℝ := σ.sphScale / 2 - σ.sphLensWidth / 2

def sphCoreMargin (σ : CompactShape) : ℝ := σ.sphLensWidth / 8

def sphFoldCornerOne (σ : CompactShape) : ℂ → ℂ :=
  σ.sphCornerOne σ.sphBlendStart σ.sphBlendEnd σ.sphLensWidth σ.sphSwitchTop

def sphFoldCornerTwo (σ : CompactShape) : ℂ → ℂ :=
  σ.sphCornerTwo σ.sphBlendStart σ.sphBlendEnd σ.sphLensWidth σ.sphSwitchTop

def sphFoldCornerThree (σ : CompactShape) : ℂ → ℂ :=
  σ.sphCornerThree σ.sphOuterBlendStart σ.sphOuterBlendEnd 1 σ.sphCornerShrink

def sphFoldBlend (σ : CompactShape) : ℂ → ℝ := σ.sphBlendThree 1 σ.sphCornerShrink

def sphPreFold (σ : CompactShape) (z : ℂ) : ℂ :=
  if ‖σ.rotOne z‖ < σ.sphGermRadius then σ.sphApexOne z
  else if ‖σ.rotTwo z‖ < σ.sphGermRadius then σ.sphApexTwo z
  else if ‖z‖ < σ.sphOuterGermRadius then compactOuterGerm σ.p₃ z
  else if ‖σ.rotOne z‖ < σ.sphCornerRad 0 then σ.sphFoldCornerOne z
  else if ‖σ.rotTwo z‖ < σ.sphCornerRad 1 then σ.sphFoldCornerTwo z
  else if |σ.sphSideTwo z| < σ.sphLensWidth then σ.sphBridgeTwo z
  else σ.sphFoldCornerThree z

def sphInCore (σ : CompactShape) (z : ℂ) : Prop :=
  ‖σ.rotTwo z - σ.sphCoreCenter‖ < σ.sphCoreRadius - σ.sphCoreMargin

section Spherical

variable (hs : σ.curv = .spherical)
include hs

theorem sphScale_pos : 0 < σ.sphScale := by
  have := sphTau_pos hs 0
  have := sphTau_pos hs 1
  have := sphTau_pos hs 2
  have := σ.sin_θ₁_pos_sph
  have := σ.sin_θ₂_pos_sph
  have := σ.sin_θ₃_pos_sph
  unfold sphScale
  positivity

theorem sphScale_le_tau (j : Fin 3) : σ.sphScale ≤ σ.sphTau j / 16 := by
  have t0 := sphTau_pos hs 0
  have t1 := sphTau_pos hs 1
  have t2 := sphTau_pos hs 2
  have u0 := sphTau_lt_one hs 0
  have u1 := sphTau_lt_one hs 1
  have u2 := sphTau_lt_one hs 2
  have s1 := σ.sin_θ₁_pos_sph
  have s2 := σ.sin_θ₂_pos_sph
  have s3 := σ.sin_θ₃_pos_sph
  have hk : Real.sin σ.θ₁ * Real.sin σ.θ₂ * Real.sin σ.θ₃ ≤ 1 := by
    have := Real.sin_le_one σ.θ₁
    have := Real.sin_le_one σ.θ₂
    have := Real.sin_le_one σ.θ₃
    have h12 : Real.sin σ.θ₁ * Real.sin σ.θ₂ ≤ 1 := by nlinarith
    nlinarith
  have hk0 : 0 ≤ Real.sin σ.θ₁ * Real.sin σ.θ₂ * Real.sin σ.θ₃ := by positivity
  unfold sphScale
  fin_cases j
  · have : σ.sphTau 0 * σ.sphTau 1 * σ.sphTau 2 ≤ σ.sphTau 0 := by
      have : σ.sphTau 1 * σ.sphTau 2 ≤ 1 := by nlinarith
      nlinarith
    simp only [Fin.zero_eta, Fin.isValue]
    nlinarith
  · have : σ.sphTau 0 * σ.sphTau 1 * σ.sphTau 2 ≤ σ.sphTau 1 := by
      have : σ.sphTau 0 * σ.sphTau 2 ≤ 1 := by nlinarith
      nlinarith
    simp only [Fin.mk_one, Fin.isValue]
    nlinarith
  · have : σ.sphTau 0 * σ.sphTau 1 * σ.sphTau 2 ≤ σ.sphTau 2 := by
      have : σ.sphTau 0 * σ.sphTau 1 ≤ 1 := by nlinarith
      nlinarith
    simp only [Fin.reduceFinMk, Fin.isValue]
    nlinarith

theorem sphParams :
    0 < σ.sphCornerShrink ∧ 0 < σ.sphLensWidth ∧ σ.sphLensWidth < σ.sphSwitchTop ∧
      0 < σ.sphGermRadius ∧ σ.sphGermRadius < σ.sphBlendStart ∧
      σ.sphBlendStart < σ.sphBlendEnd ∧ σ.sphBlendEnd ≤ 1 ∧
      0 < σ.sphOuterGermRadius ∧ σ.sphOuterGermRadius < σ.sphOuterBlendStart ∧
      σ.sphOuterBlendStart < σ.sphOuterBlendEnd ∧ σ.sphOuterBlendEnd ≤ 1 / 5 := by
  have hs0 := sphScale_pos hs
  have t0 := sphTau_pos hs 0
  have t1 := sphTau_pos hs 1
  have t2 := sphTau_pos hs 2
  have u0 := sphTau_lt_one hs 0
  have u1 := sphTau_lt_one hs 1
  have u2 := sphTau_lt_one hs 2
  have hm : 0 < σ.sphInnerScale := lt_min t0 t1
  have hm1 : σ.sphInnerScale ≤ 1 := (min_le_left _ _).trans u0.le
  unfold sphCornerShrink sphLensWidth sphSwitchTop sphGermRadius sphBlendStart sphBlendEnd
    sphOuterGermRadius sphOuterBlendStart sphOuterBlendEnd
  refine ⟨by positivity, by positivity, by linarith, by positivity, by linarith, by linarith,
    by linarith, by positivity, by linarith, by linarith, by linarith⟩


theorem sphCornerRad_bounds (j : Fin 3) :
    σ.sphTau j / 2 < σ.sphCornerRad j ∧ σ.sphCornerRad j < σ.sphTau j := by
  have hs0 := sphScale_pos hs
  have hle := sphScale_le_tau hs j
  have t0 := sphTau_pos hs j
  have u0 := sphTau_lt_one hs j
  have hd : 0 < σ.sphCornerShrink := by unfold sphCornerShrink; positivity
  have hd' : σ.sphCornerShrink ≤ σ.sphTau j / 4096 := by unfold sphCornerShrink; linarith
  have hden : 0 < 1 + σ.sphTau j * σ.sphCornerShrink := by positivity
  have h1 : σ.sphTau j * σ.sphCornerShrink ≤ σ.sphCornerShrink := by nlinarith
  have h2 : σ.sphTau j / 2 * (σ.sphTau j * σ.sphCornerShrink) ≤ σ.sphCornerShrink / 2 := by
    nlinarith
  have h3 := mul_pos (mul_pos t0 t0) hd
  unfold sphCornerRad
  constructor
  · rw [lt_div_iff₀ hden]
    nlinarith
  · rw [div_lt_iff₀ hden]
    nlinarith

theorem sphSwitchTop_lt :
    σ.sphSwitchTop < Real.sin σ.θ₁ / 2 * σ.sphBlendStart ∧
      σ.sphSwitchTop < Real.sin σ.θ₂ * σ.sphBlendStart := by
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
  have hm : σ.sphInnerScale = min (σ.sphTau 0) (σ.sphTau 1) := rfl
  have hprod : σ.sphTau 0 * σ.sphTau 1 * σ.sphTau 2 ≤ min (σ.sphTau 0) (σ.sphTau 1) := by
    rcases le_total (σ.sphTau 0) (σ.sphTau 1) with h | h
    · rw [min_eq_left h]
      have : σ.sphTau 1 * σ.sphTau 2 ≤ 1 := by nlinarith
      nlinarith
    · rw [min_eq_right h]
      have : σ.sphTau 0 * σ.sphTau 2 ≤ 1 := by nlinarith
      nlinarith
  have hmin : 0 < min (σ.sphTau 0) (σ.sphTau 1) := lt_min t0 t1
  have k1 : Real.sin σ.θ₁ * Real.sin σ.θ₂ * Real.sin σ.θ₃ ≤ Real.sin σ.θ₁ := by
    have : Real.sin σ.θ₂ * Real.sin σ.θ₃ ≤ 1 := by nlinarith
    nlinarith
  have k2 : Real.sin σ.θ₁ * Real.sin σ.θ₂ * Real.sin σ.θ₃ ≤ Real.sin σ.θ₂ := by
    have : Real.sin σ.θ₁ * Real.sin σ.θ₃ ≤ 1 := by nlinarith
    nlinarith
  have hk0 : 0 ≤ Real.sin σ.θ₁ * Real.sin σ.θ₂ * Real.sin σ.θ₃ := by positivity
  have hp0 : 0 ≤ σ.sphTau 0 * σ.sphTau 1 * σ.sphTau 2 := by positivity
  unfold sphSwitchTop sphBlendStart sphScale
  rw [hm]
  constructor <;> nlinarith [mul_le_mul hprod k1 hk0 hmin.le, mul_le_mul hprod k2 hk0 hmin.le]

theorem sphLayout_ineqs :
    σ.sphGermRadius ≤ σ.sphCornerRad 0 ∧ σ.sphGermRadius ≤ σ.sphCornerRad 1 ∧
      σ.sphBlendStart ≤ σ.sphCornerRad 0 ∧ σ.sphBlendStart ≤ σ.sphCornerRad 1 ∧
      σ.sphCornerRad 0 < σ.sphTau 0 ∧ σ.sphCornerRad 1 < σ.sphTau 1 ∧
      σ.sphOuterGermRadius < σ.sphTau 2 ∧
      σ.sphSwitchTop < Real.sin σ.θ₂ * σ.sphBlendStart ∧
      σ.sphSwitchTop < Real.sin σ.θ₁ / 2 * σ.sphBlendStart := by
  obtain ⟨c0, c0'⟩ := sphCornerRad_bounds hs 0
  obtain ⟨c1, c1'⟩ := sphCornerRad_bounds hs 1
  obtain ⟨w1, w2⟩ := sphSwitchTop_lt hs
  have t0 := sphTau_pos hs 0
  have t1 := sphTau_pos hs 1
  have t2 := sphTau_pos hs 2
  have m0 : σ.sphInnerScale ≤ σ.sphTau 0 := min_le_left _ _
  have m1 : σ.sphInnerScale ≤ σ.sphTau 1 := min_le_right _ _
  have hm : 0 < σ.sphInnerScale := lt_min t0 t1
  unfold sphGermRadius sphBlendStart sphOuterGermRadius at *
  refine ⟨by linarith, by linarith, by linarith, by linarith, c0', c1', by linarith, w2, w1⟩

end Spherical

end CompactShape

end GC.Seifert
