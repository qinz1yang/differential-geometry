import DifferentialGeometry.Geometry.Curvature.Surface.ConnectionPotential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The Gram–Schmidt coframe of a surface coefficient field and its structure equations

For a coefficient field `b : E → E →L[ℝ] E →L[ℝ] ℝ` and a pair `(v₁, v₂)` write
`E = b y v₁ v₁`, `F = b y v₁ v₂`, `G = b y v₂ v₂`, `D = EG − F²`. The Gram–Schmidt coframe is

* `θ¹ = (√E)⁻¹ · b(v₁, ·)` (so `θ¹ v₁ = √E`, `θ¹ v₂ = F/√E`),
* `θ² = (√D √E)⁻¹ · (E b(v₂, ·) − F b(v₁, ·))` (so `θ² v₁ = 0`, `θ² v₂ = √D/√E`),

with `θ¹ ⊗ θ¹ + θ² ⊗ θ² = b`. With the connection-form potentials `P, Q` of
`ConnectionPotential.lean` the structure equations `dθ¹ = ω ∧ θ²`, `dθ² = −ω ∧ θ¹`
(`ω = P dx + Q dy`) read, along the directions `v₁, v₂`,

* `∂₁(F/√E) − ∂₂ √E = P · √D/√E`,
* `∂₁(√D/√E) = Q · √E − P · F/√E`.

These are the input of the developing map of a flat field (`DevelopingMap.lean`).
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

section Coframe

/-- The coframe coefficient `√E`. -/
def surfaceCoframeA (b : E → E →L[ℝ] E →L[ℝ] ℝ) (v₁ : E) (y : E) : ℝ :=
  √(b y v₁ v₁)

/-- The coframe coefficient `F / √E`. -/
def surfaceCoframeC (b : E → E →L[ℝ] E →L[ℝ] ℝ) (v₁ v₂ : E) (y : E) : ℝ :=
  b y v₁ v₂ / √(b y v₁ v₁)

/-- The coframe coefficient `√D / √E`. -/
def surfaceCoframeW (b : E → E →L[ℝ] E →L[ℝ] ℝ) (v₁ v₂ : E) (y : E) : ℝ :=
  √(surfaceGramDet b v₁ v₂ y) / √(b y v₁ v₁)

/-- The first coframe form `θ¹ = (√E)⁻¹ b(v₁, ·)`. -/
def surfaceCoframe₁ (b : E → E →L[ℝ] E →L[ℝ] ℝ) (v₁ : E) (y : E) : E →L[ℝ] ℝ :=
  (√(b y v₁ v₁))⁻¹ • b y v₁

/-- The second coframe form `θ² = (√D √E)⁻¹ (E b(v₂, ·) − F b(v₁, ·))`. -/
def surfaceCoframe₂ (b : E → E →L[ℝ] E →L[ℝ] ℝ) (v₁ v₂ : E) (y : E) : E →L[ℝ] ℝ :=
  (√(surfaceGramDet b v₁ v₂ y) * √(b y v₁ v₁))⁻¹ •
    (b y v₁ v₁ • b y v₂ - b y v₁ v₂ • b y v₁)

variable {b : E → E →L[ℝ] E →L[ℝ] ℝ} {v₁ v₂ : E}

theorem surfaceCoframe₁_apply_left (hpos : ∀ y v, v ≠ 0 → 0 < b y v v)
    (hli : LinearIndependent ℝ ![v₁, v₂]) (y : E) :
    surfaceCoframe₁ b v₁ y v₁ = surfaceCoframeA b v₁ y := by
  have hE := surfaceE_pos hpos hli y
  have hs := Real.sqrt_pos.mpr hE
  simp only [surfaceCoframe₁, surfaceCoframeA, smul_apply, smul_eq_mul]
  field_simp
  rw [Real.sq_sqrt hE.le]

theorem surfaceCoframe₁_apply_right (y : E) :
    surfaceCoframe₁ b v₁ y v₂ = surfaceCoframeC b v₁ v₂ y := by
  simp only [surfaceCoframe₁, surfaceCoframeC, smul_apply, smul_eq_mul]
  ring

theorem surfaceCoframe₂_apply_left (hsymm : ∀ y u v, b y u v = b y v u) (y : E) :
    surfaceCoframe₂ b v₁ v₂ y v₁ = 0 := by
  simp only [surfaceCoframe₂, smul_apply, sub_apply,
    smul_eq_mul, hsymm y v₂ v₁]
  ring

theorem surfaceCoframe₂_apply_right [FiniteDimensional ℝ E]
    (hsymm : ∀ y u v, b y u v = b y v u) (hpos : ∀ y v, v ≠ 0 → 0 < b y v v)
    (hli : LinearIndependent ℝ ![v₁, v₂]) (y : E) :
    surfaceCoframe₂ b v₁ v₂ y v₂ = surfaceCoframeW b v₁ v₂ y := by
  have hE := Real.sqrt_pos.mpr (surfaceE_pos hpos hli y)
  have hDpos := surfaceGramDet_pos hsymm hpos hli y
  have hD := Real.sqrt_pos.mpr hDpos
  have hsq := Real.sq_sqrt hDpos.le
  rw [surfaceGramDet_def] at hsq
  simp only [surfaceCoframe₂, surfaceCoframeW, smul_apply,
    sub_apply, smul_eq_mul]
  field_simp
  rw [surfaceGramDet_def] at hD ⊢
  linear_combination -hsq

/-- Coordinates of the coframe on the basis directions. -/
theorem surfaceCoframe_gram [FiniteDimensional ℝ E]
    (hsymm : ∀ y u v, b y u v = b y v u) (hpos : ∀ y v, v ≠ 0 → 0 < b y v v)
    (hli : LinearIndependent ℝ ![v₁, v₂]) (y : E) {a₁ a₂ c₁ c₂ : ℝ} :
    surfaceCoframe₁ b v₁ y (a₁ • v₁ + a₂ • v₂) * surfaceCoframe₁ b v₁ y (c₁ • v₁ + c₂ • v₂) +
        surfaceCoframe₂ b v₁ v₂ y (a₁ • v₁ + a₂ • v₂) *
          surfaceCoframe₂ b v₁ v₂ y (c₁ • v₁ + c₂ • v₂) =
      b y (a₁ • v₁ + a₂ • v₂) (c₁ • v₁ + c₂ • v₂) := by
  have hEpos := surfaceE_pos hpos hli y
  have hE := Real.sqrt_pos.mpr hEpos
  have hDpos := surfaceGramDet_pos hsymm hpos hli y
  have hsqE := Real.sq_sqrt hEpos.le
  have hsqD := Real.sq_sqrt hDpos.le
  simp only [map_add, map_smul, smul_eq_mul, surfaceCoframe₁_apply_left hpos hli,
    surfaceCoframe₁_apply_right, surfaceCoframe₂_apply_left hsymm,
    surfaceCoframe₂_apply_right hsymm hpos hli, add_apply,
    smul_apply, hsymm y v₂ v₁]
  simp only [surfaceCoframeA, surfaceCoframeC, surfaceCoframeW]
  set sE := √(b y v₁ v₁)
  set sD := √(surfaceGramDet b v₁ v₂ y)
  rw [surfaceGramDet_def] at hsqD
  field_simp
  linear_combination (a₁ * c₁ * sE ^ 2 - a₂ * c₂ * b y v₂ v₂) * hsqE + a₂ * c₂ * hsqD

end Coframe

section Periodic

variable {b : E → E →L[ℝ] E →L[ℝ] ℝ} {w : E}

theorem surfaceCoframe₁_add_period (hper : ∀ y, b (y + w) = b y) (v₁ y : E) :
    surfaceCoframe₁ b v₁ (y + w) = surfaceCoframe₁ b v₁ y := by
  simp only [surfaceCoframe₁, hper y]

theorem surfaceCoframe₂_add_period (hper : ∀ y, b (y + w) = b y) (v₁ v₂ y : E) :
    surfaceCoframe₂ b v₁ v₂ (y + w) = surfaceCoframe₂ b v₁ v₂ y := by
  simp only [surfaceCoframe₂, surfaceGramDet_add_period hper, hper y]

end Periodic

section Structure

variable [FiniteDimensional ℝ E] {b : E → E →L[ℝ] E →L[ℝ] ℝ} {v₁ v₂ : E}

omit [FiniteDimensional ℝ E] in
private theorem hasFDerivAt_apply_apply {y : E} (hb : DifferentiableAt ℝ b y) (u v : E) :
    HasFDerivAt (fun z => b z u v) (fderiv ℝ (fun z => b z u v) y) y :=
  ((hb.clm_apply (differentiableAt_const u)).clm_apply (differentiableAt_const v)).hasFDerivAt

/-- **Structure equations** of the Gram–Schmidt coframe along `(v₁, v₂)`:
`∂₁(F/√E) − ∂₂ √E = P √D/√E` and `∂₁(√D/√E) = Q √E − P F/√E`. -/
theorem surfaceCoframe_structure (hb : Differentiable ℝ b)
    (hsymm : ∀ y u v, b y u v = b y v u) (hpos : ∀ y v, v ≠ 0 → 0 < b y v v)
    (hli : LinearIndependent ℝ ![v₁, v₂]) (y : E) :
    fderiv ℝ (surfaceCoframeC b v₁ v₂) y v₁ - fderiv ℝ (surfaceCoframeA b v₁) y v₂ =
        surfaceConnectionP b v₁ v₂ y * surfaceCoframeW b v₁ v₂ y ∧
      fderiv ℝ (surfaceCoframeW b v₁ v₂) y v₁ =
        surfaceConnectionQ b v₁ v₂ y * surfaceCoframeA b v₁ y -
          surfaceConnectionP b v₁ v₂ y * surfaceCoframeC b v₁ v₂ y := by
  have hEpos := surfaceE_pos hpos hli y
  have hDpos := surfaceGramDet_pos hsymm hpos hli y
  have hs := Real.sqrt_pos.mpr hEpos
  have hW := Real.sqrt_pos.mpr hDpos
  have he := hasFDerivAt_apply_apply (hb y) v₁ v₁
  have hf := hasFDerivAt_apply_apply (hb y) v₁ v₂
  have hg := hasFDerivAt_apply_apply (hb y) v₂ v₂
  have hA : HasFDerivAt (fun z => √(b z v₁ v₁)) _ y := he.sqrt hEpos.ne'
  have hAinv := (hasDerivAt_inv hs.ne').comp_hasFDerivAt y hA
  have hD0 := (he.mul hg).sub (hf.pow 2)
  have hD : HasFDerivAt (surfaceGramDet b v₁ v₂) _ y := hD0
  have hWD : HasFDerivAt (fun z => √(surfaceGramDet b v₁ v₂ z)) _ y := hD.sqrt hDpos.ne'
  have hC := (hf.mul hAinv).congr_of_eventuallyEq (f₁ := surfaceCoframeC b v₁ v₂)
    (Filter.Eventually.of_forall fun z => by
      simp only [surfaceCoframeC, div_eq_mul_inv, Function.comp_apply, Pi.mul_apply])
  have hWW := (hWD.mul hAinv).congr_of_eventuallyEq (f₁ := surfaceCoframeW b v₁ v₂)
    (Filter.Eventually.of_forall fun z => by
      simp only [surfaceCoframeW, div_eq_mul_inv, Function.comp_apply, Pi.mul_apply])
  have hA' := hA.congr_of_eventuallyEq (f₁ := surfaceCoframeA b v₁)
    (Filter.Eventually.of_forall fun z => rfl)
  rw [hC.fderiv, hA'.fderiv, hWW.fderiv]
  have hsqE := Real.sq_sqrt hEpos.le
  have hsqD := Real.sq_sqrt hDpos.le
  simp only [add_apply, sub_apply,
    smul_apply, smul_eq_mul, surfaceConnectionP_def, surfaceConnectionQ_def,
    surfaceCoframeA, surfaceCoframeC, surfaceCoframeW, nsmul_eq_mul, Nat.cast_ofNat,
    Function.comp_apply, Nat.add_one_sub_one, pow_one]
  set s := √(b y v₁ v₁) with hs_def
  set W := √(surfaceGramDet b v₁ v₂ y) with hW_def
  have hWsq : W ^ 2 = s ^ 2 * b y v₂ v₂ - b y v₁ v₂ ^ 2 := by
    rw [hsqD, hsqE, surfaceGramDet_def]
  rw [← hsqE]
  constructor
  · field_simp
    ring
  · field_simp
    linear_combination (-(fderiv ℝ (fun z => b z v₁ v₁) y v₁)) * hWsq

end Structure

end DifferentialGeometry.Analysis
