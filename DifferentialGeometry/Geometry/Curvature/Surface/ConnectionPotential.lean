import DifferentialGeometry.Geometry.Curvature.Coordinates.MetricJet.CoefficientSectional
import DifferentialGeometry.Analysis.FiniteDimensional.Coercivity
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# Connection-form potentials of a surface coefficient field

For a coefficient field `b : E → E →L[ℝ] E →L[ℝ] ℝ` and a pair of directions `(v₁, v₂)` write
`E = b y v₁ v₁`, `F = b y v₁ v₂`, `G = b y v₂ v₂`, `D = EG − F²`, and let a subscript `k` denote the
derivative along `v_k`. This file defines, as explicit functions,

* `surfaceGramDet b v₁ v₂ = EG − F²`,
* `surfaceConnectionP b v₁ v₂ = (2 E F₁ − E E₂ − F E₁) / (2 E √D)`,
* `surfaceConnectionQ b v₁ v₂ = (E G₁ − F E₂) / (2 E √D)`,

the components of the connection form of the Gram–Schmidt coframe
`θ¹ = √E dx + F/√E dy`, `θ² = √(D/E) dy`. The divergence identity
`K √D = ∂₂ P − ∂₁ Q` is proved in `DivergenceForm.lean`. Here: positivity of `E` and `D`,
invariance under periods of `b`, and `C¹` regularity for a `C²` field.
-/

set_option autoImplicit false

noncomputable section

open scoped ContDiff

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The Gram determinant `EG − F²` of the pair `(v₁, v₂)` for the coefficient field `b`. -/
def surfaceGramDet (b : E → E →L[ℝ] E →L[ℝ] ℝ) (v₁ v₂ : E) (y : E) : ℝ :=
  b y v₁ v₁ * b y v₂ v₂ - (b y v₁ v₂) ^ 2

/-- The first connection-form potential `P = (2 E F₁ − E E₂ − F E₁) / (2 E √D)`. -/
def surfaceConnectionP (b : E → E →L[ℝ] E →L[ℝ] ℝ) (v₁ v₂ : E) (y : E) : ℝ :=
  (2 * b y v₁ v₁ * fderiv ℝ (fun z => b z v₁ v₂) y v₁ -
      b y v₁ v₁ * fderiv ℝ (fun z => b z v₁ v₁) y v₂ -
      b y v₁ v₂ * fderiv ℝ (fun z => b z v₁ v₁) y v₁) /
    (2 * b y v₁ v₁ * Real.sqrt (surfaceGramDet b v₁ v₂ y))

/-- The second connection-form potential `Q = (E G₁ − F E₂) / (2 E √D)`. -/
def surfaceConnectionQ (b : E → E →L[ℝ] E →L[ℝ] ℝ) (v₁ v₂ : E) (y : E) : ℝ :=
  (b y v₁ v₁ * fderiv ℝ (fun z => b z v₂ v₂) y v₁ -
      b y v₁ v₂ * fderiv ℝ (fun z => b z v₁ v₁) y v₂) /
    (2 * b y v₁ v₁ * Real.sqrt (surfaceGramDet b v₁ v₂ y))

theorem surfaceGramDet_def (b : E → E →L[ℝ] E →L[ℝ] ℝ) (v₁ v₂ y : E) :
    surfaceGramDet b v₁ v₂ y = b y v₁ v₁ * b y v₂ v₂ - (b y v₁ v₂) ^ 2 :=
  rfl

theorem surfaceConnectionP_def (b : E → E →L[ℝ] E →L[ℝ] ℝ) (v₁ v₂ y : E) :
    surfaceConnectionP b v₁ v₂ y =
      (2 * b y v₁ v₁ * fderiv ℝ (fun z => b z v₁ v₂) y v₁ -
          b y v₁ v₁ * fderiv ℝ (fun z => b z v₁ v₁) y v₂ -
          b y v₁ v₂ * fderiv ℝ (fun z => b z v₁ v₁) y v₁) /
        (2 * b y v₁ v₁ * Real.sqrt (surfaceGramDet b v₁ v₂ y)) :=
  rfl

theorem surfaceConnectionQ_def (b : E → E →L[ℝ] E →L[ℝ] ℝ) (v₁ v₂ y : E) :
    surfaceConnectionQ b v₁ v₂ y =
      (b y v₁ v₁ * fderiv ℝ (fun z => b z v₂ v₂) y v₁ -
          b y v₁ v₂ * fderiv ℝ (fun z => b z v₁ v₁) y v₂) /
        (2 * b y v₁ v₁ * Real.sqrt (surfaceGramDet b v₁ v₂ y)) :=
  rfl

/-- `E = b y v₁ v₁` is positive for a positive field and a nonzero first direction. -/
theorem surfaceE_pos {b : E → E →L[ℝ] E →L[ℝ] ℝ} (hpos : ∀ y v, v ≠ 0 → 0 < b y v v)
    {v₁ v₂ : E} (hli : LinearIndependent ℝ ![v₁, v₂]) (y : E) : 0 < b y v₁ v₁ :=
  hpos y v₁ (by simpa using hli.ne_zero 0)

/-- The Gram determinant of a linearly independent pair is positive. -/
theorem surfaceGramDet_pos [FiniteDimensional ℝ E] {b : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hsymm : ∀ y u v, b y u v = b y v u) (hpos : ∀ y v, v ≠ 0 → 0 < b y v v)
    {v₁ v₂ : E} (hli : LinearIndependent ℝ ![v₁, v₂]) (y : E) :
    0 < surfaceGramDet b v₁ v₂ y :=
  bilin_gram_pos_of_linearIndependent (hsymm y)
    ((b y).isCoercive_of_posDef (hpos y)) hli

private theorem fderiv_comp_add_period (f : E → ℝ) {w : E} (hf : ∀ y, f (y + w) = f y)
    (y : E) : fderiv ℝ f (y + w) = fderiv ℝ f y := by
  have h : (fun z => f (z + w)) = f := funext hf
  rw [← fderiv_comp_add_right, h]

private theorem apply_add_period {b : E → E →L[ℝ] E →L[ℝ] ℝ} {w : E}
    (hper : ∀ y, b (y + w) = b y) (u v : E) :
    ∀ y, (fun z => b z u v) (y + w) = (fun z => b z u v) y :=
  fun y => by simp only [hper y]

theorem surfaceGramDet_add_period {b : E → E →L[ℝ] E →L[ℝ] ℝ} {w : E}
    (hper : ∀ y, b (y + w) = b y) (v₁ v₂ y : E) :
    surfaceGramDet b v₁ v₂ (y + w) = surfaceGramDet b v₁ v₂ y := by
  simp only [surfaceGramDet, hper y]

/-- `P` inherits every period of `b`. -/
theorem surfaceConnectionP_add_period {b : E → E →L[ℝ] E →L[ℝ] ℝ} {w : E}
    (hper : ∀ y, b (y + w) = b y) (v₁ v₂ y : E) :
    surfaceConnectionP b v₁ v₂ (y + w) = surfaceConnectionP b v₁ v₂ y := by
  simp only [surfaceConnectionP, surfaceGramDet_add_period hper,
    fderiv_comp_add_period (fun z => b z v₁ v₂) (apply_add_period hper v₁ v₂),
    fderiv_comp_add_period (fun z => b z v₁ v₁) (apply_add_period hper v₁ v₁), hper y]

/-- `Q` inherits every period of `b`. -/
theorem surfaceConnectionQ_add_period {b : E → E →L[ℝ] E →L[ℝ] ℝ} {w : E}
    (hper : ∀ y, b (y + w) = b y) (v₁ v₂ y : E) :
    surfaceConnectionQ b v₁ v₂ (y + w) = surfaceConnectionQ b v₁ v₂ y := by
  simp only [surfaceConnectionQ, surfaceGramDet_add_period hper,
    fderiv_comp_add_period (fun z => b z v₂ v₂) (apply_add_period hper v₂ v₂),
    fderiv_comp_add_period (fun z => b z v₁ v₁) (apply_add_period hper v₁ v₁), hper y]

private theorem contDiff_apply_apply {n : ℕ∞ω} {b : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hb : ContDiff ℝ n b) (u v : E) : ContDiff ℝ n (fun z => b z u v) :=
  (hb.clm_apply contDiff_const).clm_apply contDiff_const

private theorem contDiff_fderiv_apply_apply {b : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hb : ContDiff ℝ 2 b) (u v w : E) :
    ContDiff ℝ 1 (fun y => fderiv ℝ (fun z => b z u v) y w) :=
  ((contDiff_apply_apply hb u v).fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const

private theorem contDiff_surface_denominator [FiniteDimensional ℝ E]
    {b : E → E →L[ℝ] E →L[ℝ] ℝ} (hb : ContDiff ℝ 2 b) (hsymm : ∀ y u v, b y u v = b y v u)
    (hpos : ∀ y v, v ≠ 0 → 0 < b y v v) {v₁ v₂ : E} (hli : LinearIndependent ℝ ![v₁, v₂]) :
    ContDiff ℝ 1 (fun y => 2 * b y v₁ v₁ * Real.sqrt (surfaceGramDet b v₁ v₂ y)) ∧
      ∀ y, 2 * b y v₁ v₁ * Real.sqrt (surfaceGramDet b v₁ v₂ y) ≠ 0 := by
  have hb1 : ContDiff ℝ 1 b := hb.of_le (by norm_num)
  have hD : ContDiff ℝ 1 (surfaceGramDet b v₁ v₂) :=
    ((contDiff_apply_apply hb1 v₁ v₁).mul (contDiff_apply_apply hb1 v₂ v₂)).sub
      ((contDiff_apply_apply hb1 v₁ v₂).pow 2)
  refine ⟨(contDiff_const.mul (contDiff_apply_apply hb1 v₁ v₁)).mul
    (hD.sqrt fun y => (surfaceGramDet_pos hsymm hpos hli y).ne'), fun y => ?_⟩
  have h1 := surfaceE_pos hpos hli y
  have h2 := Real.sqrt_pos.mpr (surfaceGramDet_pos hsymm hpos hli y)
  positivity

/-- `P` is `C¹` for a `C²` positive symmetric field and a linearly independent pair. -/
theorem contDiff_surfaceConnectionP [FiniteDimensional ℝ E] {b : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hb : ContDiff ℝ 2 b) (hsymm : ∀ y u v, b y u v = b y v u)
    (hpos : ∀ y v, v ≠ 0 → 0 < b y v v) {v₁ v₂ : E} (hli : LinearIndependent ℝ ![v₁, v₂]) :
    ContDiff ℝ 1 (surfaceConnectionP b v₁ v₂) := by
  have hb1 : ContDiff ℝ 1 b := hb.of_le (by norm_num)
  obtain ⟨hden, hden0⟩ := contDiff_surface_denominator hb hsymm hpos hli
  refine ContDiff.div ?_ hden hden0
  exact (((contDiff_const.mul (contDiff_apply_apply hb1 v₁ v₁)).mul
    (contDiff_fderiv_apply_apply hb v₁ v₂ v₁)).sub
    ((contDiff_apply_apply hb1 v₁ v₁).mul (contDiff_fderiv_apply_apply hb v₁ v₁ v₂))).sub
    ((contDiff_apply_apply hb1 v₁ v₂).mul (contDiff_fderiv_apply_apply hb v₁ v₁ v₁))

/-- `Q` is `C¹` for a `C²` positive symmetric field and a linearly independent pair. -/
theorem contDiff_surfaceConnectionQ [FiniteDimensional ℝ E] {b : E → E →L[ℝ] E →L[ℝ] ℝ}
    (hb : ContDiff ℝ 2 b) (hsymm : ∀ y u v, b y u v = b y v u)
    (hpos : ∀ y v, v ≠ 0 → 0 < b y v v) {v₁ v₂ : E} (hli : LinearIndependent ℝ ![v₁, v₂]) :
    ContDiff ℝ 1 (surfaceConnectionQ b v₁ v₂) := by
  have hb1 : ContDiff ℝ 1 b := hb.of_le (by norm_num)
  obtain ⟨hden, hden0⟩ := contDiff_surface_denominator hb hsymm hpos hli
  refine ContDiff.div ?_ hden hden0
  exact ((contDiff_apply_apply hb1 v₁ v₁).mul (contDiff_fderiv_apply_apply hb v₂ v₂ v₁)).sub
    ((contDiff_apply_apply hb1 v₁ v₂).mul (contDiff_fderiv_apply_apply hb v₁ v₁ v₂))

end DifferentialGeometry.Analysis
