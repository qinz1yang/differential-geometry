import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ConeFoldDescentMap
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.FilledPantsGeometryIsometries

/-!
# The isometries of the cone-fold descent

All deck isometries of the one-cone descent are composites of the flip `(x, y, s) ↦ (-x, y, -s)`
(`foldFlip 0`, the lift of `σ₀`) and the maps `mobiusLogMap g t` (a Möbius map `g ∈ GL₂⁺(ℝ)` in
the base and a translation by `t` in the fibre). `glOfDet A hA` turns a real matrix of positive
determinant into an element of `GL₂(ℝ)` acting by `(a z + b)/(c z + d)` (`coe_glOfDet_smul`).
The wall lifts are `wallOneLift = T_{2W} ∘ flip` with base map `σ₁` and fibre `s ↦ -s`, and
`wallTwoLift t = M₂ ∘ flip` with `M₂ = [[1/4, 0], [1, 1/4]]`, base map `σ₂` when the second vertex
is the cusp at `0` (centre `1/4`), and fibre `s ↦ t - s`; `fibreShift t` translates the fibre;
`screwLift v β t` is the elliptic Möbius map about `v` with `coneDisc v ∘ R = e^{2iβ} coneDisc v`
(`coneDisc_screwLift`), combined with the fibre translation `t`. Each is an isometry of the
`.hyperbolicProduct` coordinate metric (`pullbackMetric_*`).
-/

set_option autoImplicit false
noncomputable section
open Complex Set
open DifferentialGeometry GC.Geometry
open scoped Manifold ContDiff ComplexConjugate MatrixGroups UpperHalfPlane

namespace GC.Seifert

def glOfDet (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : 0 < A.det) : GL (Fin 2) ℝ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero A hA.ne'

theorem glOfDet_det_pos (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : 0 < A.det) :
    0 < (glOfDet A hA).det.val := by
  simpa [glOfDet] using hA

theorem coe_glOfDet_smul (A : Matrix (Fin 2) (Fin 2) ℝ) (hA : 0 < A.det) (z : ℍ) :
    ((glOfDet A hA • z : ℍ) : ℂ) = (A 0 0 * (z : ℂ) + A 0 1) / (A 1 0 * z + A 1 1) := by
  rw [UpperHalfPlane.coe_smul_of_det_pos (glOfDet_det_pos A hA)]
  rfl

theorem coe_logPoint_mobiusLogMap (g : GL (Fin 2) ℝ) (t : ℝ) (p : ModelCoordinates) :
    (logPoint (mobiusLogMap g t p) : ℂ) = ((g • logPoint p : ℍ) : ℂ) := by
  rw [mobiusLogMap, logPoint_logCoords]

theorem mobiusLogMap_two (g : GL (Fin 2) ℝ) (t : ℝ) (p : ModelCoordinates) :
    mobiusLogMap g t p 2 = p 2 + t :=
  logCoords_two _ _

theorem pullbackMetric_trans_of_isometry {Φ Ψ : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates}
    (hΦ : Diffeomorph.pullbackMetric (coordinateModelMetric .hyperbolicProduct) Φ =
      coordinateModelMetric .hyperbolicProduct)
    (hΨ : Diffeomorph.pullbackMetric (coordinateModelMetric .hyperbolicProduct) Ψ =
      coordinateModelMetric .hyperbolicProduct) :
    Diffeomorph.pullbackMetric (coordinateModelMetric .hyperbolicProduct) (Φ.trans Ψ) =
      coordinateModelMetric .hyperbolicProduct := by
  rw [← Diffeomorph.pullbackMetric_trans, hΨ, hΦ]

theorem pullbackMetric_symm_of_isometry {Φ : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates}
    (hΦ : Diffeomorph.pullbackMetric (coordinateModelMetric .hyperbolicProduct) Φ =
      coordinateModelMetric .hyperbolicProduct) :
    Diffeomorph.pullbackMetric (coordinateModelMetric .hyperbolicProduct) Φ.symm =
      coordinateModelMetric .hyperbolicProduct := by
  conv_lhs => rw [← hΦ]
  rw [Diffeomorph.pullbackMetric_trans, Diffeomorph.symm_trans_self,
    Diffeomorph.pullbackMetric_refl]

theorem foldFlip_zero_apply (p : ModelCoordinates) :
    foldFlip 0 p = ConeShape.FoldData.flipMap p := by
  rw [foldFlip_apply]
  ext i
  fin_cases i
  · simp [GC.Seifert.flipMap_zero]
  · simp [GC.Seifert.flipMap_one]
  · simp [GC.Seifert.flipMap_two]

theorem coe_logPoint_foldFlip (p : ModelCoordinates) :
    (logPoint (foldFlip 0 p) : ℂ) = -conj (logPoint p : ℂ) := by
  rw [foldFlip_zero_apply, coe_logPoint', coe_logPoint']
  apply Complex.ext <;> simp

theorem foldFlip_two (p : ModelCoordinates) : foldFlip 0 p 2 = -p 2 := by
  rw [foldFlip_zero_apply]
  simp

def fibreShift (t : ℝ) : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates :=
  pairingDiffeo 1 (by simp) t

theorem fibreShift_apply (t : ℝ) (p : ModelCoordinates) :
    fibreShift t p = mobiusLogMap 1 t p := rfl

theorem logPoint_fibreShift (t : ℝ) (p : ModelCoordinates) :
    logPoint (fibreShift t p) = logPoint p := by
  rw [fibreShift_apply, mobiusLogMap, logPoint_logCoords, one_smul]

theorem fibreShift_two (t : ℝ) (p : ModelCoordinates) : fibreShift t p 2 = p 2 + t :=
  mobiusLogMap_two _ _ _

theorem pullbackMetric_fibreShift (t : ℝ) :
    Diffeomorph.pullbackMetric (coordinateModelMetric .hyperbolicProduct) (fibreShift t) =
      coordinateModelMetric .hyperbolicProduct :=
  pullbackMetric_pairingDiffeo _ _ _

namespace ConeShape

variable (σ : ConeShape)

def wallOneMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![1, 2 * σ.width; 0, 1]

theorem wallOneMatrix_det : 0 < σ.wallOneMatrix.det := by
  simp [wallOneMatrix, Matrix.det_fin_two_of]

def wallOneLift : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates :=
  (foldFlip 0).trans
    (pairingDiffeo (glOfDet σ.wallOneMatrix σ.wallOneMatrix_det)
      (glOfDet_det_pos _ σ.wallOneMatrix_det) 0)

theorem wallOneLift_apply (p : ModelCoordinates) :
    σ.wallOneLift p = mobiusLogMap (glOfDet σ.wallOneMatrix σ.wallOneMatrix_det) 0
      (foldFlip 0 p) := rfl

theorem coe_logPoint_wallOneLift (p : ModelCoordinates) :
    (logPoint (σ.wallOneLift p) : ℂ) = σ.refl 1 (logPoint p) := by
  rw [wallOneLift_apply, coe_logPoint_mobiusLogMap, coe_glOfDet_smul, coe_logPoint_foldFlip]
  simp only [wallOneMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  simp only [refl]
  push_cast
  ring

theorem wallOneLift_two (p : ModelCoordinates) : σ.wallOneLift p 2 = -p 2 := by
  rw [wallOneLift_apply, mobiusLogMap_two, foldFlip_two, add_zero]

theorem pullbackMetric_wallOneLift :
    Diffeomorph.pullbackMetric (coordinateModelMetric .hyperbolicProduct) σ.wallOneLift =
      coordinateModelMetric .hyperbolicProduct :=
  pullbackMetric_trans_of_isometry (pullbackMetric_foldFlip 0) (pullbackMetric_pairingDiffeo _ _ _)

def wallTwoMatrix : Matrix (Fin 2) (Fin 2) ℝ := !![1 / 4, 0; 1, 1 / 4]

theorem wallTwoMatrix_det : 0 < wallTwoMatrix.det := by
  simp [wallTwoMatrix, Matrix.det_fin_two_of]

def wallTwoLift (t : ℝ) : ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates :=
  (foldFlip 0).trans
    (pairingDiffeo (glOfDet wallTwoMatrix wallTwoMatrix_det)
      (glOfDet_det_pos _ wallTwoMatrix_det) t)

theorem wallTwoLift_apply (t : ℝ) (p : ModelCoordinates) :
    wallTwoLift t p = mobiusLogMap (glOfDet wallTwoMatrix wallTwoMatrix_det) t (foldFlip 0 p) :=
  rfl

theorem coe_logPoint_wallTwoLift (hσ : σ.θ₂ = 0) (t : ℝ) (p : ModelCoordinates) :
    (logPoint (wallTwoLift t p) : ℂ) = σ.refl 2 (logPoint p) := by
  rw [wallTwoLift_apply, coe_logPoint_mobiusLogMap, coe_glOfDet_smul, coe_logPoint_foldFlip]
  simp only [wallTwoMatrix, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.empty_val', Matrix.cons_val_fin_one]
  simp only [refl, σ.cusp_centre hσ]
  set z : ℂ := (logPoint p : ℂ)
  have hz : 0 < z.im := logPoint_im_pos p
  have h1 : (1 : ℂ) * -conj z + 1 / 4 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have h2 : conj z - 1 / 4 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  have h3 : -1 + conj z * 4 ≠ 0 := by
    intro h
    have := congrArg Complex.im h
    simp at this
    linarith
  push_cast
  rw [show (1 : ℂ) / 4 + 1 / 16 / (conj z - 1 / 4) = (conj z / 4) / (conj z - 1 / 4) by
    rw [eq_div_iff h2, add_mul, div_mul_cancel₀ _ h2]
    ring, div_eq_div_iff h1 h2]
  ring

theorem wallTwoLift_two (t : ℝ) (p : ModelCoordinates) : wallTwoLift t p 2 = t - p 2 := by
  rw [wallTwoLift_apply, mobiusLogMap_two, foldFlip_two]
  ring

theorem pullbackMetric_wallTwoLift (t : ℝ) :
    Diffeomorph.pullbackMetric (coordinateModelMetric .hyperbolicProduct) (wallTwoLift t) =
      coordinateModelMetric .hyperbolicProduct :=
  pullbackMetric_trans_of_isometry (pullbackMetric_foldFlip 0) (pullbackMetric_pairingDiffeo _ _ _)

end ConeShape

def screwMatrix (v : ℂ) (β : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![Real.cos β - v.re / v.im * Real.sin β, (v.re ^ 2 + v.im ^ 2) / v.im * Real.sin β;
    -(Real.sin β / v.im), v.re / v.im * Real.sin β + Real.cos β]

theorem screwMatrix_det {v : ℂ} (hv : 0 < v.im) (β : ℝ) : (screwMatrix v β).det = 1 := by
  rw [screwMatrix, Matrix.det_fin_two_of]
  have hb : v.im ≠ 0 := hv.ne'
  have hs := Real.sin_sq_add_cos_sq β
  field_simp
  linear_combination v.im ^ 2 * hs

theorem screwMatrix_det_pos {v : ℂ} (hv : 0 < v.im) (β : ℝ) : 0 < (screwMatrix v β).det := by
  rw [screwMatrix_det hv]
  exact one_pos

def screwLift (v : ℂ) (hv : 0 < v.im) (β t : ℝ) :
    ModelCoordinates ≃ₘ⟮𝓡 3, 𝓡 3⟯ ModelCoordinates :=
  pairingDiffeo (glOfDet (screwMatrix v β) (screwMatrix_det_pos hv β))
    (glOfDet_det_pos _ (screwMatrix_det_pos hv β)) t

theorem screwLift_apply (v : ℂ) (hv : 0 < v.im) (β t : ℝ) (p : ModelCoordinates) :
    screwLift v hv β t p =
      mobiusLogMap (glOfDet (screwMatrix v β) (screwMatrix_det_pos hv β)) t p :=
  rfl

theorem screwLift_two (v : ℂ) (hv : 0 < v.im) (β t : ℝ) (p : ModelCoordinates) :
    screwLift v hv β t p 2 = p 2 + t :=
  mobiusLogMap_two _ _ _

theorem pullbackMetric_screwLift (v : ℂ) (hv : 0 < v.im) (β t : ℝ) :
    Diffeomorph.pullbackMetric (coordinateModelMetric .hyperbolicProduct) (screwLift v hv β t) =
      coordinateModelMetric .hyperbolicProduct :=
  pullbackMetric_pairingDiffeo _ _ _

theorem coneDisc_screwLift (v : ℂ) (hv : 0 < v.im) (β t : ℝ) (p : ModelCoordinates) :
    coneDisc v (logPoint (screwLift v hv β t p)) =
      exp (2 * (β : ℂ) * I) * coneDisc v (logPoint p) := by
  rw [screwLift_apply, coe_logPoint_mobiusLogMap, coe_glOfDet_smul]
  set z : ℂ := (logPoint p : ℂ) with hzdef
  have hz : 0 < z.im := logPoint_im_pos p
  set a : ℝ := v.re
  set b : ℝ := v.im
  have hb : (b : ℂ) ≠ 0 := by exact_mod_cast hv.ne'
  set co : ℝ := Real.cos β
  set si : ℝ := Real.sin β
  have hcs : co ^ 2 + si ^ 2 = 1 := by rw [add_comm]; exact Real.sin_sq_add_cos_sq β
  have hv' : v = (a : ℂ) + (b : ℂ) * I := (Complex.re_add_im v).symm
  set g := glOfDet (screwMatrix v β) (screwMatrix_det_pos hv β)
  have e00 : screwMatrix v β 0 0 = co - a / b * si := rfl
  have e01 : screwMatrix v β 0 1 = (a ^ 2 + b ^ 2) / b * si := rfl
  have e10 : screwMatrix v β 1 0 = -(si / b) := rfl
  have e11 : screwMatrix v β 1 1 = a / b * si + co := rfl
  set Dn : ℂ := ((screwMatrix v β 1 0 : ℝ) : ℂ) * z + ((screwMatrix v β 1 1 : ℝ) : ℂ) with hDn
  have hD : Dn ≠ 0 := UpperHalfPlane.denom_ne_zero g (logPoint p)
  set Nm : ℂ := ((screwMatrix v β 0 0 : ℝ) : ℂ) * z + ((screwMatrix v β 0 1 : ℝ) : ℂ) with hNm
  have he : exp ((β : ℂ) * I) = (co : ℂ) + si * I := by
    rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
  have hu : exp (2 * (β : ℂ) * I) = ((co : ℂ) + si * I) ^ 2 := by
    rw [show 2 * (β : ℂ) * I = (β : ℂ) * I + (β : ℂ) * I by ring, Complex.exp_add, he]
    ring
  have hzv : z - conj v ≠ 0 := sub_conj_ne_zero hv hz
  have h1 : Nm - v * Dn = ((co : ℂ) + si * I) * (z - v) := by
    rw [hNm, hDn, e00, e01, e10, e11, hv']
    push_cast
    field_simp
    linear_combination (b ^ 2 * si) * I_sq
  have h2 : Nm - conj v * Dn = ((co : ℂ) - si * I) * (z - conj v) := by
    rw [hNm, hDn, e00, e01, e10, e11, hv']
    simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    field_simp
    linear_combination (b ^ 2 * si) * I_sq
  have hcsi : ((co : ℂ) - si * I) ≠ 0 := by
    intro h
    have h1 : co = 0 := by simpa using congrArg Complex.re h
    have h2 : si = 0 := by simpa using congrArg Complex.im h
    rw [h1, h2] at hcs
    norm_num at hcs
  unfold coneDisc
  rw [show Nm / Dn - v = (Nm - v * Dn) / Dn by field_simp,
    show Nm / Dn - conj v = (Nm - conj v * Dn) / Dn by field_simp, h1, h2, hu]
  have hprod : ((co : ℂ) + si * I) * ((co : ℂ) - si * I) = 1 := by
    have : ((co : ℂ) + si * I) * ((co : ℂ) - si * I) = ((co ^ 2 + si ^ 2 : ℝ) : ℂ) := by
      push_cast
      linear_combination (-(si : ℂ) ^ 2) * I_sq
    rw [this, hcs]
    simp
  rw [div_div_div_cancel_right₀ hD, mul_div_mul_comm]
  congr 1
  rw [div_eq_iff hcsi]
  linear_combination (-((co : ℂ) + si * I)) * hprod

end GC.Seifert
