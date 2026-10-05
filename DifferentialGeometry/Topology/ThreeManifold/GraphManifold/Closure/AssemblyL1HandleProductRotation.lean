import Mathlib.Analysis.Complex.Isometry
import Mathlib.LinearAlgebra.Complex.Determinant
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Chapter-14 assembly, item L1, step T2′ (handles in product form): rotations of the plane

Lane ASM-L1b2. `handlePlaneRot s` is the rotation of `ℝ²` by the angle `s`, read through the
identification `ℂ ≃ ℝ²` of `planeOfCircle` (`Complex.orthonormalBasisOneI.repr`). Every linear
isometry of `ℝ²` of determinant `1` is one of them (`exists_handlePlaneRot_eq`, from
`linear_isometry_complex`: the reflections `conj ∘ rotation` have determinant `-1`), and the
rotation depends smoothly on the angle and the point (`contDiff_handlePlaneRot`). This is the
`O(2)` path between the two end isometries of a handle in product form.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open scoped ContDiff

namespace GC.GraphManifold.Assembly

/-- The rotation of `ℝ²` by the angle `s` (through `ℂ ≃ ℝ²`). -/
def handlePlaneRot (s : ℝ) : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (Complex.orthonormalBasisOneI.repr.symm.trans (rotation (Circle.exp s))).trans
    Complex.orthonormalBasisOneI.repr

theorem handlePlaneRot_apply (s : ℝ) (z : EuclideanSpace ℝ (Fin 2)) :
    handlePlaneRot s z = Complex.orthonormalBasisOneI.repr
      (Complex.exp (s * Complex.I) * Complex.orthonormalBasisOneI.repr.symm z) := by
  simp only [handlePlaneRot, LinearIsometryEquiv.trans_apply, rotation_apply, Circle.coe_exp]

theorem handlePlaneRot_zero (z : EuclideanSpace ℝ (Fin 2)) : handlePlaneRot 0 z = z := by
  rw [handlePlaneRot_apply, Complex.ofReal_zero, zero_mul, Complex.exp_zero, one_mul,
    LinearIsometryEquiv.apply_symm_apply]

/-- The rotation is smooth in the angle and the point. -/
theorem contDiff_handlePlaneRot :
    ContDiff ℝ ∞ (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => handlePlaneRot p.1 p.2) := by
  have hexp : ContDiff ℝ ∞ (fun p : ℝ × EuclideanSpace ℝ (Fin 2) =>
      Complex.exp ((p.1 : ℂ) * Complex.I)) :=
    (Complex.contDiff_exp (𝕜 := ℝ)).comp
      ((Complex.ofRealCLM.contDiff.comp contDiff_fst).mul contDiff_const)
  have hmul : ContDiff ℝ ∞ (fun p : ℝ × EuclideanSpace ℝ (Fin 2) =>
      Complex.exp ((p.1 : ℂ) * Complex.I) *
        Complex.orthonormalBasisOneI.repr.symm p.2) :=
    hexp.mul (Complex.orthonormalBasisOneI.repr.symm.toContinuousLinearEquiv.contDiff.comp
      contDiff_snd)
  have h := Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv.contDiff.comp hmul
  have he : (fun p : ℝ × EuclideanSpace ℝ (Fin 2) => handlePlaneRot p.1 p.2) =
      ⇑Complex.orthonormalBasisOneI.repr.toContinuousLinearEquiv ∘ fun p =>
        Complex.exp ((p.1 : ℂ) * Complex.I) * Complex.orthonormalBasisOneI.repr.symm p.2 := by
    funext p
    rw [handlePlaneRot_apply]
    rfl
  rw [he]
  exact h

/-- The determinant of a linear isometry of `ℂ` that is a reflection `conj` followed by a
rotation is `-1`. -/
theorem det_conjLIE_trans_rotation (a : Circle) :
    LinearMap.det ((Complex.conjLIE.trans (rotation a)).toLinearEquiv : ℂ →ₗ[ℝ] ℂ) = -1 := by
  have h : ((Complex.conjLIE.trans (rotation a)).toLinearEquiv : ℂ →ₗ[ℝ] ℂ) =
      ((rotation a).toLinearEquiv : ℂ →ₗ[ℝ] ℂ) ∘ₗ Complex.conjAe.toLinearEquiv.toLinearMap :=
    LinearMap.ext fun z => rfl
  rw [h, LinearMap.det_comp, det_rotation, Complex.det_conjAe, one_mul]

/-- **A linear isometry of `ℝ²` of determinant `1` is a rotation.** -/
theorem exists_handlePlaneRot_eq (B : EuclideanSpace ℝ (Fin 2) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2))
    (hB : LinearMap.det B.toLinearMap = 1) : ∃ α : ℝ, B = handlePlaneRot α := by
  set ι := Complex.orthonormalBasisOneI.repr with hι
  set f : ℂ ≃ₗᵢ[ℝ] ℂ := (ι.trans B).trans ι.symm with hf
  have hdet : LinearMap.det (f.toLinearEquiv : ℂ →ₗ[ℝ] ℂ) = 1 := by
    have h : (f.toLinearEquiv : ℂ →ₗ[ℝ] ℂ) = (ι.symm.toLinearEquiv : _ →ₗ[ℝ] ℂ) ∘ₗ
        B.toLinearMap ∘ₗ (ι.symm.toLinearEquiv.symm : ℂ →ₗ[ℝ] _) :=
      LinearMap.ext fun z => rfl
    rw [h, LinearMap.det_conj]
    exact hB
  obtain ⟨a, ha | ha⟩ := linear_isometry_complex f
  · refine ⟨Complex.arg a, ?_⟩
    ext1 z
    have hz : f (ι.symm z) = ι.symm (B z) := by
      rw [hf]
      simp only [LinearIsometryEquiv.trans_apply, LinearIsometryEquiv.apply_symm_apply]
    have hz' : B z = ι (f (ι.symm z)) := by
      rw [hz, LinearIsometryEquiv.apply_symm_apply]
    rw [hz', ha, handlePlaneRot, Circle.exp_arg]
    rfl
  · exfalso
    rw [ha, det_conjLIE_trans_rotation] at hdet
    norm_num at hdet

end GC.GraphManifold.Assembly
