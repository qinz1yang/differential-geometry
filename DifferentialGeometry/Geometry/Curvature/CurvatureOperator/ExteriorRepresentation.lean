import DifferentialGeometry.Geometry.Metric.ExteriorEndomorphism
import DifferentialGeometry.Geometry.Curvature.Algebraic.Form

set_option autoImplicit false

noncomputable section

namespace exteriorPower

open DifferentialGeometry.Geometry.Curvature
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedAddCommGroup E] [NormedSpace ℝ E] in
private theorem append_two_eq (v w : Fin 2 → E) :
    Fin.append v w = ![v 0, v 1, w 0, w 1] := by
  ext i
  fin_cases i <;> rfl

theorem curvatureTensor_left_alternating
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hT : IsAlgCurvForm (fun x y z w => T ![x, y, z, w]))
    (v w : Fin 2 → E) (i j : Fin 2) (hij : i ≠ j) (hv : v i = v j) :
    T (Fin.append v w) = 0 := by
  have h01 : v 0 = v 1 := by
    fin_cases i <;> fin_cases j <;> simp_all
  rw [append_two_eq, h01]
  have h := hT.anti_first (v 1) (v 1) (w 0) (w 1)
  linarith

theorem curvatureTensor_right_alternating
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hT : IsAlgCurvForm (fun x y z w => T ![x, y, z, w]))
    (v w : Fin 2 → E) (i j : Fin 2) (hij : i ≠ j) (hw : w i = w j) :
    T (Fin.append v w) = 0 := by
  have h01 : w 0 = w 1 := by
    fin_cases i <;> fin_cases j <;> simp_all
  rw [append_two_eq, h01]
  have h := hT.anti_last (v 0) (v 1) (w 1) (w 1)
  linarith

end exteriorPower

namespace exteriorPower

open DifferentialGeometry.Geometry.Curvature
open scoped RealInnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

def traceNormalizedCurvatureEndomorphism
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hT : IsAlgCurvForm (fun x y z w => T ![x, y, z, w])) :
    (⋀[ℝ]^2 E) →L[ℝ] ⋀[ℝ]^2 E :=
  (-2 : ℝ) • multilinearEndomorphism 2 T (curvatureTensor_left_alternating T hT)

theorem endomorphismTensor_traceNormalizedCurvatureEndomorphism
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hT : IsAlgCurvForm (fun x y z w => T ![x, y, z, w])) :
    endomorphismTensor 2 (traceNormalizedCurvatureEndomorphism T hT) = (-2 : ℝ) • T := by
  change endomorphismTensorLinear 2 ((-2 : ℝ) • _) = _
  rw [map_smul]
  congr 1
  exact endomorphismTensor_multilinearEndomorphism 2 T
    (curvatureTensor_left_alternating T hT) (curvatureTensor_right_alternating T hT)

theorem traceNormalizedCurvatureEndomorphism_isSymmetric
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hT : IsAlgCurvForm (fun x y z w => T ![x, y, z, w])) :
    (traceNormalizedCurvatureEndomorphism T hT).toLinearMap.IsSymmetric := by
  rw [isSymmetric_iff_endomorphismTensor, endomorphismTensor_traceNormalizedCurvatureEndomorphism]
  intro v w
  rw [smul_apply, smul_apply, append_two_eq, append_two_eq]
  exact congrArg (fun a : ℝ => (-2 : ℝ) • a) (hT.pair_swap (v 0) (v 1) (w 0) (w 1))

theorem inner_traceNormalizedCurvatureEndomorphism_ιMulti
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hT : IsAlgCurvForm (fun x y z w => T ![x, y, z, w])) (v w : Fin 2 → E) :
    ⟪traceNormalizedCurvatureEndomorphism T hT (ιMulti ℝ 2 v), ιMulti ℝ 2 w⟫ =
      2 * T ![v 0, v 1, w 1, w 0] := by
  rw [← endomorphismTensor_apply_append, endomorphismTensor_traceNormalizedCurvatureEndomorphism,
    smul_apply, append_two_eq, smul_eq_mul]
  have h := hT.anti_last (v 0) (v 1) (w 0) (w 1)
  linarith

def traceNormalizedCurvatureSelfAdjoint
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hT : IsAlgCurvForm (fun a b c d => T ![a, b, c, d])) :
    selfAdjoint ((⋀[ℝ]^2 E) →L[ℝ] ⋀[ℝ]^2 E) :=
  ⟨traceNormalizedCurvatureEndomorphism T hT,
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
      (traceNormalizedCurvatureEndomorphism_isSymmetric T hT)⟩

theorem traceNormalizedCurvatureSelfAdjoint_coe
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hT : IsAlgCurvForm (fun a b c d => T ![a, b, c, d])) :
    (traceNormalizedCurvatureSelfAdjoint T hT : (⋀[ℝ]^2 E) →L[ℝ] ⋀[ℝ]^2 E) =
      traceNormalizedCurvatureEndomorphism T hT := rfl

theorem eq_traceNormalizedCurvatureEndomorphism_iff
    (A : (⋀[ℝ]^2 E) →L[ℝ] ⋀[ℝ]^2 E)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hT : IsAlgCurvForm (fun a b c d => T ![a, b, c, d])) :
    A = traceNormalizedCurvatureEndomorphism T hT ↔
      ∀ a b c d : E, ⟪A (ιMulti ℝ 2 ![a, b]), ιMulti ℝ 2 ![c, d]⟫ =
        2 * T ![a, b, d, c] := by
  constructor
  · rintro rfl a b c d
    exact inner_traceNormalizedCurvatureEndomorphism_ιMulti T hT ![a, b] ![c, d]
  · intro h
    apply endomorphismTensor_injective 2
    ext v
    have hv : v = Fin.append ![v 0, v 1] ![v 2, v 3] := by
      ext i
      fin_cases i <;> rfl
    rw [hv, endomorphismTensor_apply_append, endomorphismTensor_apply_append,
      inner_traceNormalizedCurvatureEndomorphism_ιMulti]
    exact h _ _ _ _

theorem existsUnique_traceNormalizedCurvatureSelfAdjoint
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hT : IsAlgCurvForm (fun a b c d => T ![a, b, c, d])) :
    ∃! A : selfAdjoint ((⋀[ℝ]^2 E) →L[ℝ] ⋀[ℝ]^2 E),
      ∀ a b c d : E, ⟪(A : (⋀[ℝ]^2 E) →L[ℝ] ⋀[ℝ]^2 E) (ιMulti ℝ 2 ![a, b]),
        ιMulti ℝ 2 ![c, d]⟫ = 2 * T ![a, b, d, c] := by
  refine ⟨traceNormalizedCurvatureSelfAdjoint T hT, ?_, ?_⟩
  · exact (eq_traceNormalizedCurvatureEndomorphism_iff _ T hT).mp rfl
  · intro A hA
    apply Subtype.ext
    exact (eq_traceNormalizedCurvatureEndomorphism_iff _ T hT).mpr hA

theorem traceNormalizedCurvatureEndomorphism_eq_smul_id_of_constant_curvature
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin 4 => E) ℝ)
    (hT : IsAlgCurvForm (fun x y z w => T ![x, y, z, w])) (k : ℝ)
    (hk : ∀ a b c d, T ![a, b, c, d] =
      k * (⟪a, d⟫ * ⟪b, c⟫ - ⟪a, c⟫ * ⟪b, d⟫)) :
    traceNormalizedCurvatureEndomorphism T hT = (2 * k) • ContinuousLinearMap.id ℝ (⋀[ℝ]^2 E) := by
  apply endomorphismTensor_injective 2
  ext v
  rw [endomorphismTensor_traceNormalizedCurvatureEndomorphism]
  have hv : v = ![v 0, v 1, v 2, v 3] := by
    ext i
    fin_cases i <;> rfl
  have happ : v = Fin.append ![v 0, v 1] ![v 2, v 3] := by
    ext i
    fin_cases i <;> rfl
  rw [smul_apply, smul_eq_mul]
  conv_lhs => rw [hv, hk]
  conv_rhs => rw [happ]
  rw [endomorphismTensor_apply_append, smul_apply,
    ContinuousLinearMap.id_apply, real_inner_smul_left, inner_ιMulti_ιMulti, Matrix.det_fin_two]
  simp only [Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one]
  ring

end exteriorPower
