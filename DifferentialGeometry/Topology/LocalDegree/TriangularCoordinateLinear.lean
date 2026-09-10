import DifferentialGeometry.Topology.LocalDegree.LinearSphere
import DifferentialGeometry.Topology.LocalDegree.SphereDegree

set_option autoImplicit false
open Metric Set
open scoped unitInterval
noncomputable section
namespace Poincare.LocalDegree
variable {E D : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup D] [NormedSpace ℝ D]


def triangularLinearEquiv (ℓ : E →L[ℝ] ℝ) (c : ℝ) (hc : c ≠ 0) :
    (E × ℝ) ≃L[ℝ] (E × ℝ) where
  toFun p := (p.1, ℓ p.1 + c * p.2)
  invFun q := (q.1, c⁻¹ * (q.2 - ℓ q.1))
  left_inv p := by
    apply Prod.ext
    · rfl
    change c⁻¹ * (ℓ p.1 + c * p.2 - ℓ p.1) = p.2
    rw [add_sub_cancel_left, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  right_inv p := by
    apply Prod.ext
    · rfl
    change ℓ p.1 + c * (c⁻¹ * (p.2 - ℓ p.1)) = p.2
    rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
    abel
  map_add' p q := by
    apply Prod.ext
    · rfl
    change ℓ (p.1 + q.1) + c * (p.2 + q.2) =
      (ℓ p.1 + c * p.2) + (ℓ q.1 + c * q.2)
    rw [map_add]
    ring
  map_smul' a p := by
    apply Prod.ext
    · rfl
    change ℓ (a • p.1) + c * (a * p.2) = a * (ℓ p.1 + c * p.2)
    rw [map_smul]
    change a * ℓ p.1 + c * (a * p.2) = _
    ring
  continuous_toFun := continuous_fst.prodMk
    ((ℓ.continuous.comp continuous_fst).add (continuous_const.mul continuous_snd))
  continuous_invFun := continuous_fst.prodMk
    (continuous_const.mul (continuous_snd.sub (ℓ.continuous.comp continuous_fst)))


@[simp]
theorem triangularLinearEquiv_apply (ℓ : E →L[ℝ] ℝ) (c : ℝ) (hc : c ≠ 0) (p : E × ℝ) :
    triangularLinearEquiv ℓ c hc p = (p.1, ℓ p.1 + c * p.2) := rfl


@[simp]
theorem triangularLinearEquiv_symm_apply (ℓ : E →L[ℝ] ℝ) (c : ℝ) (hc : c ≠ 0)
    (p : E × ℝ) :
    (triangularLinearEquiv ℓ c hc).symm p = (p.1, c⁻¹ * (p.2 - ℓ p.1)) := rfl


def triangularConjugate (C : D ≃L[ℝ] E × ℝ) (ℓ : E →L[ℝ] ℝ) (c : ℝ) (hc : c ≠ 0) : D ≃L[ℝ] D :=
  (C.trans (triangularLinearEquiv ℓ c hc)).trans C.symm


@[simp]
theorem triangularConjugate_apply (C : D ≃L[ℝ] E × ℝ) (ℓ : E →L[ℝ] ℝ)
    (c : ℝ) (hc : c ≠ 0) (x : D) :
    triangularConjugate C ℓ c hc x = C.symm ((C x).1, ℓ (C x).1 + c * (C x).2) := rfl

private def triangularLinearInterpolation (C : D ≃L[ℝ] E × ℝ)
    (ℓ : E →L[ℝ] ℝ) (c : ℝ) : C(I × sphere (0 : D) 1, D) where
  toFun p := C.symm ((C p.2).1,
    (1 - (p.1 : ℝ)) * ℓ (C p.2).1 + ((1 - (p.1 : ℝ)) * c + (p.1 : ℝ)) * (C p.2).2)
  continuous_toFun := by fun_prop

private theorem triangularLinearInterpolation_ne_zero (C : D ≃L[ℝ] E × ℝ)
    (ℓ : E →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c) (p : I × sphere (0 : D) 1) :
    triangularLinearInterpolation C ℓ c p ≠ 0 := by
  intro hz
  have he := C.symm.map_eq_zero_iff.mp hz
  have hfst : (C p.2).1 = 0 := congrArg Prod.fst he
  have hsnd := congrArg Prod.snd he
  change (1 - (p.1 : ℝ)) * ℓ (C p.2).1 +
    ((1 - (p.1 : ℝ)) * c + (p.1 : ℝ)) * (C p.2).2 = 0 at hsnd
  rw [hfst, map_zero, mul_zero, zero_add] at hsnd
  have hcoef : 0 < (1 - (p.1 : ℝ)) * c + (p.1 : ℝ) := by
    by_cases ht : (p.1 : ℝ) = 1
    · simp [ht]
    · exact add_pos_of_pos_of_nonneg
        (mul_pos (sub_pos.mpr (lt_of_le_of_ne p.1.property.2 ht)) hc) p.1.property.1
  have ht0 := (mul_eq_zero.mp hsnd).resolve_left hcoef.ne'
  have hp0 : C p.2 = 0 := Prod.ext hfst ht0
  exact ne_zero_of_mem_unit_sphere p.2 (C.map_eq_zero_iff.mp hp0)

def triangularSphereHomotopy (C : D ≃L[ℝ] E × ℝ)
    (ℓ : E →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c) :
    (linearSphereMap (triangularConjugate C ℓ c hc.ne')).Homotopy
      (ContinuousMap.id (sphere (0 : D) 1)) where
  toFun p := (homeomorphUnitSphereProd D
    ⟨triangularLinearInterpolation C ℓ c p, triangularLinearInterpolation_ne_zero C ℓ hc p⟩).1
  continuous_toFun := (homeomorphUnitSphereProd D).continuous.fst.comp
    ((triangularLinearInterpolation C ℓ c).continuous.subtype_mk
      (triangularLinearInterpolation_ne_zero C ℓ hc))
  map_zero_left x := by
    apply Subtype.ext
    simp [homeomorphUnitSphereProd_apply_fst_coe, triangularLinearInterpolation,
      linearSphereMap_apply, triangularConjugate, triangularLinearEquiv]
  map_one_left x := by
    apply Subtype.ext
    simp [homeomorphUnitSphereProd_apply_fst_coe, triangularLinearInterpolation,
      norm_eq_of_mem_sphere]


theorem triangularSphereHomotopy_apply (C : D ≃L[ℝ] E × ℝ)
    (ℓ : E →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c) (p : I × sphere (0 : D) 1) :
    (triangularSphereHomotopy C ℓ hc p : D) =
      let y := C.symm ((C p.2).1, (1 - (p.1 : ℝ)) * ℓ (C p.2).1 +
        ((1 - (p.1 : ℝ)) * c + (p.1 : ℝ)) * (C p.2).2)
      ‖y‖⁻¹ • y := by
  exact homeomorphUnitSphereProd_apply_fst_coe D _


theorem euclideanSphereDegree_triangularConjugate {d : ℕ}
    (C : EuclideanSpace ℝ (Fin (d + 1)) ≃L[ℝ] E × ℝ)
    (ℓ : E →L[ℝ] ℝ) {c : ℝ} (hc : 0 < c) :
    euclideanSphereDegree (linearSphereMap (triangularConjugate C ℓ c hc.ne')) = 1 := by
  rw [euclideanSphereDegree_eq_of_homotopy (triangularSphereHomotopy C ℓ hc), euclideanSphereDegree_id]

end Poincare.LocalDegree
