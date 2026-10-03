import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.RCLike.Basic
import Mathlib.Analysis.Normed.Operator.LinearIsometry
import Mathlib.LinearAlgebra.Determinant
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

local notation "CylinderAmbient" => EuclideanSpace ℝ (Fin 3)
local notation "SphereTwo" => Metric.sphere (0 : CylinderAmbient) 1

theorem cylinderDeck_involution_eq_neg_of_sphere_free
    (A : CylinderAmbient ≃ₗᵢ[ℝ] CylinderAmbient)
    (hinvolution : Function.Involutive (A : CylinderAmbient → CylinderAmbient))
    (hfree : ∀ y : SphereTwo, A (y : CylinderAmbient) ≠ (y : CylinderAmbient)) :
    A = LinearIsometryEquiv.neg ℝ := by
  classical
  apply LinearIsometryEquiv.ext
  intro v
  change A v = -v
  let w : CylinderAmbient := v + A v
  have hwfixed : A w = w := by
    change A (v + A v) = v + A v
    rw [map_add, hinvolution v]
    exact add_comm _ _
  have hwzero : w = 0 := by
    by_contra hwne
    have hnorm : ‖(‖w‖⁻¹ : ℝ) • w‖ = 1 := norm_smul_inv_norm hwne
    let y : SphereTwo := ⟨(‖w‖⁻¹ : ℝ) • w, by
      simpa only [Metric.mem_sphere, dist_zero_right] using hnorm⟩
    apply hfree y
    change A ((‖w‖⁻¹ : ℝ) • w) = (‖w‖⁻¹ : ℝ) • w
    rw [map_smul, hwfixed]
  apply (add_eq_zero_iff_eq_neg).mp
  change v + A v = 0 at hwzero
  rw [add_comm]
  exact hwzero

theorem cylinderDeck_not_square_neg
    (A : CylinderAmbient ≃ₗᵢ[ℝ] CylinderAmbient) :
    ¬ ∀ v : CylinderAmbient, A (A v) = -v := by
  intro hsquare
  let L : CylinderAmbient →ₗ[ℝ] CylinderAmbient := A.toLinearEquiv.toLinearMap
  have hlinear : L.comp L = (-1 : ℝ) • (LinearMap.id :
      CylinderAmbient →ₗ[ℝ] CylinderAmbient) := by
    apply LinearMap.ext
    intro v
    change A (A v) = (-1 : ℝ) • v
    simpa only [neg_one_smul] using hsquare v
  have hdet := congrArg
    (fun B : CylinderAmbient →ₗ[ℝ] CylinderAmbient => LinearMap.det B) hlinear
  rw [LinearMap.det_comp, LinearMap.det_smul, LinearMap.det_id] at hdet
  norm_num [finrank_euclideanSpace_fin] at hdet
  nlinarith [sq_nonneg (LinearMap.det L)]

theorem cylinderDeck_reflection_eq_neg_of_free
    (A : CylinderAmbient ≃ₗᵢ[ℝ] CylinderAmbient)
    (hsquare : Function.Involutive (A : CylinderAmbient → CylinderAmbient) ∨
      ∀ v : CylinderAmbient, A (A v) = -v)
    (hfree : ∀ p : SphereTwo × ℝ,
      (A (p.1 : CylinderAmbient), -p.2) ≠ ((p.1 : CylinderAmbient), p.2)) :
    A = LinearIsometryEquiv.neg ℝ := by
  have hinvolution : Function.Involutive (A : CylinderAmbient → CylinderAmbient) :=
    hsquare.resolve_right (cylinderDeck_not_square_neg A)
  apply cylinderDeck_involution_eq_neg_of_sphere_free A hinvolution
  intro y hy
  apply hfree (y, 0)
  exact Prod.ext hy (neg_zero : -(0 : ℝ) = 0)

theorem cylinderDeck_antipodal_comp_reflection_fixes_central
    (A : CylinderAmbient ≃ₗᵢ[ℝ] CylinderAmbient)
    (hsquare : Function.Involutive (A : CylinderAmbient → CylinderAmbient) ∨
      ∀ v : CylinderAmbient, A (A v) = -v)
    (hfree : ∀ p : SphereTwo × ℝ,
      (A (p.1 : CylinderAmbient), -p.2) ≠ ((p.1 : CylinderAmbient), p.2))
    (y : SphereTwo) :
    ((fun p : CylinderAmbient × ℝ => (-p.1, p.2)) ∘
      (fun p : CylinderAmbient × ℝ => (A p.1, -p.2)))
        ((y : CylinderAmbient), 0) = ((y : CylinderAmbient), 0) := by
  have hA := cylinderDeck_reflection_eq_neg_of_free A hsquare hfree
  change (-A (y : CylinderAmbient), -(0 : ℝ)) = ((y : CylinderAmbient), 0)
  rw [hA]
  simp only [LinearIsometryEquiv.coe_neg, neg_neg, neg_zero]

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
