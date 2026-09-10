import DifferentialGeometry.Topology.LocalDegree.LinearDegreePath
import DifferentialGeometry.Topology.LocalDegree.OrthogonalDegree

set_option autoImplicit false
open Metric
noncomputable section
namespace Poincare.LocalDegree

variable {n : ℕ}

private theorem reduction_sphere_nonzero
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (t : unitInterval) (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    orthogonalReductionPath A t v ≠ 0 := by
  apply orthogonalReductionPath_nonzero
  intro hv
  have hn := norm_eq_of_mem_sphere v
  rw [hv, norm_zero] at hn
  exact zero_ne_one hn

def linearSphereOrthogonalHomotopy
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n)) :
    (linearSphereMap A).Homotopy
      (linearSphereMap (orthogonalReduction A).toContinuousLinearEquiv) where
  toFun p := (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin n))
    ⟨orthogonalReductionPath A p.1 p.2, reduction_sphere_nonzero A p.1 p.2⟩).1
  continuous_toFun := by
    have hc : Continuous (fun p : unitInterval × sphere (0 : EuclideanSpace ℝ (Fin n)) 1 =>
        orthogonalReductionPath A p.1 p.2) :=
      ((orthogonalReductionPath A).continuous.comp continuous_fst).clm_apply
        (continuous_subtype_val.comp continuous_snd)
    exact (homeomorphUnitSphereProd (EuclideanSpace ℝ (Fin n))).continuous.fst.comp
      (hc.subtype_mk (fun p => reduction_sphere_nonzero A p.1 p.2))
  map_zero_left v := by
    apply Subtype.ext
    simp [homeomorphUnitSphereProd_apply_fst_coe]
  map_one_left v := by
    apply Subtype.ext
    simp [homeomorphUnitSphereProd_apply_fst_coe]


theorem linearSphereOrthogonalHomotopy_apply
    (A : EuclideanSpace ℝ (Fin n) ≃L[ℝ] EuclideanSpace ℝ (Fin n))
    (t : unitInterval) (v : sphere (0 : EuclideanSpace ℝ (Fin n)) 1) :
    (linearSphereOrthogonalHomotopy A (t, v) : EuclideanSpace ℝ (Fin n)) =
      ‖orthogonalReductionPath A t v‖⁻¹ • orthogonalReductionPath A t v :=
  homeomorphUnitSphereProd_apply_fst_coe _ _

theorem euclideanSphereDegree_linearEquiv {d : ℕ}
    (A : EuclideanSpace ℝ (Fin (d + 1)) ≃L[ℝ] EuclideanSpace ℝ (Fin (d + 1))) :
    euclideanSphereDegree (linearSphereMap A) =
      (SignType.sign (LinearMap.det A.toLinearMap) : ℤ) := by
  rw [euclideanSphereDegree_eq_of_homotopy (linearSphereOrthogonalHomotopy A),
    euclideanSphereDegree_linearIsometryEquiv, orthogonalReduction_det_sign]

end Poincare.LocalDegree
