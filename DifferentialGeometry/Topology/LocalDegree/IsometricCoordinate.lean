import DifferentialGeometry.Topology.LocalDegree.IsolatedZero
import DifferentialGeometry.Topology.LocalDegree.LinearSphere
import Mathlib.Analysis.Normed.Operator.LinearIsometry

set_option autoImplicit false
open Metric Set
noncomputable section
namespace Poincare.LocalDegree
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


theorem IsolatingRadius.isometry_conjugate (A : E ≃ₗᵢ[ℝ] F)
    {f : F → F} {x : E} {R : ℝ} (h : IsolatingRadius f (A x) R) :
    IsolatingRadius (fun y => A.symm (f (A y))) x R where
  pos := h.pos
  continuousOn := A.symm.continuous.comp_continuousOn
    (h.continuousOn.comp A.continuous.continuousOn (fun y hy => by
      simpa only [mem_closedBall, A.dist_map] using hy))
  zero_iff y hy := by
    rw [A.symm.map_eq_zero_iff, h.zero_iff _ (by
      simpa only [mem_closedBall, A.dist_map] using hy), A.injective.eq_iff]

theorem sphereMap_isometry_conjugate (A : E ≃ₗᵢ[ℝ] F)
    {f : F → F} {x : E} {R : ℝ} (h : IsolatingRadius f (A x) R)
    (r : Ioc (0 : ℝ) R) :
    (linearSphereMap A.toContinuousLinearEquiv).comp
        (sphereMap (fun y => A.symm (f (A y))) x R
          (h.isometry_conjugate A).continuousOn (h.isometry_conjugate A).nonzero r) =
      (sphereMap f (A x) R h.continuousOn h.nonzero r).comp
        (linearSphereMap A.toContinuousLinearEquiv) := by
  apply ContinuousMap.ext
  intro v
  apply Subtype.ext
  have hv : (linearSphereMap A.toContinuousLinearEquiv v : F) = A v := by
    rw [linearSphereMap_apply]
    change ‖A v‖⁻¹ • A v = A v
    rw [A.norm_map, norm_eq_of_mem_sphere v]
    simp
  rw [ContinuousMap.comp_apply, linearSphereMap_apply]
  change ‖A (sphereMap (fun y => A.symm (f (A y))) x R
      (h.isometry_conjugate A).continuousOn (h.isometry_conjugate A).nonzero r v : E)‖⁻¹ •
    A (sphereMap (fun y => A.symm (f (A y))) x R
      (h.isometry_conjugate A).continuousOn (h.isometry_conjugate A).nonzero r v : E) = _
  rw [A.norm_map, norm_eq_of_mem_sphere, inv_one, one_smul,
    sphereMap_apply, map_smul, A.apply_symm_apply, A.symm.norm_map,
    ContinuousMap.comp_apply, sphereMap_apply, hv, map_add, map_smul]

end Poincare.LocalDegree
