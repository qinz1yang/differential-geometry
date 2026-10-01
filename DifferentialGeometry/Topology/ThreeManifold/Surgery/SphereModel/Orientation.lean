import DifferentialGeometry.Topology.ThreeManifold.Surgery.SphereModel.Defs
import DifferentialGeometry.Topology.ThreeManifold.Surgery.SphereModel.CapDerivatives
import DifferentialGeometry.Topology.ThreeManifold.Surgery.CutCap.PresentationOrientation

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open private standardNeckCapSum_false_apply
  from DifferentialGeometry.Topology.ThreeManifold.Surgery.SphereModel.Capping

attribute [local instance] threeBallChartedSpace threeBall_isManifold

theorem standardNeckCapping_cap_false_apply (y : ThreeBall) :
    standardNeckCapping.cap (PUnit.unit, false) y = Sum.inl (standardNeckCapFun false y) := by
  rw [← standardNeckCapSum_false_apply y]
  rfl

theorem not_orientation_map_eq_of_sphereOutwardDeterminant_not_pos
    (L : EuclideanSpace ℝ (Fin 3) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin 3))
    (hframe : ¬ 0 < sphereOutwardDeterminant 3 (standardNeckCapFun false 0)
      ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.map L)) :
    ¬ (Orientation.map (Fin 3) L
        (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.orientation =
      (sphereThreeStage.sum sphereThreeStage).orientation.orientation
        (standardNeckCapping.cap (PUnit.unit, false) 0)) := by
  intro heq
  have htarget : (sphereThreeStage.sum sphereThreeStage).orientation.orientation
      (standardNeckCapping.cap (PUnit.unit, false) 0) =
      (sphereOrientation 3 (by decide)).orientation (standardNeckCapFun false 0) := by
    rw [standardNeckCapping_cap_false_apply 0]
    exact (DifferentialGeometry.Topology.ClosedOrientedManifold.sum_orientation_inl sphereThreeStage sphereThreeStage
      (standardNeckCapFun false 0)).trans rfl
  have hb : ((EuclideanSpace.basisFun (Fin 3) ℝ).toBasis.map L).orientation =
      (sphereOrientation 3 (by decide)).orientation (standardNeckCapFun false 0) := by
    rw [Module.Basis.orientation_map, ← htarget]
    exact heq
  exact hframe ((sphereOrientation_characterization 3 (by decide) _ _).mp hb)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
