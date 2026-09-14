import DifferentialGeometry.Topology.Homology.ContractibleCoverSignFunctional
import DifferentialGeometry.Topology.Homology.TriangleRayComplement
import DifferentialGeometry.Topology.Homology.EuclideanLocalVanishing
import DifferentialGeometry.Topology.Homology.TriangleBoundary

noncomputable section

namespace DifferentialGeometry.Topology.SimplexDegree

universe u

private instance : PathConnectedSpace puncturedPlane.{u} :=
  puncturedSpace_pathConnected_of_finrank (liftedSphereSpace.{u} 0)
    (by rw [liftedSphereSpace_finrank]; norm_num)

private instance : ContractibleSpace puncturedPlanePositiveRayComplement.{u} :=
  puncturedPlanePositiveRayComplement_contractibleSpace

private instance : ContractibleSpace puncturedPlaneNegativeRayComplement.{u} :=
  puncturedPlaneNegativeRayComplement_contractibleSpace

def puncturedPlaneDiagonalDegree : integralSingularHomology 1 puncturedPlane.{u} →ₗ[ℤ] ℤ :=
  integralHomologyOneCoverSignFunctional puncturedPlanePositiveRayComplement
    puncturedPlaneNegativeRayComplement isOpen_puncturedPlanePositiveRayComplement
    isOpen_puncturedPlaneNegativeRayComplement puncturedPlaneRayComplements_cover
    puncturedPlaneRayOverlapSign true


theorem puncturedPlaneDiagonalDegree_standardTriangleBoundaryClass :
    puncturedPlaneDiagonalDegree standardTriangleBoundaryClass.{u} = 1 := by
  change integralHomologyOneCoverSignFunctional puncturedPlanePositiveRayComplement
    puncturedPlaneNegativeRayComplement isOpen_puncturedPlanePositiveRayComplement
    isOpen_puncturedPlaneNegativeRayComplement puncturedPlaneRayComplements_cover
    puncturedPlaneRayOverlapSign true
      (integralHomologyClassOf 0 (integralChainHom 1 standardTriangleBoundaryChain) _) = 1
  rw [integralHomologyOneCoverSignFunctional_apply
    puncturedPlanePositiveRayComplement puncturedPlaneNegativeRayComplement
    isOpen_puncturedPlanePositiveRayComplement isOpen_puncturedPlaneNegativeRayComplement
    puncturedPlaneRayComplements_cover puncturedPlaneRayOverlapSign true
    (integralChainHom 1 standardTriangleBoundaryChain) _
    trianglePositiveEdgeChain triangleNegativeEdgeChain triangleEdgeChain_split
    (triangleOverlapVertex 0) (triangleOverlapVertex 1) triangleEdgeBoundaryChain_inclusion]
  simp [puncturedPlaneRayOverlapSign_apply, triangleOverlapVertex, standardTriangleVertex]

end DifferentialGeometry.Topology.SimplexDegree
