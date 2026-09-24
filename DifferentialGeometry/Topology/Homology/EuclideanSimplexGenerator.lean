import DifferentialGeometry.Topology.Homology.TriangleBoundaryDegree

noncomputable section

namespace DifferentialGeometry.Topology.SimplexDegree

universe u

def euclideanSimplexBoundaryDegree :
    integralSingularHomology 2 puncturedThreeSpace.{u} →ₗ[ℤ] ℤ :=
  puncturedPlaneDiagonalDegree.comp tetrahedronToTriangleHomology

theorem euclideanSimplexBoundaryDegree_euclideanStandardSimplexBoundaryClass :
    euclideanSimplexBoundaryDegree euclideanStandardSimplexBoundaryClass.{u} = 1 := by
  rw [euclideanSimplexBoundaryDegree, LinearMap.comp_apply,
    tetrahedronToTriangleHomology_euclideanStandardSimplexBoundaryClass,
    puncturedPlaneDiagonalDegree_standardTriangleBoundaryClass]

theorem euclideanStandardSimplexClass_generator :
    Function.Bijective (fun z : ℤ => z • euclideanStandardSimplexClass.{u}) := by
  apply euclideanStandardSimplexClass_generator_iff_isSphereHomologyGenerator.mpr
  apply (isSphereHomologyGenerator_iff_exists_functional 1 _).mpr
  let e := (integralPuncturedSpaceSphereHomologyEquiv (liftedSphereSpace.{u} 1) 2).trans
    (integralSingularHomologyHomotopyEquiv 2
      (liftedSphereHomeomorph.{u} 1).toHomotopyEquiv).symm
  refine ⟨euclideanSimplexBoundaryDegree.comp e.symm.toLinearMap, ?_⟩
  change euclideanSimplexBoundaryDegree (e.symm (e euclideanStandardSimplexBoundaryClass.{u})) = 1
  rw [LinearEquiv.symm_apply_apply]
  exact euclideanSimplexBoundaryDegree_euclideanStandardSimplexBoundaryClass

end DifferentialGeometry.Topology.SimplexDegree
