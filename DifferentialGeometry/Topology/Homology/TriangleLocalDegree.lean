import DifferentialGeometry.Topology.Homology.TriangleBoundaryDegree
import DifferentialGeometry.Topology.Homology.SquareBoundaryDegree

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Module
open scoped Simplicial Topology

namespace DifferentialGeometry.Topology.SimplexDegree

universe u

private theorem standardTriangleBoundaryChain_inclusion_hom :
    integralChainHom 1 standardTriangleBoundaryChain.{u} ≫
      (integralSingularChainMap (singularSubspaceInclusion puncturedPlane.{u})).f 1 =
        integralChainHom 2 standardTriangleChain.{u} ≫
          (integralSingularChains (liftedSphereSpace.{u} 0)).d 2 1 := by
  rw [integralChainHom_comp_map, standardTriangleBoundaryChain_inclusion, integralChainHom_d]

def standardTriangleRelativeChain :
    integralSingularCoefficients ⟶ (integralRelativeChains puncturedPlane.{u}).X 2 :=
  integralChainHom 2 standardTriangleChain ≫ (integralRelativeProjection puncturedPlane).f 2

theorem standardTriangleRelativeChain_boundary :
    standardTriangleRelativeChain.{u} ≫ (integralRelativeChains puncturedPlane).d 2 1 = 0 :=
  integralRelativeChain_projection_boundary 0 puncturedPlane
    (integralChainHom 2 standardTriangleChain) (integralChainHom 1 standardTriangleBoundaryChain)
    standardTriangleBoundaryChain_inclusion_hom

def standardTriangleLocalClass : integralLocalHomology 2 (0 : liftedSphereSpace.{u} 0) :=
  integralRelativeClassOf 1 puncturedPlane standardTriangleRelativeChain
    standardTriangleRelativeChain_boundary

theorem integralRelativeConnecting_standardTriangleLocalClass :
    integralRelativeConnecting 1 puncturedPlane standardTriangleLocalClass.{u} =
      standardTriangleBoundaryClass :=
  integralRelativeConnecting_liftCycles_apply 0 puncturedPlane
    (integralChainHom 2 standardTriangleChain) standardTriangleRelativeChain_boundary
    (integralChainHom 1 standardTriangleBoundaryChain)
    (by rw [integralChainHom_d 0 standardTriangleBoundaryChain,
      standardTriangleBoundaryChain_boundary, integralChainHom_zero])
    standardTriangleBoundaryChain_inclusion_hom

def standardTriangleLocalDegree :
    integralLocalHomology 2 (0 : liftedSphereSpace.{u} 0) →ₗ[ℤ] ℤ :=
  puncturedPlaneDiagonalDegree.comp (integralRelativeConnecting 1 puncturedPlane)

theorem standardTriangleLocalDegree_standardTriangleLocalClass :
    standardTriangleLocalDegree standardTriangleLocalClass.{u} = 1 := by
  rw [standardTriangleLocalDegree, LinearMap.comp_apply,
    integralRelativeConnecting_standardTriangleLocalClass,
    puncturedPlaneDiagonalDegree_standardTriangleBoundaryClass]

end DifferentialGeometry.Topology.SimplexDegree
