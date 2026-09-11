import DifferentialGeometry.Topology.Homology.ContractiblePairOne



noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Set Module

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]


instance integralRelativeZeroKernel_module (A : Set X) :
    Module ℤ (LinearMap.ker (integralSingularHomologyMap 0 (singularSubspaceInclusion A))) :=
  (LinearMap.ker (integralSingularHomologyMap 0 (singularSubspaceInclusion A))).module



def integralRelativeConnectingZeroKernelEquiv [ContractibleSpace X] (A : Set X) :
    integralRelativeHomology 1 A ≃ₗ[ℤ]
      LinearMap.ker (integralSingularHomologyMap 0 (singularSubspaceInclusion A)) :=
  (LinearEquiv.ofInjective (integralRelativeConnecting 0 A)
    (integralRelativeConnecting_zero_injective A)).trans
      (LinearEquiv.ofEq _ _ ((LinearMap.exact_iff.mp (integralRelative_exact_subspace 0 A)).symm))




def integralHomologyOneContractibleCoverEquiv [PathConnectedSpace X] (A B : Set X)
    [ContractibleSpace A] [ContractibleSpace B]
    (hA : IsOpen A) (hB : IsOpen B) (hcover : A ∪ B = univ) :
    integralSingularHomology 1 X ≃ₗ[ℤ]
      LinearMap.ker (integralSingularHomologyMap 0 (singularSubspaceInclusion (subspaceIntersection A B))) :=
  ((integralAbsoluteToRelativeOneIsoOfContractible A).toLinearEquiv.trans
    (integralRelativeOpenExcisionIso 1 A B hA hB hcover).symm.toLinearEquiv).trans
      (integralRelativeConnectingZeroKernelEquiv (subspaceIntersection A B))

end DifferentialGeometry.Topology
