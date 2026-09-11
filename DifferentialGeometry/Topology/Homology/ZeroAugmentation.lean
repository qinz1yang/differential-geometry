import DifferentialGeometry.Topology.Homology.TotallyDisconnectedZero
import DifferentialGeometry.Topology.Homology.ConnectedZeroHomology
import Mathlib.LinearAlgebra.Finsupp.Pi



noncomputable section

open CategoryTheory ContinuousMap

universe u

namespace DifferentialGeometry.Topology


def integralPointZeroEquiv :
    integralSingularHomology 0 PUnit.{u + 1} ≃ₗ[ℤ] ℤ :=
  integralTotallyDisconnectedZeroEquiv.trans (Finsupp.uniqueLinearEquiv ℤ ℤ PUnit.unit)

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]


def integralZeroAugmentation : integralSingularHomology 0 X →ₗ[ℤ] ℤ :=
  integralPointZeroEquiv.toLinearMap.comp
    (integralSingularHomologyMap 0 (ContinuousMap.const X PUnit.unit))


theorem integralZeroAugmentation_vertex (x : X) :
    integralZeroAugmentation (integralZeroChainClass (integralVertexChain x)) = 1 := by
  change integralPointZeroEquiv (integralSingularHomologyMap 0 (.const X PUnit.unit)
    (integralZeroChainClass (integralVertexChain x))) = _
  rw [integralZeroChainClass_map, integralVertexChain_map]
  change Finsupp.uniqueLinearEquiv ℤ ℤ PUnit.unit
    (integralTotallyDisconnectedZeroEquiv (integralZeroChainClass
      (integralVertexChain PUnit.unit))) = _
  rw [integralTotallyDisconnectedZeroEquiv_vertex]
  simp [Finsupp.uniqueLinearEquiv]


theorem integralZeroAugmentation_natural (f : C(X, Y)) :
    integralZeroAugmentation.comp (integralSingularHomologyMap 0 f) =
      integralZeroAugmentation := by
  unfold integralZeroAugmentation
  rw [LinearMap.comp_assoc, ← integralSingularHomologyMap_comp]
  rfl



def integralConnectedZeroAugmentationEquiv [PathConnectedSpace X] :
    integralSingularHomology 0 X ≃ₗ[ℤ] ℤ :=
  (integralSingularHomologyZeroMapEquiv (ContinuousMap.const X PUnit.unit)).trans
    integralPointZeroEquiv


theorem integralConnectedZeroAugmentationEquiv_toLinearMap [PathConnectedSpace X] :
    (integralConnectedZeroAugmentationEquiv (X := X)).toLinearMap = integralZeroAugmentation := rfl

end DifferentialGeometry.Topology
