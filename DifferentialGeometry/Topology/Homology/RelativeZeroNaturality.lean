import DifferentialGeometry.Topology.Homology.RelativeZero

noncomputable section

open CategoryTheory ContinuousMap Module Set

universe u

namespace DifferentialGeometry.Topology

theorem integralAbsoluteToRelative_zero_vertex_of_mem
    {X : Type u} [TopologicalSpace X] (A : Set X) (x : X) (hx : x ∈ A) :
    integralAbsoluteToRelative 0 A (integralZeroChainClass (integralVertexChain x)) = 0 := by
  have h := (integralRelative_exact_absolute 0 A).apply_apply_eq_zero
    (integralZeroChainClass (integralVertexChain (⟨x, hx⟩ : A)))
  rw [integralZeroChainClass_map, integralVertexChain_map] at h
  exact h

theorem integralRelativeHomologyMap_zero_vertex
    {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]
    (f : C(X, Y)) {A : Set X} {B : Set Y} (hf : MapsTo f A B) (x : X) :
    integralRelativeHomologyMap 0 f hf
      (integralAbsoluteToRelative 0 A (integralZeroChainClass (integralVertexChain x))) =
    integralAbsoluteToRelative 0 B (integralZeroChainClass (integralVertexChain (f x))) := by
  have h := LinearMap.congr_fun (integralAbsoluteToRelative_natural 0 f hf)
    (integralZeroChainClass (integralVertexChain x))
  change integralAbsoluteToRelative 0 B
      (integralSingularHomologyMap 0 f (integralZeroChainClass (integralVertexChain x))) =
    integralRelativeHomologyMap 0 f hf
      (integralAbsoluteToRelative 0 A (integralZeroChainClass (integralVertexChain x))) at h
  rw [integralZeroChainClass_map, integralVertexChain_map] at h
  exact h.symm

end DifferentialGeometry.Topology
