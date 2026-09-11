import DifferentialGeometry.Topology.Homology.ZeroChainClasses
import DifferentialGeometry.Topology.Homology.SimplexMaps



noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology ContinuousMap Module

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]


theorem integralSimplexChain_zero_vertex (σ : integralSingularSimplex 0 X) :
    integralSimplexChain 0 σ = integralVertexChain (TopCat.toSSetObj₀Equiv σ) := by
  unfold integralVertexChain
  rw [Equiv.symm_apply_apply]


theorem integralVertexChain_map (f : C(X, Y)) (x : X) :
    (integralSingularChainMap f).f 0 (integralVertexChain x) = integralVertexChain (f x) := by
  unfold integralVertexChain
  rw [integralSimplexChain_map]
  rfl



theorem integralZeroVertexClass_eq_of_joined {x y : X} (h : Joined x y) :
    integralZeroChainClass (integralVertexChain x) = integralZeroChainClass (integralVertexChain y) := by
  obtain ⟨p⟩ := h
  exact ((integralZeroChainClass_eq_iff (integralVertexChain y) (integralVertexChain x)).mpr
    ⟨integralPathChain p, integralPathChain_boundary p⟩).symm




theorem integralSingularHomologyMap_zero_eq_of_joined (f g : C(X, Y))
    (h : ∀ x, Joined (f x) (g x)) : integralSingularHomologyMap 0 f = integralSingularHomologyMap 0 g := by
  have he : (integralSingularHomologyMap 0 f).comp integralZeroChainClass =
      (integralSingularHomologyMap 0 g).comp integralZeroChainClass := by
    apply (integralSingularChainBasis 0 X).ext
    intro σ
    simp only [LinearMap.comp_apply, integralSingularChainBasis_apply]
    rw [integralSimplexChain_zero_vertex, integralZeroChainClass_map, integralZeroChainClass_map,
      integralVertexChain_map, integralVertexChain_map]
    exact integralZeroVertexClass_eq_of_joined (h _)
  apply LinearMap.ext
  intro a
  obtain ⟨c, rfl⟩ := integralZeroChainClass_surjective a
  exact LinearMap.congr_fun he c

end DifferentialGeometry.Topology
