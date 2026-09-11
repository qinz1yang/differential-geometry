import DifferentialGeometry.Topology.Homology.SingularSubdivisionBoundary
import DifferentialGeometry.Topology.Homology.UniversalHomotopyBoundary



noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]


theorem integralSingularSubdivisionHomotopy_boundary_simplex (n : ℕ)
    (σ : integralSingularSimplex (n + 1) X) :
    (integralSingularChains X).d (n + 2) (n + 1)
      (integralSingularSubdivisionHomotopy (n + 1) (integralSimplexChain (n + 1) σ)) =
        integralSimplexChain (n + 1) σ - integralSingularSubdivision (n + 1) (integralSimplexChain (n + 1) σ) -
          integralSingularSubdivisionHomotopy n ((integralSingularChains X).d (n + 1) n
            (integralSimplexChain (n + 1) σ)) := by
  rw [integralSingularSubdivisionHomotopy_simplex, ← singularSimplexChainPush_boundary,
    universalSimplexHomotopy_boundary]
  simp only [map_sub, map_sum, map_zsmul]
  rw [singularSimplexChainPush_identity, integralSingularSubdivision_simplex,
    integralSimplexChain_boundary, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  rw [singularSimplexChainPush_face, map_zsmul, integralSingularSubdivisionHomotopy_simplex]



theorem integralSingularSubdivisionHomotopy_boundary (n : ℕ) :
    ((integralSingularChains X).d (n + 2) (n + 1)).hom.comp (integralSingularSubdivisionHomotopy (n + 1)) =
      LinearMap.id - integralSingularSubdivision (n + 1) -
        (integralSingularSubdivisionHomotopy n).comp ((integralSingularChains X).d (n + 1) n).hom := by
  apply (integralSingularChainBasis (n + 1) X).ext
  intro σ
  rw [integralSingularChainBasis_apply]
  exact integralSingularSubdivisionHomotopy_boundary_simplex n σ



theorem integralSingularSubdivisionHomotopy_cycle (n : ℕ)
    (c : (integralSingularChains X).X (n + 1)) (hc : (integralSingularChains X).d (n + 1) n c = 0) :
    (integralSingularChains X).d (n + 2) (n + 1) (integralSingularSubdivisionHomotopy (n + 1) c) =
      c - integralSingularSubdivision (n + 1) c := by
  have h := LinearMap.congr_fun (integralSingularSubdivisionHomotopy_boundary n) c
  simpa only [LinearMap.comp_apply, LinearMap.sub_apply, LinearMap.id_apply, hc, map_zero, sub_zero] using h

end DifferentialGeometry.Topology
