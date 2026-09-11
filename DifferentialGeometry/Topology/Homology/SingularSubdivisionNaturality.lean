import DifferentialGeometry.Topology.Homology.SingularSubdivisionHomotopy



noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module

universe u

namespace DifferentialGeometry.Topology

variable {X Y : Type u} [TopologicalSpace X] [TopologicalSpace Y]


theorem singularSimplexEvaluation_map (n : ℕ) (f : C(X, Y))
    (σ : integralSingularSimplex n X) :
    singularSimplexEvaluation n (integralSingularSimplexMap n f σ) =
      f.comp (singularSimplexEvaluation n σ) := by
  unfold singularSimplexEvaluation
  rw [integralSingularSimplexMap_apply]
  rfl


theorem singularSimplexChainPush_map (n k : ℕ) (f : C(X, Y))
    (σ : integralSingularSimplex n X)
    (c : integralSingularChainsIn k (liftedSimplexBody.{u} n)) :
    singularSimplexChainPush n k (integralSingularSimplexMap n f σ) c =
      (integralSingularChainMap f).f k (singularSimplexChainPush n k σ c) := by
  unfold singularSimplexChainPush
  rw [singularSimplexEvaluation_map, integralSingularChainMap_comp]
  rfl


theorem integralSingularSubdivision_map (n : ℕ) (f : C(X, Y))
    (c : (integralSingularChains X).X n) :
    integralSingularSubdivision n ((integralSingularChainMap f).f n c) =
      (integralSingularChainMap f).f n (integralSingularSubdivision n c) := by
  have h : (integralSingularSubdivision n).comp ((integralSingularChainMap f).f n).hom =
      ((integralSingularChainMap f).f n).hom.comp (integralSingularSubdivision n) := by
    apply (integralSingularChainBasis n X).ext
    intro σ
    rw [integralSingularChainBasis_apply]
    simp only [LinearMap.comp_apply]
    change integralSingularSubdivision n ((integralSingularChainMap f).f n (integralSimplexChain n σ)) = _
    rw [integralSimplexChain_map, integralSingularSubdivision_simplex,
      singularSimplexChainPush_map, integralSingularSubdivision_simplex]
  exact LinearMap.congr_fun h c


theorem integralSingularSubdivisionHomotopy_map (n : ℕ) (f : C(X, Y))
    (c : (integralSingularChains X).X n) :
    integralSingularSubdivisionHomotopy n ((integralSingularChainMap f).f n c) =
      (integralSingularChainMap f).f (n + 1) (integralSingularSubdivisionHomotopy n c) := by
  have h : (integralSingularSubdivisionHomotopy n).comp ((integralSingularChainMap f).f n).hom =
      ((integralSingularChainMap f).f (n + 1)).hom.comp (integralSingularSubdivisionHomotopy n) := by
    apply (integralSingularChainBasis n X).ext
    intro σ
    rw [integralSingularChainBasis_apply]
    simp only [LinearMap.comp_apply]
    change integralSingularSubdivisionHomotopy n
      ((integralSingularChainMap f).f n (integralSimplexChain n σ)) = _
    rw [integralSimplexChain_map, integralSingularSubdivisionHomotopy_simplex,
      singularSimplexChainPush_map, integralSingularSubdivisionHomotopy_simplex]
  exact LinearMap.congr_fun h c

end DifferentialGeometry.Topology
