import DifferentialGeometry.Topology.Homology.SimplexEvaluation
import DifferentialGeometry.Topology.Homology.LiftedFaces



noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module

universe u

namespace DifferentialGeometry.Topology

variable {X : Type u} [TopologicalSpace X]



theorem singularSimplexEvaluation_face (n : ℕ) (σ : integralSingularSimplex (n + 1) X)
    (i : Fin (n + 2)) :
    singularSimplexEvaluation n ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) =
      (singularSimplexEvaluation (n + 1) σ).comp (liftedSimplexBodyMap n (n + 1) i.succAbove) := by
  apply ContinuousMap.ext
  intro z
  rfl



theorem singularSimplexChainPush_face (n k : ℕ) (σ : integralSingularSimplex (n + 1) X)
    (i : Fin (n + 2)) (c : integralSingularChainsIn k (liftedSimplexBody.{u} n)) :
    singularSimplexChainPush (n + 1) k σ
      (singularCarrierMap k ⟨liftedSimplexLinearMap n (n + 1) i.succAbove,
        (liftedSimplexLinearMap n (n + 1) i.succAbove).continuous⟩
          (liftedSimplexLinearMap_body n (n + 1) i.succAbove) c) =
      singularSimplexChainPush n k ((TopCat.toSSet.obj (TopCat.of X)).δ i σ) c := by
  unfold singularSimplexChainPush
  rw [LinearMap.comp_apply, integralSingularChainRestriction_map, LinearMap.comp_apply]
  have hmap : integralSingularChainMap
      (singularSimplexEvaluation n ((TopCat.toSSet.obj (TopCat.of X)).δ i σ)) =
        integralSingularChainMap (liftedSimplexBodyMap n (n + 1) i.succAbove) ≫
          integralSingularChainMap (singularSimplexEvaluation (n + 1) σ) := by
    rw [singularSimplexEvaluation_face, integralSingularChainMap_comp]
  exact (congrArg (fun h : integralSingularChains (liftedSimplexBody.{u} n) ⟶ integralSingularChains X =>
    h.f k (integralSingularChainRestriction k (liftedSimplexBody n) c)) hmap).symm

end DifferentialGeometry.Topology
