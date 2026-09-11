import DifferentialGeometry.Topology.Homology.SingularSubdivision
import DifferentialGeometry.Topology.Homology.SimplexPushFaces



noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module

universe u

namespace DifferentialGeometry.Topology



theorem universalSimplexSubdivision_face (n : ℕ) (i : Fin (n + 2)) :
    affineSingularSubdivision n
      (affineSingularChain n (liftedSimplexVertex.{u} (n + 1) ∘ i.succAbove)) =
      (singularCarrierMap n ⟨liftedSimplexLinearMap n (n + 1) i.succAbove,
        (liftedSimplexLinearMap n (n + 1) i.succAbove).continuous⟩
          (liftedSimplexLinearMap_body n (n + 1) i.succAbove) (universalSimplexSubdivision n)).val := by
  change _ = (integralSingularChainMap
    ⟨liftedSimplexLinearMap n (n + 1) i.succAbove, (liftedSimplexLinearMap n (n + 1) i.succAbove).continuous⟩).f n
      (affineSingularSubdivision n (affineSingularChain n (liftedSimplexVertex.{u} n)))
  rw [affineSingularSubdivision_linear n _ (convex_liftedSimplexBody n) (liftedSimplexChain_mem n),
    affineSingularChain_linear]
  have hv : liftedSimplexLinearMap.{u} n (n + 1) i.succAbove ∘ liftedSimplexVertex n =
      liftedSimplexVertex (n + 1) ∘ i.succAbove :=
    funext (liftedSimplexLinearMap_vertex n (n + 1) i.succAbove)
  rw [hv]


theorem universalSimplexHomotopy_face (n : ℕ) (i : Fin (n + 2)) :
    affineSubdivisionHomotopy n
      (affineSingularChain n (liftedSimplexVertex.{u} (n + 1) ∘ i.succAbove)) =
      (singularCarrierMap (n + 1) ⟨liftedSimplexLinearMap n (n + 1) i.succAbove,
        (liftedSimplexLinearMap n (n + 1) i.succAbove).continuous⟩
          (liftedSimplexLinearMap_body n (n + 1) i.succAbove) (universalSimplexHomotopy n)).val := by
  change _ = (integralSingularChainMap
    ⟨liftedSimplexLinearMap n (n + 1) i.succAbove, (liftedSimplexLinearMap n (n + 1) i.succAbove).continuous⟩).f (n + 1)
      (affineSubdivisionHomotopy n (affineSingularChain n (liftedSimplexVertex.{u} n)))
  rw [affineSubdivisionHomotopy_linear n _ (convex_liftedSimplexBody n) (liftedSimplexChain_mem n),
    affineSingularChain_linear]
  have hv : liftedSimplexLinearMap.{u} n (n + 1) i.succAbove ∘ liftedSimplexVertex n =
      liftedSimplexVertex (n + 1) ∘ i.succAbove :=
    funext (liftedSimplexLinearMap_vertex n (n + 1) i.succAbove)
  rw [hv]



theorem universalSimplexSubdivision_boundary (n : ℕ) :
    (⟨(integralSingularChains (liftedSimplexSpace.{u} (n + 1))).d (n + 1) n
        (universalSimplexSubdivision (n + 1)).val,
      integralSingularChainsIn_boundary n _ (universalSimplexSubdivision (n + 1)).property⟩ :
        integralSingularChainsIn n (liftedSimplexBody (n + 1))) =
      ∑ i : Fin (n + 2), (-1 : ℤ) ^ i.val •
        singularCarrierMap n ⟨liftedSimplexLinearMap n (n + 1) i.succAbove,
          (liftedSimplexLinearMap n (n + 1) i.succAbove).continuous⟩
            (liftedSimplexLinearMap_body n (n + 1) i.succAbove) (universalSimplexSubdivision n) := by
  apply Subtype.ext
  change (integralSingularChains (liftedSimplexSpace.{u} (n + 1))).d (n + 1) n
    (affineSingularSubdivision (n + 1) (affineSingularChain (n + 1) (liftedSimplexVertex (n + 1)))) =
      (integralSingularChainsIn n (liftedSimplexBody (n + 1))).subtype (∑ i : Fin (n + 2),
        (-1 : ℤ) ^ i.val • singularCarrierMap n
          ⟨liftedSimplexLinearMap n (n + 1) i.succAbove, (liftedSimplexLinearMap n (n + 1) i.succAbove).continuous⟩
            (liftedSimplexLinearMap_body n (n + 1) i.succAbove) (universalSimplexSubdivision n))
  rw [map_sum, affineSingularSubdivision_boundary n (convex_liftedSimplexBody (n + 1))
    (liftedSimplexChain_mem (n + 1)), affineSingularChain_boundary, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_zsmul, map_zsmul, universalSimplexSubdivision_face]
  rfl

end DifferentialGeometry.Topology
