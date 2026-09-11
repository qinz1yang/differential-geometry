import DifferentialGeometry.Topology.Homology.SimplexEvaluation
import DifferentialGeometry.Topology.Homology.SubdivisionHomotopyNaturality



noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module

universe u

namespace DifferentialGeometry.Topology



def universalSimplexSubdivision (n : ℕ) : integralSingularChainsIn n (liftedSimplexBody.{u} n) :=
  ⟨affineSingularSubdivision n (affineSingularChain n (liftedSimplexVertex n)),
    affineSingularChainsIn_le n (convex_liftedSimplexBody n)
      (affineSingularSubdivision_mem n (convex_liftedSimplexBody n) (liftedSimplexChain_mem n))⟩


def universalSimplexHomotopy (n : ℕ) : integralSingularChainsIn (n + 1) (liftedSimplexBody.{u} n) :=
  ⟨affineSubdivisionHomotopy n (affineSingularChain n (liftedSimplexVertex n)),
    affineSingularChainsIn_le (n + 1) (convex_liftedSimplexBody n)
      (affineSubdivisionHomotopy_mem n (convex_liftedSimplexBody n) (liftedSimplexChain_mem n))⟩

variable {X : Type u} [TopologicalSpace X]



def integralSingularSubdivision (n : ℕ) :
    (integralSingularChains X).X n →ₗ[ℤ] (integralSingularChains X).X n :=
  (integralSingularChainBasis n X).constr (M' := (integralSingularChains X).X n) ℕ
    (fun σ => singularSimplexChainPush n n σ (universalSimplexSubdivision n))


theorem integralSingularSubdivision_simplex (n : ℕ) (σ : integralSingularSimplex n X) :
    integralSingularSubdivision n (integralSimplexChain n σ) =
      singularSimplexChainPush n n σ (universalSimplexSubdivision n) := by
  rw [← integralSingularChainBasis_apply]
  exact (integralSingularChainBasis n X).constr_basis ℕ _ σ


def integralSingularSubdivisionHomotopy (n : ℕ) :
    (integralSingularChains X).X n →ₗ[ℤ] (integralSingularChains X).X (n + 1) :=
  (integralSingularChainBasis n X).constr (M' := (integralSingularChains X).X (n + 1)) ℕ
    (fun σ => singularSimplexChainPush n (n + 1) σ (universalSimplexHomotopy n))


theorem integralSingularSubdivisionHomotopy_simplex (n : ℕ) (σ : integralSingularSimplex n X) :
    integralSingularSubdivisionHomotopy n (integralSimplexChain n σ) =
      singularSimplexChainPush n (n + 1) σ (universalSimplexHomotopy n) := by
  rw [← integralSingularChainBasis_apply]
  exact (integralSingularChainBasis n X).constr_basis ℕ _ σ


theorem integralSingularSubdivision_zero :
    integralSingularSubdivision (X := X) 0 = LinearMap.id := by
  apply (integralSingularChainBasis 0 X).ext
  intro σ
  rw [integralSingularChainBasis_apply, integralSingularSubdivision_simplex]
  exact singularSimplexChainPush_identity 0 σ


theorem integralSingularSubdivisionHomotopy_zero :
    integralSingularSubdivisionHomotopy (X := X) 0 = 0 := by
  apply (integralSingularChainBasis 0 X).ext
  intro σ
  rw [integralSingularChainBasis_apply, integralSingularSubdivisionHomotopy_simplex]
  exact (singularSimplexChainPush 0 1 σ).map_zero

end DifferentialGeometry.Topology
