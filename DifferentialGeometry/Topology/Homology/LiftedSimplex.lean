import DifferentialGeometry.Topology.Homology.AffineNaturality
import Mathlib.Analysis.Normed.Operator.LinearIsometry



noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module

universe u

namespace DifferentialGeometry.Topology


abbrev liftedSimplexSpace (n : ℕ) := ULift.{u} (Fin (n + 1) → ℝ)


def liftedSimplexBody (n : ℕ) : Set (liftedSimplexSpace.{u} n) :=
  {x | x.down ∈ stdSimplex ℝ (Fin (n + 1))}


def liftedSimplexVertex (n : ℕ) (i : Fin (n + 1)) : liftedSimplexSpace.{u} n :=
  ULift.up (Pi.single i 1)


theorem convex_liftedSimplexBody (n : ℕ) : Convex ℝ (liftedSimplexBody.{u} n) :=
  (convex_stdSimplex ℝ (Fin (n + 1))).linear_preimage
    (ULift.moduleEquiv : liftedSimplexSpace.{u} n ≃ₗ[ℝ] (Fin (n + 1) → ℝ)).toLinearMap


theorem liftedSimplexVertex_mem (n : ℕ) (i : Fin (n + 1)) :
    liftedSimplexVertex.{u} n i ∈ liftedSimplexBody n := single_mem_stdSimplex ℝ i



def liftedSimplexHomeomorph (n : ℕ) :
    stdSimplex ℝ (Fin (n + 1)) ≃ₜ liftedSimplexBody.{u} n where
  toFun t := ⟨ULift.up t.val, t.property⟩
  invFun t := ⟨t.val.down, t.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := ((Homeomorph.ulift.symm.continuous).comp continuous_subtype_val).subtype_mk _
  continuous_invFun := ((Homeomorph.ulift.continuous).comp continuous_subtype_val).subtype_mk _



theorem affineSimplexMap_liftedSimplexVertex (n : ℕ) (t : stdSimplex ℝ (Fin (n + 1))) :
    affineSimplexMap (liftedSimplexVertex.{u} n) t = ULift.up t.val := by
  apply (ULift.moduleEquiv : liftedSimplexSpace.{u} n ≃ₗ[ℝ] (Fin (n + 1) → ℝ)).injective
  change (ULift.moduleEquiv : liftedSimplexSpace.{u} n ≃ₗ[ℝ] (Fin (n + 1) → ℝ))
    (∑ i, t.val i • liftedSimplexVertex n i) = t.val
  rw [map_sum]
  simp only [map_smul]
  funext j
  simp [Finset.sum_apply, liftedSimplexVertex, Pi.single_apply]


theorem liftedSimplexChain_mem (n : ℕ) :
    affineSingularChain n (liftedSimplexVertex.{u} n) ∈ affineSingularChainsIn n (liftedSimplexBody n) :=
  affineSingularChain_mem n _ _ (liftedSimplexVertex_mem n)

end DifferentialGeometry.Topology
