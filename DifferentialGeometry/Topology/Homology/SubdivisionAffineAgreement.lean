import DifferentialGeometry.Topology.Homology.SubdivisionCarriers
import DifferentialGeometry.Topology.Homology.MeshIteration



noncomputable section

open CategoryTheory AlgebraicTopology ContinuousMap Set Module

universe u

namespace DifferentialGeometry.Topology

variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E]



def liftedAffineSimplexLinearMap (n : ℕ) (v : Fin (n + 1) → E) :
    liftedSimplexSpace.{u} n →L[ℝ] E where
  toFun x := ∑ i, x.down i • v i
  map_add' x y := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' a x := by simp [Finset.smul_sum, smul_smul]
  cont := continuous_finsetSum _ (fun i _ =>
    ((continuous_apply i).comp Homeomorph.ulift.continuous).smul continuous_const)


theorem liftedAffineSimplexLinearMap_vertex (n : ℕ) (v : Fin (n + 1) → E) (i : Fin (n + 1)) :
    liftedAffineSimplexLinearMap n v (liftedSimplexVertex n i) = v i := by
  change ∑ j, (Pi.single i (1 : ℝ) : Fin (n + 1) → ℝ) j • v j = v i
  simp [Pi.single_apply]



theorem singularSimplexEvaluation_affine (n : ℕ) (v : Fin (n + 1) → E) :
    singularSimplexEvaluation n (affineSingularSimplex n v) =
      (⟨liftedAffineSimplexLinearMap n v, (liftedAffineSimplexLinearMap n v).continuous⟩ :
        C(liftedSimplexSpace n, E)).comp (singularSubspaceInclusion (liftedSimplexBody n)) := by
  unfold singularSimplexEvaluation affineSingularSimplex
  rw [Equiv.apply_symm_apply]
  rfl



theorem singularSimplexChainPush_affine (n k : ℕ) (v : Fin (n + 1) → E)
    (c : integralSingularChainsIn k (liftedSimplexBody.{u} n)) :
    singularSimplexChainPush n k (affineSingularSimplex n v) c =
      (integralSingularChainMap ⟨liftedAffineSimplexLinearMap n v,
        (liftedAffineSimplexLinearMap n v).continuous⟩).f k c.val := by
  unfold singularSimplexChainPush
  rw [singularSimplexEvaluation_affine, integralSingularChainMap_comp]
  change (integralSingularChainMap _).f k
    ((integralSingularChainMap (singularSubspaceInclusion (liftedSimplexBody n))).f k
      (integralSingularChainRestriction k (liftedSimplexBody n) c)) = _
  rw [integralSingularChainRestriction_inclusion]



theorem integralSingularSubdivision_affine_simplex (n : ℕ) (v : Fin (n + 1) → E) :
    integralSingularSubdivision n (affineSingularChain n v) =
      affineSingularSubdivision n (affineSingularChain n v) := by
  change integralSingularSubdivision n (integralSimplexChain n (affineSingularSimplex n v)) = _
  rw [integralSingularSubdivision_simplex, singularSimplexChainPush_affine]
  change (integralSingularChainMap _).f n
    (affineSingularSubdivision n (affineSingularChain n (liftedSimplexVertex n))) = _
  rw [affineSingularSubdivision_linear n _ (convex_liftedSimplexBody n) (liftedSimplexChain_mem n),
    affineSingularChain_linear]
  have hv : liftedAffineSimplexLinearMap n v ∘ liftedSimplexVertex n = v :=
    funext (liftedAffineSimplexLinearMap_vertex n v)
  rw [hv]


theorem integralSingularSubdivision_affine (n : ℕ) (A : Set E)
    {c : (integralSingularChains E).X n} (hc : c ∈ affineSingularChainsIn n A) :
    integralSingularSubdivision n c = affineSingularSubdivision n c := by
  have h : affineSingularChainsIn n A ≤
      LinearMap.ker (integralSingularSubdivision n - affineSingularSubdivision n) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v, _, rfl⟩
    exact sub_eq_zero.mpr (integralSingularSubdivision_affine_simplex n v)
  exact sub_eq_zero.mp (h hc)

end DifferentialGeometry.Topology
