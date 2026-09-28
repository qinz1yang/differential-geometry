/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DiskBoundaryCollar
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubcomplexBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.MoiseChain

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPLAnnulusWithEnds.exists_disk_union {A G J D : Set E3}
    (hA : IsPLAnnulusWithEnds A G J) {r : (Fin 3 → ℝ) → E3}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hboundary : r '' stdSimplexBoundary 2 = G) (hAD : A ∩ D = G) :
    ∃ q : (Fin 3 → ℝ) → E3, IsPLHomeomorphOn q (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) (D ∪ A) ∧
      q '' stdSimplexBoundary 2 = J ∧ Disjoint D J := by
  obtain ⟨Q, f, hQ, hf, hG, hJ⟩ := hA
  let g : E3 → E3 := fun x => f (x, 0)
  have hg : IsPLHomeomorphOn g Q G := by
    rw [hG]
    exact (hQ.isPolyhedron.isPLHomeomorphOn_prod_const 0).trans
      (hf.restrict (hQ.isPolyhedron.prod (isHPolytope_singleton (0 : ℝ)).isPolyhedron)
        (fun z hz => ⟨hz.1, hz.2.symm ▸ ⟨le_rfl, zero_le_one⟩⟩))
  let σ := f ∘ Prod.map (Function.invFunOn g Q) (id : ℝ → ℝ)
  have hσ : IsPLHomeomorphOn σ (G ×ˢ Icc (0 : ℝ) 1) A :=
    (hg.symm.prodMap isHPolytope_Icc.isPolyhedron.isPLHomeomorphOn_id).trans hf
  have hσ0 : ∀ x ∈ G, σ (x, 0) = x := by
    intro x hx
    exact hg.bijOn.invOn_invFunOn.2 hx
  have hσ1 : σ '' (G ×ˢ {(1 : ℝ)}) = J := by
    rw [hJ]
    refine Subset.antisymm ?_ ?_
    · rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      exact ⟨(Function.invFunOn g Q x, t),
        ⟨hg.bijOn.surjOn.mapsTo_invFunOn hx, ht⟩, rfl⟩
    · rintro _ ⟨⟨x, t⟩, ⟨hx, ht⟩, rfl⟩
      refine ⟨(g x, t), ⟨hg.bijOn.mapsTo hx, ht⟩, ?_⟩
      change f (Function.invFunOn g Q (g x), t) = f (x, t)
      rw [hg.bijOn.invOn_invFunOn.1 hx]
  obtain ⟨q, hq, hqb, hqD⟩ := hr.exists_isPLHomeomorphOn_union_collar zero_lt_one
    (by rwa [hboundary]) (by rwa [hboundary]) (hAD.trans hboundary.symm)
  have hqb' : q '' stdSimplexBoundary 2 = J := by
    rw [hqb, hboundary, hσ1]
  exact ⟨q, hq, hqb', hqb' ▸ hqD⟩

theorem IsPLAnnulusWithEnds.disk_union_mem_nhdsSetWithin {A G J D P : Set E3}
    (hA : IsPLAnnulusWithEnds A G J) {r : (Fin 3 → ℝ) → E3}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) D)
    (hboundary : r '' stdSimplexBoundary 2 = G) (hAD : A ∩ D = G)
    (hP : IsPLBall 2 P) (hsub : D ∪ A ⊆ P) : D ∪ A ∈ 𝓝ˢ[P] D := by
  classical
  let _ : DecidableEq E3 := fun a b => Classical.propDecidable (a = b)
  obtain ⟨q, hq, hqb, hDJ⟩ := hA.exists_disk_union hr hboundary hAD
  have hDA : IsPLBall 2 (D ∪ A) := ⟨q, hq⟩
  obtain ⟨K, hKfin, hKP⟩ := hP.isPolyhedron.exists_simplicialComplex
  obtain ⟨L, hLfin, hLspace⟩ := hDA.isPolyhedron.exists_simplicialComplex
  let _ : Finite K.faces := hKfin.to_subtype
  let _ : Finite L.faces := hLfin.to_subtype
  have hK : IsPLBall 2 K.space := hKP.symm ▸ hP
  have hL : IsPLBall 2 L.space := hLspace.symm ▸ hDA
  have hLbd : (boundaryComplex 2 L).space = J := by
    rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex L (hLspace.symm ▸ hq),
      simplexBoundary_stdVertices_space, hqb]
  have hinter : (D ∪ A) ∩ closure (P \ (D ∪ A)) ⊆ J := by
    have hLK : L.space ⊆ K.space := hLspace.subset.trans (hsub.trans hKP.symm.subset)
    have h := inter_closure_sdiff_subset_boundaryComplex (n := 1) K L
      hK.isCombinatorialManifoldWithBoundary hL.isCombinatorialManifoldWithBoundary hLK
    intro x hx
    have hxL : x ∈ L.space := hLspace.symm ▸ hx.1
    have hxcl : x ∈ closure (K.space \ L.space) := by
      rw [hKP, hLspace]
      exact hx.2
    exact hLbd ▸ h ⟨hxL, hxcl⟩
  refine mem_nhdsSetWithin.mpr
    ⟨(closure (P \ (D ∪ A)))ᶜ, isClosed_closure.isOpen_compl, ?_, ?_⟩
  · intro x hxD hxcl
    exact disjoint_left.mp hDJ hxD (hinter ⟨Or.inl hxD, hxcl⟩)
  · rintro x ⟨hxcl, hxP⟩
    by_contra hxDA
    exact hxcl (subset_closure ⟨hxP, hxDA⟩)

end DifferentialGeometry.Topology.PiecewiseLinear
