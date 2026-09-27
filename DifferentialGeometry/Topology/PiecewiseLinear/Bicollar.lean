/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.TwoSidedNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.CollarRestriction
import DifferentialGeometry.Topology.PiecewiseLinear.BicollarGluing
import DifferentialGeometry.Topology.PiecewiseLinear.DisjointGluing
import Mathlib.Order.Filter.Finite

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_bicollar_of_isConnected
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : IsCombinatorialManifold 2 L)
    (hLK : L.space ⊆ K.space) (hBd : Disjoint L.space (boundaryComplex 3 K).space)
    (hconn : IsConnected L.space)
    (htwo : Topology.IsTwoSided (((↑) : K.space → E) ⁻¹' L.space))
    {U : Set E} (hU : U ∈ 𝓝ˢ[K.space] L.space) :
    ∃ (W : Set E) (ρ : E × ℝ → E), IsPolyhedron W ∧
      W ⊆ K.space \ (boundaryComplex 3 K).space ∧ W ⊆ U ∧
      W ∈ 𝓝ˢ[K.space] L.space ∧ IsPLHomeomorphOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1) W ∧
      ∀ x ∈ L.space, ρ (x, 0) = x := by
  obtain ⟨N, A, B, hNfin, hAfin, hBfin, -, hA, hB, -, -, -, hNK, hNU, hNnhds,
    hBN, hcover, hmeet, hboundaryA, hboundaryB⟩ :=
    hK.exists_neighborhood_manifold_pair_of_twoSided hL hLK hBd hconn htwo hU
  let _ : Finite N.faces := hNfin.to_subtype
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite B.faces := hBfin.to_subtype
  let _ : Finite (boundaryComplex 3 N).faces := (boundaryComplex_faces_finite 3 N).to_subtype
  have hAN : A.space ⊆ N.space := subset_union_left.trans hcover.subset
  have hBN' : B.space ⊆ N.space := subset_union_right.trans hcover.subset
  have hSA : L.space ⊆ (boundaryComplex 3 A).space := subset_union_left.trans hboundaryA.symm.subset
  have hSB : L.space ⊆ (boundaryComplex 3 B).space := subset_union_left.trans hboundaryB.symm.subset
  have hcompl (P T : Set E) (hP : IsClosed P)
      (hT : T = L.space ∪ (P ∩ (boundaryComplex 3 N).space)) : IsClosed (T \ L.space) := by
    have heq : T \ L.space = P ∩ (boundaryComplex 3 N).space := by
      apply Subset.antisymm
      · rintro x ⟨hx, hxL⟩
        exact (hT.subset hx).resolve_left hxL
      · intro x hx
        exact ⟨hT.symm.subset (Or.inr hx), fun hxL => disjoint_left.mp hBN hxL hx.2⟩
    rw [heq]
    exact hP.inter (isPolyhedron_space (boundaryComplex 3 N)).isClosed
  obtain ⟨W₀, ρ₀, hW₀, hW₀A, hW₀nhds, hρ₀, h₀, htrace₀, -⟩ :=
    hA.exists_collar_of_boundary_subset A (isPolyhedron_space L) hSA
      (hcompl A.space _ (isPolyhedron_space A).isClosed hboundaryA)
  obtain ⟨W₁, ρ₁, hW₁, hW₁B, hW₁nhds, hρ₁, h₁, htrace₁, -⟩ :=
    hB.exists_collar_of_boundary_subset B (isPolyhedron_space L) hSB
      (hcompl B.space _ (isPolyhedron_space B).isClosed hboundaryB)
  have hWW : W₀ ∩ W₁ = L.space := by
    apply Subset.antisymm
    · intro x hx
      exact hmeet.subset ⟨hW₀A hx.1, hW₁B hx.2⟩
    · intro x hx
      exact ⟨(htrace₀.symm.subset hx).1, (htrace₁.symm.subset hx).1⟩
  obtain ⟨ρ, hρ, hbottom, -, -⟩ :=
    exists_isPLHomeomorphOn_prod_Icc_of_collars (isPolyhedron_space L) hρ₀ hρ₁ h₀ h₁ hWW
  have hWK : W₀ ∪ W₁ ⊆ K.space :=
    union_subset (hW₀A.trans (hAN.trans hNK)) (hW₁B.trans (hBN'.trans hNK))
  have hWint : W₀ ∪ W₁ ⊆ K.space \ (boundaryComplex 3 K).space := by
    intro x hx
    refine ⟨hWK hx, ?_⟩
    intro hxB
    rcases hx with hx | hx
    · have hxA := inter_boundaryComplex_space_subset_of_subset K A hK hA (hAN.trans hNK)
        ⟨hW₀A hx, hxB⟩
      exact disjoint_left.mp hBd (htrace₀.subset ⟨hx, hxA⟩) hxB
    · have hxB' := inter_boundaryComplex_space_subset_of_subset K B hK hB (hBN'.trans hNK)
        ⟨hW₁B hx, hxB⟩
      exact disjoint_left.mp hBd (htrace₁.subset ⟨hx, hxB'⟩) hxB
  have hWpoint : ∀ x ∈ L.space, W₀ ∪ W₁ ∈ 𝓝[K.space] x := by
    obtain ⟨O₀, hO₀, hLO₀, hO₀W₀⟩ := mem_nhdsSetWithin.mp hW₀nhds
    obtain ⟨O₁, hO₁, hLO₁, hO₁W₁⟩ := mem_nhdsSetWithin.mp hW₁nhds
    intro x hx
    have hW₀x : W₀ ∈ 𝓝[A.space] x := mem_nhdsWithin.mpr ⟨O₀, hO₀, hLO₀ hx, hO₀W₀⟩
    have hW₁x : W₁ ∈ 𝓝[B.space] x := mem_nhdsWithin.mpr ⟨O₁, hO₁, hLO₁ hx, hO₁W₁⟩
    have hWN : W₀ ∪ W₁ ∈ 𝓝[N.space] x := by
      rw [← hcover, nhdsWithin_union, Filter.mem_sup]
      exact ⟨Filter.mem_of_superset hW₀x subset_union_left,
        Filter.mem_of_superset hW₁x subset_union_right⟩
    have hle : 𝓝[K.space] x ≤ 𝓝[N.space] x :=
      le_inf nhdsWithin_le_nhds (Filter.le_principal_iff.mpr (hNnhds x hx))
    exact hle hWN
  have hWnhds : W₀ ∪ W₁ ∈ 𝓝ˢ[K.space] L.space := by
    have hpre : ((↑) : K.space → E) ⁻¹' (W₀ ∪ W₁) ∈
        𝓝ˢ (((↑) : K.space → E) ⁻¹' L.space) := mem_nhdsSet_iff_forall.mpr fun x hx =>
      preimage_coe_mem_nhds_subtype.mpr (hWpoint x hx)
    have h := mem_nhdsSet_subtype_iff_nhdsSetWithin.mp hpre
    rwa [Subtype.image_preimage_coe, Subtype.image_preimage_coe,
      inter_eq_right.mpr hWK, inter_eq_right.mpr hLK] at h
  exact ⟨W₀ ∪ W₁, ρ, hW₀.union hW₁, hWint,
    union_subset (hW₀A.trans (hAN.trans hNU)) (hW₁B.trans (hBN'.trans hNU)),
    hWnhds, hρ, hbottom⟩

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_bicollar
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : IsCombinatorialManifold 2 L)
    (hLK : L.space ⊆ K.space) (hBd : Disjoint L.space (boundaryComplex 3 K).space)
    (htwo : Topology.IsTwoSided (((↑) : K.space → E) ⁻¹' L.space))
    {U : Set E} (hU : U ∈ 𝓝ˢ[K.space] L.space) :
    ∃ (W : Set E) (ρ : E × ℝ → E), IsPolyhedron W ∧
      W ⊆ K.space \ (boundaryComplex 3 K).space ∧ W ⊆ U ∧
      W ∈ 𝓝ˢ[K.space] L.space ∧ IsPLHomeomorphOn ρ (L.space ×ˢ Icc (-1 : ℝ) 1) W ∧
      ∀ x ∈ L.space, ρ (x, 0) = x := by
  classical
  let I := ConnectedComponents L.space
  let R : I → Geometry.SimplicialComplex ℝ E := fun i => PiecewiseLinear.connectedComponentComplex L
      i
  let _ : Finite I := finite_connectedComponents_space L
  let _ (i : I) : Finite (R i).faces := (connectedComponentComplex_faces_finite L i).to_subtype
  have hcover : (⋃ i, (R i).space) = L.space := iUnion_connectedComponentComplex_space L
  have hsub (i : I) : (R i).space ⊆ L.space := (subset_iUnion (fun j => (R j).space) i).trans
      hcover.subset
  have hdis : Pairwise fun i j => Disjoint (R i).space (R j).space :=
    pairwise_disjoint_connectedComponentComplex_space L
  have htwoR (i : I) : Topology.IsTwoSided (((↑) : K.space → E) ⁻¹' (R i).space) := by
    obtain ⟨p, rfl⟩ := ConnectedComponents.surjective_coe i
    simpa only [R, PiecewiseLinear.connectedComponentComplex_mk,
        restrict_connectedComponentIn_space]
      using htwo.preimage_connectedComponentIn continuous_subtype_val (p : E)
  have hfilters : Pairwise fun i j : I => Disjoint (𝓝ˢ (R i).space) (𝓝ˢ (R j).space) :=
    fun i j hij => disjoint_nhdsSet_nhdsSet (isPolyhedron_space (R i)).isClosed
      (isPolyhedron_space (R j)).isClosed (hdis hij)
  obtain ⟨V, hV, hVdis⟩ := hfilters.exists_mem_filter_of_disjoint
  have hlocal (i : I) : ∃ (W : Set E) (ρ : E × ℝ → E), IsPolyhedron W ∧
      W ⊆ K.space \ (boundaryComplex 3 K).space ∧ W ⊆ U ∩ V i ∧
      W ∈ 𝓝ˢ[K.space] (R i).space ∧
      IsPLHomeomorphOn ρ ((R i).space ×ˢ Icc (-1 : ℝ) 1) W ∧
      ∀ x ∈ (R i).space, ρ (x, 0) = x := by
    have hVi : V i ∈ 𝓝ˢ[K.space] (R i).space := Filter.mem_inf_of_left (hV i)
    exact hK.exists_bicollar_of_isConnected (hL.connectedComponentComplex i) ((hsub i).trans hLK)
      (hBd.mono_left (hsub i)) (isConnected_connectedComponentComplex_space L i) (htwoR i)
      (Filter.inter_mem (nhdsSetWithin_mono_left (hsub i) hU) hVi)
  choose W ρ hW hWint hWsub hWnhds hρ hcenter using hlocal
  have hPdis : Pairwise fun i j => Disjoint ((R i).space ×ˢ Icc (-1 : ℝ) 1)
      ((R j).space ×ˢ Icc (-1 : ℝ) 1) := by
    intro i j hij
    exact disjoint_left.mpr fun _ hx hy => disjoint_left.mp (hdis hij) hx.1 hy.1
  have hWdis : Pairwise fun i j => Disjoint (W i) (W j) := fun i j hij =>
    (hVdis hij).mono ((hWsub i).trans inter_subset_right) ((hWsub j).trans inter_subset_right)
  obtain ⟨σ, hσ, hσeq⟩ := exists_isPLHomeomorphOn_iUnion_of_pairwise_disjoint
    (fun i => (isPolyhedron_space (R i)).prod isHPolytope_Icc.isPolyhedron) hρ hPdis hWdis
  have hprod : (⋃ i, (R i).space ×ˢ Icc (-1 : ℝ) 1) = L.space ×ˢ Icc (-1 : ℝ) 1 := by
    ext z
    constructor
    · intro hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp hz
      exact ⟨hsub i hi.1, hi.2⟩
    · intro hz
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm.subset hz.1)
      exact mem_iUnion.mpr ⟨i, hi, hz.2⟩
  rw [hprod] at hσ
  have hnhds : (⋃ i, W i) ∈ 𝓝ˢ[K.space] L.space := by
    choose O hO hRO hOW using fun i => mem_nhdsSetWithin.mp (hWnhds i)
    refine mem_nhdsSetWithin.mpr ⟨⋃ i, O i, isOpen_iUnion hO, ?_, ?_⟩
    · intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm.subset hx)
      exact mem_iUnion.mpr ⟨i, hRO i hi⟩
    · rintro x ⟨hxO, hxK⟩
      obtain ⟨i, hi⟩ := mem_iUnion.mp hxO
      exact mem_iUnion.mpr ⟨i, hOW i ⟨hi, hxK⟩⟩
  refine ⟨⋃ i, W i, σ, IsPolyhedron.iUnion hW, iUnion_subset hWint,
    iUnion_subset (fun i => (hWsub i).trans inter_subset_left), hnhds, hσ, ?_⟩
  intro x hx
  obtain ⟨i, hi⟩ := mem_iUnion.mp (hcover.symm.subset hx)
  exact (hσeq i ⟨hi, by norm_num, by norm_num⟩).trans (hcenter i x hi)
end DifferentialGeometry.Topology.PiecewiseLinear
