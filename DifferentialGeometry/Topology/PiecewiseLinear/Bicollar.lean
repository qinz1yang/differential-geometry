import DifferentialGeometry.Topology.PiecewiseLinear.TwoSidedNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.CollarRestriction
import DifferentialGeometry.Topology.PiecewiseLinear.BicollarGluing

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

end DifferentialGeometry.Topology.PiecewiseLinear
