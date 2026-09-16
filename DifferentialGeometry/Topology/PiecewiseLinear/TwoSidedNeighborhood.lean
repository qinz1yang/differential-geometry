import DifferentialGeometry.Topology.PiecewiseLinear.ConnectedNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexNhdsWithin
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceComponentClosure
import DifferentialGeometry.Topology.Connected.TwoSided

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem IsCombinatorialManifoldWithBoundary.exists_connected_neighborhood_sdiff_not_isPreconnected
    {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) {C U : Set E}
    (hC : IsCompact C) (hconn : IsConnected C) (hCK : C ⊆ K.space)
    (htwo : Topology.IsTwoSided (((↑) : K.space → E) ⁻¹' C))
    (hU : U ∈ 𝓝ˢ[K.space] C) :
    ∃ N : Geometry.SimplicialComplex ℝ E, N.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary (n + 1) N ∧ IsConnected N.space ∧
      N.space ⊆ K.space ∧ N.space ⊆ U ∧
      (∀ x ∈ C, N.space ∈ 𝓝[K.space] x) ∧ ¬IsPreconnected (N.space \ C) := by
  let S := ((↑) : K.space → E) ⁻¹' C
  obtain ⟨p, hp⟩ := hconn.nonempty
  let q : K.space := ⟨p, hCK hp⟩
  have hSconn : IsPreconnected S := by
    apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
    rw [Subtype.image_preimage_coe, inter_eq_right.mpr hCK]
    exact hconn.isPreconnected
  have hcomp : connectedComponentIn S q = S :=
    Subset.antisymm (connectedComponentIn_subset S q)
      (hSconn.subset_connectedComponentIn (show q ∈ S from hp) subset_rfl)
  obtain ⟨V, hV, hsep⟩ := htwo q hp
  change V ∈ 𝓝ˢ (connectedComponentIn S q) at hV
  change ∀ W ∈ 𝓝ˢ (connectedComponentIn S q), W ⊆ V → IsConnected W →
    ¬IsPreconnected (W \ connectedComponentIn S q) at hsep
  rw [hcomp] at hV hsep
  have hV' : ((↑) : K.space → E) '' V ∈ 𝓝ˢ[K.space] C := by
    have h := mem_nhdsSet_subtype_iff_nhdsSetWithin.mp hV
    rwa [Subtype.image_preimage_coe, inter_eq_right.mpr hCK] at h
  obtain ⟨N, hNfin, hN, hNconn, hNK, hNU, hNnhds⟩ :=
    hK.exists_connected_neighborhood hC hconn hCK (Filter.inter_mem hV' hU)
  let W := ((↑) : K.space → E) ⁻¹' N.space
  have hWnhds : W ∈ 𝓝ˢ S := mem_nhdsSet_iff_forall.mpr fun x hx =>
    preimage_coe_mem_nhds_subtype.mpr (hNnhds x hx)
  have hWV : W ⊆ V := by
    intro x hx
    obtain ⟨y, hy, hxy⟩ := (hNU hx).1
    exact Subtype.val_injective hxy ▸ hy
  have hWconn : IsConnected W := by
    refine ⟨?_, Topology.IsInducing.subtypeVal.isPreconnected_image.mp ?_⟩
    · obtain ⟨x, hx⟩ := hNconn.nonempty
      exact ⟨⟨x, hNK hx⟩, hx⟩
    · rw [Subtype.image_preimage_coe, inter_eq_right.mpr hNK]
      exact hNconn.isPreconnected
  refine ⟨N, hNfin, hN, hNconn, hNK, hNU.trans inter_subset_right, hNnhds, ?_⟩
  intro hpre
  apply hsep W hWnhds hWV hWconn
  apply Topology.IsInducing.subtypeVal.isPreconnected_image.mp
  change IsPreconnected (((↑) : K.space → E) ''
    (((↑) : K.space → E) ⁻¹' (N.space \ C)))
  rwa [Subtype.image_preimage_coe, inter_eq_right.mpr (sdiff_subset.trans hNK)]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_neighborhood_connectedComponentIn_pair_sdiff_of_twoSided
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : IsCombinatorialManifold 2 L)
    (hLK : L.space ⊆ K.space) (hB : Disjoint L.space (boundaryComplex 3 K).space)
    (hconn : IsConnected L.space)
    (htwo : Topology.IsTwoSided (((↑) : K.space → E) ⁻¹' L.space))
    {U : Set E} (hU : U ∈ 𝓝ˢ[K.space] L.space) :
    ∃ N : Geometry.SimplicialComplex ℝ E, N.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 3 N ∧ IsConnected N.space ∧
      N.space ⊆ K.space ∧ N.space ⊆ U ∧ L.space ⊆ N.space ∧
      (∀ x ∈ L.space, N.space ∈ 𝓝[K.space] x) ∧
      Disjoint L.space (boundaryComplex 3 N).space ∧
      ∃ a ∈ N.space \ L.space, ∃ b ∈ N.space \ L.space,
        let A := connectedComponentIn (N.space \ L.space) a
        let B := connectedComponentIn (N.space \ L.space) b
        Disjoint A B ∧ A ∪ B = N.space \ L.space ∧
        closure A ∪ closure B = N.space ∧ closure A ∩ closure B = L.space := by
  obtain ⟨N, hNfin, hN, hNconn, hNK, hNU, hNnhds, hsep⟩ :=
    hK.exists_connected_neighborhood_sdiff_not_isPreconnected
      (isPolyhedron_space L).isCompact hconn hLK htwo hU
  let _ : Finite N.faces := hNfin.to_subtype
  have hLN : L.space ⊆ N.space := fun x hx => mem_of_mem_nhdsWithin (hLK hx) (hNnhds x hx)
  have hBN : Disjoint L.space (boundaryComplex 3 N).space := by
    apply disjoint_left.mpr
    intro x hx hxB
    exact disjoint_left.mp hB hx
      ((mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin K N hK hN hNK
        (hLN hx) (hNnhds x hx)).mp hxB)
  exact ⟨N, hNfin, hN, hNconn, hNK, hNU, hLN, hNnhds, hBN,
    hN.exists_connectedComponentIn_pair_sdiff_of_separating_surface hL hLN hBN
      hNconn.isPreconnected hconn hsep⟩

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_neighborhood_manifold_pair_of_twoSided
    {K L : Geometry.SimplicialComplex ℝ E} [Finite K.faces] [Finite L.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hL : IsCombinatorialManifold 2 L)
    (hLK : L.space ⊆ K.space) (hB : Disjoint L.space (boundaryComplex 3 K).space)
    (hconn : IsConnected L.space)
    (htwo : Topology.IsTwoSided (((↑) : K.space → E) ⁻¹' L.space))
    {U : Set E} (hU : U ∈ 𝓝ˢ[K.space] L.space) :
    ∃ N A B : Geometry.SimplicialComplex ℝ E,
      N.faces.Finite ∧ A.faces.Finite ∧ B.faces.Finite ∧
      IsCombinatorialManifoldWithBoundary 3 N ∧ IsCombinatorialManifoldWithBoundary 3 A ∧
      IsCombinatorialManifoldWithBoundary 3 B ∧
      IsConnected N.space ∧ IsConnected A.space ∧ IsConnected B.space ∧
      N.space ⊆ K.space ∧ N.space ⊆ U ∧
      (∀ x ∈ L.space, N.space ∈ 𝓝[K.space] x) ∧
      Disjoint L.space (boundaryComplex 3 N).space ∧
      A.space ∪ B.space = N.space ∧ A.space ∩ B.space = L.space ∧
      (boundaryComplex 3 A).space = L.space ∪ (A.space ∩ (boundaryComplex 3 N).space) ∧
      (boundaryComplex 3 B).space = L.space ∪ (B.space ∩ (boundaryComplex 3 N).space) := by
  obtain ⟨N, hNfin, hN, hNconn, hNK, hNU, hLN, hNnhds, hBN,
    a, ha, b, hb, hdis, hcover, hclcover, hclmeet⟩ :=
    hK.exists_neighborhood_connectedComponentIn_pair_sdiff_of_twoSided hL hLK hB hconn htwo hU
  let _ : Finite N.faces := hNfin.to_subtype
  obtain ⟨A, hAfin, hAspace⟩ :=
    (isPolyhedron_closure_connectedComponentIn_sdiff_of_subset N L hLN a).exists_simplicialComplex
  obtain ⟨B, hBfin, hBspace⟩ :=
    (isPolyhedron_closure_connectedComponentIn_sdiff_of_subset N L hLN b).exists_simplicialComplex
  let _ : Finite A.faces := hAfin.to_subtype
  let _ : Finite B.faces := hBfin.to_subtype
  have hclmeet' : closure (connectedComponentIn (N.space \ L.space) b) ∩
      closure (connectedComponentIn (N.space \ L.space) a) = L.space := by
    rwa [inter_comm]
  have hA := isCombinatorialManifoldWithBoundary_of_space_eq_closure_connectedComponentIn_sdiff
    hN hL hLN hBN hdis hclmeet A hAspace
  have hB := isCombinatorialManifoldWithBoundary_of_space_eq_closure_connectedComponentIn_sdiff
    hN hL hLN hBN hdis.symm hclmeet' B hBspace
  refine ⟨N, A, B, hNfin, hAfin, hBfin, hN, hA, hB, hNconn,
    ?_, ?_, hNK, hNU, hNnhds, hBN, ?_, ?_, ?_, ?_⟩
  · rw [hAspace]
    exact (isConnected_connectedComponentIn_iff.mpr ha).closure
  · rw [hBspace]
    exact (isConnected_connectedComponentIn_iff.mpr hb).closure
  · rwa [hAspace, hBspace]
  · rwa [hAspace, hBspace]
  · exact boundaryComplex_space_of_space_eq_closure_connectedComponentIn_sdiff
      hN hL hLN hBN hdis hclmeet A hAspace
  · exact boundaryComplex_space_of_space_eq_closure_connectedComponentIn_sdiff
      hN hL hLN hBN hdis.symm hclmeet' B hBspace
end DifferentialGeometry.Topology.PiecewiseLinear
