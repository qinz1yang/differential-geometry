/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceCircleCollar
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldNeighborhood

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_surface_union_disk_of_circle_collar
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K)
    {Δ : Set E} {r : (Fin 3 → ℝ) → E}
    (hr : IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ)
    (hmeet : K.space ∩ Δ = r '' stdSimplexBoundary 2)
    (hcollar : HasPLCircleCollar K.space (r '' stdSimplexBoundary 2)) :
    ∃ (Q : Geometry.SimplicialComplex ℝ E) (hQfin : Q.faces.Finite),
      letI := hQfin.to_subtype
      IsCombinatorialManifoldWithBoundary 2 Q ∧ Q.space = K.space ∪ Δ ∧
      (boundaryComplex 2 Q).space = (boundaryComplex 2 K).space \ r '' stdSimplexBoundary 2 := by
  let _ : DecidableEq E := fun a b => Classical.propDecidable (a = b)
  let G := r '' stdSimplexBoundary 2
  have hGΔ : G ⊆ Δ := (image_mono (fun _ hx => hx.1)).trans hr.image_eq.subset
  obtain ⟨W, ρ, hρ, hρ0, hW, hWnear⟩ := hcollar.2 univ isOpen_univ (subset_univ _)
  have hWK : W ⊆ K.space := hW.trans inter_subset_left
  have hGW : G ⊆ W := fun x hx => hρ0 x hx ▸ hρ.bijOn.mapsTo ⟨hx, by norm_num⟩
  have hWΔ : W ∩ Δ = G := Subset.antisymm
    (fun x hx => hmeet.subset ⟨hWK hx.1, hx.2⟩) (fun x hx => ⟨hGW hx, hGΔ hx⟩)
  obtain ⟨q, hq, -, hΔq⟩ := hr.exists_isPLHomeomorphOn_union_collar zero_lt_one hρ hρ0 hWΔ
  have hΔ : IsPLBall 2 Δ := ⟨r, hr⟩
  have hΔW : IsPLBall 2 (Δ ∪ W) := ⟨q, hq⟩
  obtain ⟨D, hDfin, hDspace⟩ := hΔ.isPolyhedron.exists_simplicialComplex
  obtain ⟨P, hPfin, hPspace⟩ := hΔW.isPolyhedron.exists_simplicialComplex
  obtain ⟨Q, hQfin, hQspace⟩ :=
    ((isPolyhedron_space K).union hΔ.isPolyhedron).exists_simplicialComplex
  let _ : Finite D.faces := hDfin.to_subtype
  let _ : Finite P.faces := hPfin.to_subtype
  let _ : Finite Q.faces := hQfin.to_subtype
  have hD : IsPLBall 2 D.space := hDspace.symm ▸ hΔ
  have hP : IsPLBall 2 P.space := hPspace.symm ▸ hΔW
  have hDb : (boundaryComplex 2 D).space = G := by
    rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex D (hDspace.symm ▸ hr),
      simplexBoundary_stdVertices_space]
  have hPb : (boundaryComplex 2 P).space = q '' stdSimplexBoundary 2 := by
    rw [boundaryComplex_space_of_isPLHomeomorphOn_stdSimplex P (hPspace.symm ▸ hq),
      simplexBoundary_stdVertices_space]
  have hKQ : K.space ⊆ Q.space := hQspace.symm ▸ subset_union_left
  have hDQ : D.space ⊆ Q.space := hDspace.subset.trans (hQspace.symm ▸ subset_union_right)
  have hPQ : P.space ⊆ Q.space := by
    rw [hPspace, hQspace]
    exact union_subset subset_union_right (hWK.trans subset_union_left)
  have hKnear : ∀ x ∉ Δ, K.space ∈ 𝓝[Q.space] x := by
    intro x hx
    refine mem_nhdsWithin.mpr ⟨Δᶜ, hΔ.isPolyhedron.isClosed.isOpen_compl, hx, ?_⟩
    rintro y ⟨hyΔ, hyQ⟩
    exact (hQspace.subset hyQ).resolve_right hyΔ
  have hDnear : ∀ x ∉ K.space, D.space ∈ 𝓝[Q.space] x := by
    intro x hx
    rw [hDspace]
    refine mem_nhdsWithin.mpr
      ⟨K.spaceᶜ, (isPolyhedron_space K).isClosed.isOpen_compl, hx, ?_⟩
    rintro y ⟨hyK, hyQ⟩
    exact (hQspace.subset hyQ).resolve_left hyK
  have hPnear : ∀ x ∈ G, P.space ∈ 𝓝[Q.space] x := by
    intro x hx
    obtain ⟨O, hO, hGO, hOW⟩ := mem_nhdsSetWithin.mp hWnear
    rw [hPspace]
    refine mem_nhdsWithin.mpr ⟨O, hO, hGO hx, ?_⟩
    rintro y ⟨hyO, hyQ⟩
    rcases hQspace.subset hyQ with hyK | hyΔ
    · exact Or.inr (hOW ⟨hyO, hyK⟩)
    · exact Or.inl hyΔ
  have hQ : IsCombinatorialManifoldWithBoundary 2 Q := by
    intro x hx
    by_cases hxG : x ∈ G
    · exact isPLSphere_or_isPLBall_geometricLink_of_manifold_neighborhood Q P
        hP.isCombinatorialManifoldWithBoundary hPQ hx (hPnear x hxG)
    · have hxQ := Q.subset_space hx (Finset.mem_singleton_self x)
      rcases hQspace.subset hxQ with hxK | hxΔ
      · exact isPLSphere_or_isPLBall_geometricLink_of_manifold_neighborhood Q K hK hKQ hx
          (hKnear x (fun hxΔ => hxG (hmeet.subset ⟨hxK, hxΔ⟩)))
      · exact isPLSphere_or_isPLBall_geometricLink_of_manifold_neighborhood Q D
          hD.isCombinatorialManifoldWithBoundary hDQ hx
          (hDnear x (fun hxK => hxG (hmeet.subset ⟨hxK, hxΔ⟩)))
  refine ⟨Q, hQfin, hQ, hQspace, ?_⟩
  ext x
  constructor
  · intro hxB
    have hxQ := boundaryComplex_space_subset 2 Q hxB
    have hxG : x ∉ G := by
      intro hxG
      have hxP : x ∈ P.space := hPspace.symm ▸ Or.inl (hGΔ hxG)
      have hxPB := (mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin (n := 1) Q P
        hQ hP.isCombinatorialManifoldWithBoundary hPQ hxP (hPnear x hxG)).mpr hxB
      exact disjoint_left.mp hΔq (hGΔ hxG) (hPb ▸ hxPB)
    rcases hQspace.subset hxQ with hxK | hxΔ
    · exact ⟨(mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin (n := 1) Q K
        hQ hK hKQ hxK (hKnear x (fun hxΔ => hxG (hmeet.subset ⟨hxK, hxΔ⟩)))).mpr hxB, hxG⟩
    · have hxD : x ∈ D.space := hDspace.symm ▸ hxΔ
      have hxDB := (mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin (n := 1) Q D
        hQ hD.isCombinatorialManifoldWithBoundary hDQ hxD
        (hDnear x (fun hxK => hxG (hmeet.subset ⟨hxK, hxΔ⟩)))).mpr hxB
      exact (hxG (hDb ▸ hxDB)).elim
  · rintro ⟨hxB, hxG⟩
    have hxK := boundaryComplex_space_subset 2 K hxB
    exact (mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin (n := 1) Q K hQ hK hKQ hxK
      (hKnear x (fun hxΔ => hxG (hmeet.subset ⟨hxK, hxΔ⟩)))).mp hxB

end DifferentialGeometry.Topology.PiecewiseLinear
