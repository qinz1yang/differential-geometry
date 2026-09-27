/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualVertexBoundary

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
theorem compactDualCutBoundary_splitDisk_eq_union
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hKM : K.faces ⊆ M.faces)
    (hint : K.space ⊆ interior M.space) (e : Section34CompactEdgeIndex K K) :
    compactDualCutBoundary M K hKM (.splitDisk e) =
      (⋃ (i : Section34CompactEdgeArcIndex K K) (_ : i.1.2 = e),
        compactDualCutCell M K hKM (.edgeArc i)) ∪
      ⋃ (q : Section34CompactOuterEdgeIndex K K) (_ : q.1 = e),
        compactDualCutCell M K hKM (.outerArc q) := by
  let dNative : DecidableEq E3 := inferInstance
  let : DecidableEq E3 := Classical.decEq E3
  let _ : Finite K.faces := ((Set.toFinite M.faces).subset hKM).to_subtype
  let _ : Finite (Section34CompactSimplexIndex K 4) :=
    finite_section34CompactSimplexIndex (Set.toFinite K.faces) 4
  let L := restrict K (section34CompactGraphSkeleton K)
  let G := splittingDisk M e.1 (hKM e.2.1)
  let D := compactDualSplitDisk M K hKM e
  let N := compactDualNeighborhood M K
  let _ : Finite G.faces := (splittingDisk_faces_finite M (hKM e.2.1)).to_subtype
  have hLM : L.faces ⊆ M.faces := (restrict_faces_subset K _).trans hKM
  have heL : e.1 ∈ L.faces := ⟨e.2.1, e.2.2.2⟩
  have hLcard : ∀ s ∈ L.faces, s.card ≤ e.1.card := by
    intro s hs
    rw [e.2.2.1]
    exact card_le_two_of_mem_restrict_section34CompactGraphSkeleton hs
  have hN : N = (derivedNeighborhood M L).space := by
    change (⋃ v ∈ K.vertices, (graphDualCell M L v).space) = _
    rw [vertices_eq_setOf_restrict_section34CompactGraphSkeleton]
    exact iUnion_graphDualCell_space M L hLM
  have hNint : N ⊆ interior M.space := by
    rw [hN]
    exact derivedNeighborhood_space_subset_interior (n := 2) (by simp) hM hLM
      ((space_mono_of_faces_subset (restrict_faces_subset K _)).trans hint)
  have hDN : D ⊆ N := compactDualSplitDisk_subset_neighborhood M K hKM e
  have hDM : D ⊆ M.space := hDN.trans (hNint.trans interior_subset)
  have hvertices : ∀ v ∈ L.vertices, v ∈ interior M.space := by
    intro v hv
    exact hint (K.subset_space hv.1 (Finset.mem_singleton_self v))
  obtain ⟨r, hr, hfront⟩ := hM.exists_isPLHomeomorphOn_splittingDisk_inter_frontier
    (n := 2) (k := 1) (by simp) hLM hvertices heL e.2.2.1 (by decide) hLcard
  have hUnion : (⋃ v ∈ L.vertices, (graphDualCell M L v).space) = N :=
    (iUnion_graphDualCell_space M L hLM).trans hN.symm
  have hfrontN : D ∩ frontier N = r '' stdSimplexBoundary 2 :=
    (congrArg (fun P : Set E3 => D ∩ frontier P) hUnion).symm.trans hfront
  have hB : D ∩ frontier N = (boundaryComplex 2 G).space :=
    hfrontN.trans (hr.image_stdSimplexBoundary_eq_boundaryComplex G rfl)
  have hGTransport : @boundaryComplex E3 _ _ dNative 2 G = boundaryComplex 2 G :=
    congrArg (fun d : DecidableEq E3 => @boundaryComplex E3 _ _ d 2 G)
      (Subsingleton.elim _ _)
  rw [compactDualCutBoundary_splitDisk M K hKM e, hGTransport]
  change (boundaryComplex 2 G).space = _
  apply Subset.antisymm
  · intro x hxB
    have hx := hB.symm ▸ hxB
    have hxD : x ∈ D := hx.1
    have hxFN : x ∈ frontier N := hx.2
    by_cases hxK : x ∈ K.space
    · have hxR : x ∈ closure (K.space \ N) := by
        rw [hN] at hxFN ⊢
        exact frontier_derivedNeighborhood_inter_subcomplex_subset_residual M K L hKM hLM
          (hN ▸ hNint) ⟨hxFN, hxK⟩
      have hcover : K.space \ N ⊆ ⋃ t : Section34CompactSimplexIndex K 4,
          compactDualResidualCell M K t.1 := by
        rintro y ⟨hyK, hyN⟩
        obtain ⟨s, hs, hys⟩ := K.mem_space_iff.mp hyK
        obtain ⟨t, ht, hst, htcard⟩ := hK.exists_face_superset_card_eq hs
        exact mem_iUnion.mpr ⟨⟨t, ht, htcard⟩, subset_closure
          ⟨convexHull_mono (Finset.coe_subset.mpr hst) hys, hyN⟩⟩
      have hclosed : IsClosed (⋃ t : Section34CompactSimplexIndex K 4,
          compactDualResidualCell M K t.1) := isClosed_iUnion_of_finite fun _ => isClosed_closure
      obtain ⟨t, hxt⟩ := mem_iUnion.mp (closure_minimal hcover hclosed hxR)
      have hxtconv : x ∈ convexHull ℝ (t.1 : Set E3) :=
        closure_minimal sdiff_subset (t.1.finite_toSet.isCompact_convexHull ℝ).isClosed hxt
      have het : e.1 ⊆ t.1 := subset_of_mem_dualCell_of_mem_convexHull M (hKM e.2.1)
        (hKM t.2.1) (splittingDisk_space_subset_dualCell M (hKM e.2.1) hxD) hxtconv
      have hinc : Section34Incident e.1 t.1 :=
        (Finset.coe_subset.mpr het).trans (subset_convexHull ℝ _)
      let i : Section34CompactEdgeArcIndex K K := ⟨(t, e), hinc⟩
      exact Or.inl (mem_iUnion₂.mpr ⟨i, rfl, hxt, hxD⟩)
    · let Q := subcomplexGeneratedBy M K.facesᶜ
      have hQM : Q.faces ⊆ M.faces := subcomplexGeneratedBy_faces_subset M K.facesᶜ
      have hQsp : Q.space = closure (M.space \ K.space) :=
        (closure_space_sdiff_space_eq_subcomplexGeneratedBy M M K Subset.rfl hKM).symm
      have hxQ : x ∈ Q.space := hQsp.symm ▸ subset_closure ⟨hDM hxD, hxK⟩
      have heQ := mem_faces_of_dualCell_inter_subcomplex M Q hQM (hKM e.2.1)
        (splittingDisk_space_subset_dualCell M (hKM e.2.1) hxD) hxQ
      have hdis : Disjoint K.space (boundaryComplex 3 M).space := by
        rw [← frontier_space_eq_boundaryComplex_space (n := 2) hM]
        exact disjoint_left.mpr fun y hyK hyB => hyB.2 (hint hyK)
      have hmeet := inter_closure_sdiff_eq_boundaryComplex_of_disjoint_boundary M K
        hM hK (space_mono_of_faces_subset hKM) hdis
      have heB : convexHull ℝ (e.1 : Set E3) ⊆ frontier K.space := by
        rw [frontier_space_eq_boundaryComplex_space (n := 2) hK, ← hmeet]
        intro y hy
        exact ⟨K.convexHull_subset_space e.2.1 hy,
          hQsp ▸ Q.convexHull_subset_space heQ hy⟩
      let q : Section34CompactOuterEdgeIndex K K := ⟨e, heB⟩
      have hxBNative : x ∈ (@boundaryComplex E3 _ _ dNative 2 G).space :=
        hGTransport.symm ▸ hxB
      exact Or.inr (mem_iUnion₂.mpr ⟨q, rfl, subset_closure ⟨hxBNative, hxK⟩⟩)
  · rintro x (hxI | hxQ)
    · obtain ⟨i, hie, hxi⟩ := mem_iUnion₂.mp hxI
      change x ∈ compactDualResidualCell M K i.1.1.1 ∩
        compactDualSplitDisk M K hKM i.1.2 at hxi
      rw [hie] at hxi
      apply hB.subset
      refine ⟨hxi.2, ?_⟩
      rw [frontier_eq_closure_inter_closure]
      refine ⟨subset_closure (hDN hxi.2), ?_⟩
      exact closure_mono (fun y hy => hy.2) hxi.1
    · obtain ⟨q, hqe, hxq⟩ := mem_iUnion₂.mp hxQ
      subst e
      change x ∈ closure ((@boundaryComplex E3 _ _ dNative 2 G).space \ K.space) at hxq
      rw [hGTransport] at hxq
      exact closure_minimal sdiff_subset
        (isPolyhedron_space (boundaryComplex 2 G)).isClosed hxq

end DifferentialGeometry.Topology.PiecewiseLinear
