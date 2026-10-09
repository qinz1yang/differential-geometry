/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactOuterCarrier

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
theorem exists_compact_boundary_faceDisk_of_frontier_neighborhood
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hKM : K.faces ⊆ M.faces)
    (hint : K.space ⊆ interior M.space) {x : E3}
    (hxN : x ∈ frontier (compactDualNeighborhood M K)) (hxK : x ∈ frontier K.space) :
    ∃ s : Section34CompactSimplexIndex K 3,
      convexHull ℝ (s.1 : Set E3) ⊆ frontier K.space ∧ x ∈ compactDualResidualCell M K s.1 := by
  let : DecidableEq E3 := Classical.decEq E3
  let _ : Finite K.faces := ((Set.toFinite M.faces).subset hKM).to_subtype
  let _ : Finite (Section34CompactSimplexIndex K 3) :=
    finite_section34CompactSimplexIndex (Set.toFinite K.faces) 3
  let B := boundaryComplex 3 K
  let _ : Finite B.faces := (boundaryComplex_faces_finite 3 K).to_subtype
  let L := restrict K (section34CompactGraphSkeleton K)
  let N := compactDualNeighborhood M K
  have hBK : B.faces ⊆ K.faces := boundaryComplex_faces_subset 3 K
  have hBM : B.faces ⊆ M.faces := hBK.trans hKM
  have hLM : L.faces ⊆ M.faces := (restrict_faces_subset K _).trans hKM
  have hB := (isCombinatorialManifold_boundaryComplex K hK).isCombinatorialManifoldWithBoundary
  have hBsp : B.space = frontier K.space :=
    (frontier_space_eq_boundaryComplex_space (n := 2) hK).symm
  have hN : N = (derivedNeighborhood M L).space := by
    change (⋃ v ∈ K.vertices, (graphDualCell M L v).space) = _
    rw [vertices_eq_setOf_restrict_section34CompactGraphSkeleton]
    exact iUnion_graphDualCell_space M L hLM
  have hNint : N ⊆ interior M.space := by
    rw [hN]
    exact derivedNeighborhood_space_subset_interior (n := 2) (by simp) hM hLM
      ((space_mono_of_faces_subset (restrict_faces_subset K _)).trans hint)
  have hxR : x ∈ closure (B.space \ N) := by
    change x ∈ frontier N at hxN
    rw [hN] at hxN ⊢
    exact frontier_derivedNeighborhood_inter_subcomplex_subset_residual M B L hBM hLM
      (hN ▸ hNint) ⟨hxN, hBsp.symm ▸ hxK⟩
  let U := ⋃ (s : Section34CompactSimplexIndex K 3)
    (_ : convexHull ℝ (s.1 : Set E3) ⊆ frontier K.space), compactDualResidualCell M K s.1
  have hcover : B.space \ N ⊆ U := by
    rintro y ⟨hyB, hyN⟩
    obtain ⟨r, hr, hyr⟩ := B.mem_space_iff.mp hyB
    obtain ⟨s, hs, hrs, hsc⟩ := hB.exists_face_superset_card_eq hr
    let f : Section34CompactSimplexIndex K 3 := ⟨s, hBK hs, hsc⟩
    have hfB : convexHull ℝ (f.1 : Set E3) ⊆ frontier K.space :=
      (B.convexHull_subset_space hs).trans hBsp.subset
    exact mem_iUnion₂.mpr ⟨f, hfB, subset_closure
      ⟨convexHull_mono (Finset.coe_subset.mpr hrs) hyr, hyN⟩⟩
  have hUc : IsClosed U := isClosed_iUnion_of_finite fun _ =>
    isClosed_iUnion_of_finite fun _ => isClosed_closure
  obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp (closure_minimal hcover hUc hxR)
  exact ⟨s, hs, hxs⟩

open Classical in
theorem compactDualCutBoundary_outerArc_eq_union
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hKM : K.faces ⊆ M.faces)
    (hint : K.space ⊆ interior M.space) (q : Section34CompactOuterEdgeIndex K K) :
    compactDualCutBoundary M K hKM (.outerArc q) =
      ⋃ (p : Section34CompactMarkIndex K K)
        (_ : p.1.2 = q.1 ∧ convexHull ℝ (p.1.1.1 : Set E3) ⊆ frontier K.space),
          compactDualCutCell M K hKM (.markedPoint p) := by
  let : DecidableEq E3 := Classical.decEq E3
  rw [compactDualCutBoundary_outerArc_eq_splitBoundary_inter_frontier M K hM hK hKM hint q]
  apply Subset.antisymm
  · rintro x ⟨hxDbd, hxK⟩
    have hx := (compactDualCutBoundary_splitDisk_eq_inter_frontier M K hM hKM hint q.1)
      ▸ hxDbd
    obtain ⟨s, hsB, hxs⟩ := exists_compact_boundary_faceDisk_of_frontier_neighborhood
      M K hM hK hKM hint hx.2 hxK
    have hxconv : x ∈ convexHull ℝ (s.1 : Set E3) :=
      closure_minimal sdiff_subset (s.1.finite_toSet.isCompact_convexHull ℝ).isClosed hxs
    have hes : q.1.1 ⊆ s.1 := subset_of_mem_dualCell_of_mem_convexHull M (hKM q.1.2.1)
      (hKM s.2.1) (splittingDisk_space_subset_dualCell M (hKM q.1.2.1) hx.1) hxconv
    have hinc : Section34Incident q.1.1 s.1 :=
      (Finset.coe_subset.mpr hes).trans (subset_convexHull ℝ _)
    let p : Section34CompactMarkIndex K K := ⟨(s, q.1), hinc⟩
    exact mem_iUnion₂.mpr ⟨p, ⟨rfl, hsB⟩, hx.1, hxs⟩
  · intro x hx
    obtain ⟨p, ⟨hpq, hpB⟩, hxp⟩ := mem_iUnion₂.mp hx
    change x ∈ compactDualSplitDisk M K hKM p.1.2 ∩ compactDualResidualCell M K p.1.1.1 at hxp
    rw [hpq] at hxp
    exact ⟨compactDualSplitDisk_inter_residual_subset_boundary M K hM hKM hint q.1
      p.1.1.1 hxp, hpB (closure_minimal sdiff_subset
        (p.1.1.1.finite_toSet.isCompact_convexHull ℝ).isClosed hxp.2)⟩

open Classical in
theorem compactDualCutBoundary_outerFace_eq_union
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hKM : K.faces ⊆ M.faces)
    (hint : K.space ⊆ interior M.space) (o : Section34CompactOuterVertexIndex K K) :
    compactDualCutBoundary M K hKM (.outerFace o) =
      (⋃ (a : Section34CompactArcIndex K K)
        (_ : a.1.2 = o.1 ∧ convexHull ℝ (a.1.1.1 : Set E3) ⊆ frontier K.space),
          compactDualCutCell M K hKM (.faceArc a)) ∪
      ⋃ (q : Section34CompactOuterEdgeIndex K K) (_ : o.1.1 ⊆ q.1.1),
        compactDualCutCell M K hKM (.outerArc q) := by
  let : DecidableEq E3 := Classical.decEq E3
  let _ : Finite K.faces := ((Set.toFinite M.faces).subset hKM).to_subtype
  let L := restrict K (section34CompactGraphSkeleton K)
  let v := o.1.1.centroid ℝ id
  have hvs : {v} = o.1.1 := singleton_centroid_eq_compactVertexIndex o.1
  have hvL : {v} ∈ L.faces := by
    rw [hvs]
    exact ⟨o.1.2.1, o.1.2.2.2⟩
  have hLM : L.faces ⊆ M.faces := (restrict_faces_subset K _).trans hKM
  have hLcard : ∀ s ∈ L.faces, s.card ≤ 2 :=
    fun _ hs => card_le_two_of_mem_restrict_section34CompactGraphSkeleton hs
  have hdis : Disjoint K.space (boundaryComplex 3 M).space := by
    rw [← frontier_space_eq_boundaryComplex_space (n := 2) hM]
    exact disjoint_left.mpr fun x hxK hxB => hxB.2 (hint hxK)
  have hmeet : K.space ∩ closure (M.space \ K.space) = frontier K.space := by
    rw [frontier_space_eq_boundaryComplex_space (n := 2) hK]
    exact inter_closure_sdiff_eq_boundaryComplex_of_disjoint_boundary M K hM hK
      (space_mono_of_faces_subset hKM) hdis
  apply Subset.antisymm
  · intro x hxB
    have hx := (compactDualCutBoundary_outerFace_eq_inter M K hM hK hKM hint o) ▸ hxB
    have hxo := (compactDualOuterFace_eq_inter_frontier_complement M K hM hK hKM hint o)
      ▸ hx.1
    rcases hx.2 with hxK | hxD
    · have hxKB : x ∈ frontier K.space := hmeet ▸ ⟨hxK, hxo.2⟩
      obtain ⟨s, hsB, hxs⟩ := exists_compact_boundary_faceDisk_of_frontier_neighborhood
        M K hM hK hKM hint hxo.1.2 hxKB
      have hxconv : x ∈ convexHull ℝ (s.1 : Set E3) :=
        closure_minimal sdiff_subset (s.1.finite_toSet.isCompact_convexHull ℝ).isClosed hxs
      have hvs' : v ∈ s.1 := by
        by_contra hvs'
        have h := graphDualCell_space_inter_convexHull_eq_empty L (hLM hvL) (hKM s.2.1) hvs'
        exact (h ▸ (show x ∈ (graphDualCell M L v).space ∩
          convexHull ℝ (s.1 : Set E3) from ⟨hxo.1.1, hxconv⟩)).elim
      have hinc : Section34Incident o.1.1 s.1 := by
        rw [← hvs]
        intro z hz
        have hzv : z = v := by simpa only [Finset.coe_singleton, mem_singleton_iff] using hz
        subst z
        exact subset_convexHull ℝ _ hvs'
      let a : Section34CompactArcIndex K K := ⟨(s, o.1), hinc⟩
      exact Or.inl (mem_iUnion₂.mpr ⟨a, ⟨rfl, hsB⟩, hxo.1.1, hxs⟩)
    · obtain ⟨e, hxe⟩ := mem_iUnion.mp hxD
      let Q := subcomplexGeneratedBy M K.facesᶜ
      have hQM : Q.faces ⊆ M.faces := subcomplexGeneratedBy_faces_subset M K.facesᶜ
      have hQsp : Q.space = closure (M.space \ K.space) :=
        (closure_space_sdiff_space_eq_subcomplexGeneratedBy M M K Subset.rfl hKM).symm
      have heQ := mem_faces_of_dualCell_inter_subcomplex M Q hQM (hKM e.2.1)
        (splittingDisk_space_subset_dualCell M (hKM e.2.1) hxe) (hQsp.symm ▸ hxo.2)
      have heB : convexHull ℝ (e.1 : Set E3) ⊆ frontier K.space := by
        intro y hy
        exact hmeet ▸ ⟨K.convexHull_subset_space e.2.1 hy,
          hQsp ▸ Q.convexHull_subset_space heQ hy⟩
      let q : Section34CompactOuterEdgeIndex K K := ⟨e, heB⟩
      have hve := mem_of_graphDualCell_inter_splittingDisk_nonempty M L (hLM hvL)
        (hKM e.2.1) ⟨x, hxo.1.1, hxe⟩
      have hwe : o.1.1 ⊆ q.1.1 := by rw [← hvs]; exact Finset.singleton_subset_iff.mpr hve
      refine Or.inr (mem_iUnion₂.mpr ⟨q, hwe, ?_⟩)
      rw [compactDualOuterArc_eq_splitBoundary_inter_complement M K hM hK hKM hint q,
        compactDualCutBoundary_splitDisk_eq_inter_frontier M K hM hKM hint q.1]
      exact ⟨⟨hxe, hxo.1.2⟩, hxo.2⟩
  · rintro x (hxA | hxQ)
    · obtain ⟨a, ⟨hao, haB⟩, hxa⟩ := mem_iUnion₂.mp hxA
      change x ∈ compactDualVertexBall M K a.1.2 ∩ compactDualResidualCell M K a.1.1.1 at hxa
      rw [hao] at hxa
      have hxK : x ∈ K.space := compactDualResidualCell_subset_space M K a.1.1.2.1 hxa.2
      have hxKB : x ∈ frontier K.space := haB (closure_minimal sdiff_subset
        (a.1.1.1.finite_toSet.isCompact_convexHull ℝ).isClosed hxa.2)
      have hxQ : x ∈ closure (M.space \ K.space) := (hmeet.symm ▸ hxKB).2
      have havoid : compactDualResidualCell M K a.1.1.1 ⊆
          (interior (compactDualNeighborhood M K))ᶜ := by
        apply closure_minimal
        · exact fun _ hy hyi => hy.2 (interior_subset hyi)
        · exact isOpen_interior.isClosed_compl
      have hxN : x ∈ frontier (compactDualNeighborhood M K) :=
        ⟨subset_closure (compactDualVertexBall_subset_neighborhood M K o.1 hxa.1), havoid hxa.2⟩
      have hxO : x ∈ compactDualCutCell M K hKM (.outerFace o) := by
        rw [compactDualOuterFace_eq_inter_frontier_complement M K hM hK hKM hint o]
        exact ⟨⟨hxa.1, hxN⟩, hxQ⟩
      exact compactDualCutCell_outerFace_inter_base_subset_boundary M K hM hK hKM hint o
        ⟨hxO, hxK⟩
    · obtain ⟨q, hoq, hxq⟩ := mem_iUnion₂.mp hxQ
      have hqx := (compactDualOuterArc_eq_splitBoundary_inter_complement M K hM hK hKM hint q)
        ▸ hxq
      have hx := (compactDualCutBoundary_splitDisk_eq_inter_frontier M K hM hKM hint q.1)
        ▸ hqx.1
      have hve : v ∈ q.1.1 := hoq (hvs ▸ Finset.mem_singleton_self v)
      obtain ⟨u, hue, huv⟩ := Finset.exists_mem_ne
        (by rw [q.1.2.2.1]; omega : 1 < q.1.1.card) v
      have heL : q.1.1 ∈ L.faces := ⟨q.1.2.1, q.1.2.2.2⟩
      have hI := graphDualCell_space_inter_of_mem M L hLM hLcard heL hve hue huv.symm
      have hxV : x ∈ compactDualVertexBall M K o.1 := (hI.symm.subset hx.1).1
      have hxO : x ∈ compactDualCutCell M K hKM (.outerFace o) := by
        rw [compactDualOuterFace_eq_inter_frontier_complement M K hM hK hKM hint o]
        exact ⟨⟨hxV, hx.2⟩, hqx.2⟩
      rw [compactDualCutBoundary_outerFace_eq_inter M K hM hK hKM hint o]
      exact ⟨hxO, Or.inr (mem_iUnion.mpr ⟨q.1, hx.1⟩)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
