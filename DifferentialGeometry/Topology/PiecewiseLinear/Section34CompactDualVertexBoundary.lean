/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedCellSubcomplex
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactOuterFace
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactPatchRecognition
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCellSeparation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

section Restriction

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem frontier_derivedNeighborhood_inter_subcomplex_subset_residual
    (M K L : Geometry.SimplicialComplex ℝ E) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (hLM : L.faces ⊆ M.faces)
    (hint : (derivedNeighborhood M L).space ⊆ interior M.space) :
    frontier (derivedNeighborhood M L).space ∩ K.space ⊆
      closure (K.space \ (derivedNeighborhood M L).space) := by
  let _ : Finite K.faces := ((Set.toFinite M.faces).subset hKM).to_subtype
  rintro x ⟨hxF, hxK⟩
  have hxint := hint (frontier_derivedNeighborhood_space_subset M L hxF)
  have hxR : x ∈ closure (M.space \ (derivedNeighborhood M L).space) := by
    rw [frontier_eq_closure_inter_closure] at hxF
    apply mem_closure_iff.mpr
    intro O hO hxO
    obtain ⟨y, hyO, hyN⟩ := mem_closure_iff.mp hxF.2 (O ∩ interior M.space)
      (hO.inter isOpen_interior) ⟨hxO, hxint⟩
    exact ⟨y, hyO.1, interior_subset hyO.2, hyN⟩
  rw [closure_space_sdiff_derivedNeighborhood_space (A := M) Subset.rfl hLM] at hxR
  obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hxR
  have hxsD : x ∈ (dualCell (barycentricSubdivision M) {s.centroid ℝ id}
      (singleton_centroid_mem_barycentricSubdivision M hs.1)).space := by
    rwa [derivedNeighborhoodCell_eq_dualCell M hs.1] at hxs
  have hcsK := mem_faces_of_dualCell_inter_subcomplex
    (barycentricSubdivision M) (barycentricSubdivision K)
    (barycentricSubdivision_faces_subset hKM)
    (singleton_centroid_mem_barycentricSubdivision M hs.1) hxsD
    ((barycentricSubdivision_isSubdivision K).space_eq.symm ▸ hxK)
  obtain ⟨t, ht, htc⟩ := exists_eq_centroid_of_singleton_mem_barycentricSubdivision K hcsK
  have hts := injOn_faces_of_mem_openSimplex M
    (centroid_mem_openSimplex_of_mem_faces M) (hKM ht) hs.1 htc
  have hsK : s ∈ K.faces := hts ▸ ht
  have hxcell : x ∈ (derivedNeighborhoodCell K s).space := by
    rw [← derivedNeighborhoodCell_inter_subcomplex M K hKM hsK]
    exact ⟨hxs, hxK⟩
  have hxR' : x ∈ closure (K.space \ (derivedNeighborhood K L).space) := by
    rw [closure_space_sdiff_derivedNeighborhood_space hKM hLM]
    exact mem_iUnion₂.mpr ⟨s, ⟨hsK, hs.2⟩, hxcell⟩
  have hdiff : K.space \ (derivedNeighborhood K L).space =
      K.space \ (derivedNeighborhood M L).space := by
    rw [← derivedNeighborhood_space_inter_subcomplex M K L hKM]
    ext y
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  rwa [hdiff] at hxR'

open Classical in
theorem frontier_graphDualCell_sdiff_splittingDisk_subset
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hLK : L.faces ⊆ K.faces) (hcard : ∀ s ∈ L.faces, s.card ≤ 2)
    {v : E} (hv : {v} ∈ L.faces) :
    frontier (graphDualCell K L v).space \
      (⋃ e : {e : Finset E // e ∈ L.faces ∧ e.card = 2},
        (splittingDisk K e.1 (hLK e.2.1)).space) ⊆
      frontier (derivedNeighborhood K L).space := by
  let C := graphDualCell K L v
  let _ : Finite C.faces := (graphDualCell_faces_finite K L v).to_subtype
  have hCc : IsClosed C.space := (SimplicialComplex.isCompact_geometricSpace C).isClosed
  rintro x ⟨hxF, hxD⟩
  have hxC := hCc.frontier_subset hxF
  refine ⟨subset_closure (graphDualCell_space_subset K L v hxC), ?_⟩
  intro hxN
  let O := ⋃ w ∈ L.vertices \ {v}, (graphDualCell K L w).space
  have hfin : L.vertices.Finite :=
    Set.Finite.preimage Finset.singleton_injective.injOn ((Set.toFinite K.faces).subset hLK)
  have hOc : IsClosed O := (hfin.subset sdiff_subset).isClosed_biUnion fun w _ => by
    let _ : Finite (graphDualCell K L w).faces := (graphDualCell_faces_finite K L w).to_subtype
    exact (SimplicialComplex.isCompact_geometricSpace _).isClosed
  have hxO : x ∉ O := by
    intro hx
    obtain ⟨w, ⟨hw, hwv⟩, hxw⟩ := mem_iUnion₂.mp hx
    have hvw : v ≠ w := fun h => hwv h.symm
    by_cases he : {v, w} ∈ L.faces
    · apply hxD
      refine mem_iUnion.mpr ⟨⟨{v, w}, he, by simp [hvw]⟩, ?_⟩
      rw [← graphDualCell_space_inter K L hLK hcard hvw he]
      exact ⟨hxC, hxw⟩
    · have h := graphDualCell_space_inter_eq_empty K L hLK hcard hv hw hvw he
      exact (h ▸ (show x ∈ (graphDualCell K L v).space ∩
        (graphDualCell K L w).space from ⟨hxC, hxw⟩)).elim
  apply hxF.2
  refine mem_interior.mpr ⟨interior (derivedNeighborhood K L).space ∩ Oᶜ, ?_,
    isOpen_interior.inter hOc.isOpen_compl, hxN, hxO⟩
  rintro y ⟨hyN, hyO⟩
  have hy : y ∈ ⋃ w ∈ L.vertices, (graphDualCell K L w).space :=
    (iUnion_graphDualCell_space K L hLK).symm ▸ interior_subset hyN
  obtain ⟨w, hw, hyw⟩ := mem_iUnion₂.mp hy
  by_cases hwv : w = v
  · change y ∈ (graphDualCell K L v).space
    rwa [hwv] at hyw
  · exact (hyO (mem_iUnion₂.mpr ⟨w, ⟨hw, hwv⟩, hyw⟩)).elim

end Restriction

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
theorem compactDualCutBoundary_vertexBall_eq_union
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hKM : K.faces ⊆ M.faces)
    (hint : K.space ⊆ interior M.space) (w : Section34CompactVertexIndex K K) :
    compactDualCutBoundary M K hKM (.vertexBall w) =
      ((⋃ (e : Section34CompactEdgeIndex K K) (_ : w.1 ⊆ e.1),
          compactDualCutCell M K hKM (.splitDisk e)) ∪
        ⋃ (p : Section34CompactPatchIndex K K) (_ : p.1.2 = w),
          compactDualCutCell M K hKM (.patch p)) ∪
      ⋃ (o : Section34CompactOuterVertexIndex K K) (_ : o.1 = w),
        compactDualCutCell M K hKM (.outerFace o) := by
  let : DecidableEq E3 := Classical.decEq E3
  let _ : Finite K.faces := ((Set.toFinite M.faces).subset hKM).to_subtype
  let _ : Finite (Section34CompactSimplexIndex K 4) :=
    finite_section34CompactSimplexIndex (Set.toFinite K.faces) 4
  let L := restrict K (section34CompactGraphSkeleton K)
  let v := w.1.centroid ℝ id
  let C := compactDualVertexBall M K w
  let N := compactDualNeighborhood M K
  have hLM : L.faces ⊆ M.faces := (restrict_faces_subset K _).trans hKM
  have hLcard : ∀ s ∈ L.faces, s.card ≤ 2 :=
    fun _ hs => card_le_two_of_mem_restrict_section34CompactGraphSkeleton hs
  have hws : {v} = w.1 := singleton_centroid_eq_compactVertexIndex w
  have hvL : {v} ∈ L.faces := by
    rw [hws]
    exact ⟨w.2.1, w.2.2.2⟩
  have hCball : IsPLBall 3 C := hM.isPLBall_graphDualCell M L hLM hLcard hvL
  have hCN : C ⊆ N := compactDualVertexBall_subset_neighborhood M K w
  have hN : N = (derivedNeighborhood M L).space := by
    change (⋃ v ∈ K.vertices, (graphDualCell M L v).space) = _
    rw [vertices_eq_setOf_restrict_section34CompactGraphSkeleton]
    exact iUnion_graphDualCell_space M L hLM
  have hNint : N ⊆ interior M.space := by
    rw [hN]
    exact derivedNeighborhood_space_subset_interior (n := 2) (by simp) hM hLM
      ((space_mono_of_faces_subset (restrict_faces_subset K _)).trans hint)
  have hCM : C ⊆ M.space := hCN.trans (hNint.trans interior_subset)
  rw [compactDualCutBoundary_vertexBall_eq_frontier M K hKM hM w]
  change frontier C = _
  apply Subset.antisymm
  · intro x hxF
    have hxC := hCball.isPolyhedron.isClosed.frontier_subset hxF
    by_cases hxD : x ∈ ⋃ e : Section34CompactEdgeIndex K K, compactDualSplitDisk M K hKM e
    · obtain ⟨e, hxe⟩ := mem_iUnion.mp hxD
      have hve := mem_of_graphDualCell_inter_splittingDisk_nonempty M L (hLM hvL)
        (hKM e.2.1) ⟨x, hxC, hxe⟩
      have hwe : w.1 ⊆ e.1 := by
        rw [← hws]
        exact Finset.singleton_subset_iff.mpr hve
      exact Or.inl (Or.inl (mem_iUnion₂.mpr ⟨e, hwe, hxe⟩))
    · have hxFN : x ∈ frontier (derivedNeighborhood M L).space := by
        apply frontier_graphDualCell_sdiff_splittingDisk_subset M L hLM hLcard hvL
        refine ⟨hxF, ?_⟩
        intro hx
        obtain ⟨e, hxe⟩ := mem_iUnion.mp hx
        exact hxD (mem_iUnion.mpr ⟨⟨e.1, e.2.1.1, e.2.2, e.2.1.2⟩, hxe⟩)
      by_cases hxK : x ∈ K.space
      · have hxR : x ∈ closure (K.space \ N) := by
          rw [hN]
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
        have hvt : v ∈ t.1 := by
          by_contra hvt
          have h := graphDualCell_space_inter_convexHull_eq_empty L (hLM hvL) (hKM t.2.1) hvt
          exact (h ▸ (show x ∈ (graphDualCell M L v).space ∩
            convexHull ℝ (t.1 : Set E3) from ⟨hxC, hxtconv⟩)).elim
        have hwt : Section34Incident w.1 t.1 := by
          rw [← hws]
          intro z hz
          have hzv : z = v := by simpa only [Finset.coe_singleton, mem_singleton_iff] using hz
          subst z
          exact subset_convexHull ℝ _ hvt
        let p : Section34CompactPatchIndex K K := ⟨(t, w), hwt⟩
        exact Or.inl (Or.inr (mem_iUnion₂.mpr ⟨p, rfl, hxt, hxC⟩))
      · let Q := subcomplexGeneratedBy M K.facesᶜ
        have hQM : Q.faces ⊆ M.faces := subcomplexGeneratedBy_faces_subset M K.facesᶜ
        have hQsp : Q.space = closure (M.space \ K.space) :=
          (closure_space_sdiff_space_eq_subcomplexGeneratedBy M M K Subset.rfl hKM).symm
        have hxQ : x ∈ Q.space := hQsp.symm ▸ subset_closure ⟨hCM hxC, hxK⟩
        have hxdual : x ∈ (dualCell M {v} (hLM hvL)).space := by
          rw [← closedStar_barycentricSubdivision_eq_dualCell M (hLM hvL)]
          exact graphDualCell_space_subset_closedStar M L v hxC
        have hvQ := mem_faces_of_dualCell_inter_subcomplex M Q hQM (hLM hvL) hxdual hxQ
        have hvQsp := Q.subset_space hvQ (Finset.mem_singleton_self v)
        have hvKsp := K.subset_space (hws.symm ▸ w.2.1) (Finset.mem_singleton_self v)
        have hdis : Disjoint K.space (boundaryComplex 3 M).space := by
          rw [← frontier_space_eq_boundaryComplex_space (n := 2) hM]
          exact disjoint_left.mpr fun y hyK hyB => hyB.2 (hint hyK)
        have hmeet := inter_closure_sdiff_eq_boundaryComplex_of_disjoint_boundary M K
          hM hK (space_mono_of_faces_subset hKM) hdis
        have hvB : v ∈ frontier K.space := by
          rw [frontier_space_eq_boundaryComplex_space (n := 2) hK, ← hmeet]
          exact ⟨hvKsp, hQsp ▸ hvQsp⟩
        have hwB : (w.1 : Set E3) ⊆ frontier K.space := by
          rw [← hws, Finset.coe_singleton]
          exact singleton_subset_iff.mpr hvB
        let o : Section34CompactOuterVertexIndex K K := ⟨w, hwB⟩
        refine Or.inr (mem_iUnion₂.mpr ⟨o, rfl, subset_closure ?_⟩)
        exact ⟨hxF, fun h => h.elim hxK hxD⟩
  · rintro x ((hxD | hxP) | hxO)
    · obtain ⟨e, hwe, hxe⟩ := mem_iUnion₂.mp hxD
      have hve : v ∈ e.1 := hwe (hws ▸ Finset.mem_singleton_self v)
      obtain ⟨u, hue, huv⟩ := Finset.exists_mem_ne
        (by rw [e.2.2.1]; omega : 1 < e.1.card) v
      have heL : e.1 ∈ L.faces := ⟨e.2.1, e.2.2.2⟩
      have huL : {u} ∈ L.faces := L.down_closed heL (Finset.singleton_subset_iff.mpr hue)
        (Finset.singleton_nonempty u)
      have hI := graphDualCell_space_inter_of_mem M L hLM hLcard heL hve hue huv.symm
      have hDball : IsPLBall 2 (splittingDisk M e.1 (hKM e.2.1)).space :=
        hM.isPLBall_splittingDisk M (hKM e.2.1) (k := 1) e.2.2.1 (by decide)
      have hball : IsPLBall 2 (C ∩ (graphDualCell M L u).space) := hI.symm ▸ hDball
      have hsub := (hM.isPLBall_graphDualCell M L hLM hLcard huL)
        |>.inter_subset_frontier_of_isPLBall hball (by decide : 2 < 3)
      exact hsub (hI.symm ▸ hxe)
    · obtain ⟨p, hpw, hxp⟩ := mem_iUnion₂.mp hxP
      change x ∈ compactDualResidualCell M K p.1.1.1 ∩
        compactDualVertexBall M K p.1.2 at hxp
      rw [hpw] at hxp
      rw [frontier_eq_closure_inter_closure]
      refine ⟨subset_closure hxp.2, ?_⟩
      apply closure_mono (t := Cᶜ) ?_ hxp.1
      rintro y ⟨-, hyN⟩ hyC
      exact hyN (hCN hyC)
    · obtain ⟨o, how, hxo⟩ := mem_iUnion₂.mp hxO
      change x ∈ closure (frontier (compactDualVertexBall M K o.1) \ _) at hxo
      rw [how] at hxo
      exact closure_minimal sdiff_subset isClosed_frontier hxo

end DifferentialGeometry.Topology.PiecewiseLinear
