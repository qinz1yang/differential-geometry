/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodResidualRestriction
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactDualCellInteriors
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactPatchRecognition
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactCellSeparation

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

open Classical in
theorem compactDualResidualCell_inter_convexHull
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces] (hKM : K.faces ⊆ M.faces)
    {t s : Finset E3} (ht : t ∈ K.faces) (hs : s ∈ K.faces) (hst : s ⊆ t) :
    compactDualResidualCell M K t ∩ convexHull ℝ (s : Set E3) =
      compactDualResidualCell M K s := by
  let : DecidableEq E3 := Classical.decEq E3
  let A := restrict M (convexHull ℝ (t : Set E3))
  let B := restrict M (convexHull ℝ (s : Set E3))
  let L := restrict K (section34CompactGraphSkeleton K)
  have hAM : A.faces ⊆ M.faces := restrict_faces_subset M _
  have hBM : B.faces ⊆ M.faces := restrict_faces_subset M _
  have hBA : B.faces ⊆ A.faces := by
    intro r hr
    exact ⟨hr.1, hr.2.trans (convexHull_mono (Finset.coe_subset.mpr hst))⟩
  have hLM : L.faces ⊆ M.faces := (restrict_faces_subset K _).trans hKM
  have hAsp : A.space = convexHull ℝ (t : Set E3) := restrict_convexHull_space (hKM ht)
  have hBsp : B.space = convexHull ℝ (s : Set E3) := restrict_convexHull_space (hKM hs)
  have hdiffA : A.space \ (derivedNeighborhood A L).space =
      convexHull ℝ (t : Set E3) \ (derivedNeighborhood M L).space := by
    rw [← derivedNeighborhood_space_inter_subcomplex M A L hAM, hAsp]
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  have hdiffB : B.space \ (derivedNeighborhood B L).space =
      convexHull ℝ (s : Set E3) \ (derivedNeighborhood M L).space := by
    rw [← derivedNeighborhood_space_inter_subcomplex M B L hBM, hBsp]
    ext x
    simp only [mem_sdiff, mem_inter_iff]
    tauto
  have hN : compactDualNeighborhood M K = (derivedNeighborhood M L).space := by
    change (⋃ v ∈ K.vertices, (graphDualCell M L v).space) = _
    rw [vertices_eq_setOf_restrict_section34CompactGraphSkeleton]
    exact iUnion_graphDualCell_space M L hLM
  have h := closure_sdiff_derivedNeighborhood_inter_subcomplex M A B L hAM hBA hLM
  rw [hdiffA, hdiffB, hBsp, ← hN] at h
  exact h

open Classical in
theorem exists_compact_faceDisk_of_tetra_inter
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces] (hKM : K.faces ⊆ M.faces)
    (s t : Section34CompactSimplexIndex K 4) (hst : s ≠ t) {x : E3}
    (hx : x ∈ compactDualResidualCell M K s.1 ∩ compactDualResidualCell M K t.1) :
    ∃ f : Section34CompactSimplexIndex K 3, Section34Incident f.1 s.1 ∧
      Section34Incident f.1 t.1 ∧ x ∈ compactDualResidualCell M K f.1 := by
  let : DecidableEq E3 := Classical.decEq E3
  let r := s.1 ∩ t.1
  have hsub (u : Section34CompactSimplexIndex K 4) :
      compactDualResidualCell M K u.1 ⊆ convexHull ℝ (u.1 : Set E3) :=
    closure_minimal sdiff_subset (u.1.finite_toSet.isCompact_convexHull ℝ).isClosed
  have hxr : x ∈ convexHull ℝ (r : Set E3) := by
    simpa only [r, Finset.coe_inter] using K.inter_subset_convexHull s.2.1 t.2.1
      ⟨hsub s hx.1, hsub t hx.2⟩
  have hrne : r.Nonempty := nonempty_of_mem_convexHull hxr
  have hrK : r ∈ K.faces := K.down_closed s.2.1 Finset.inter_subset_left hrne
  have hxR : x ∈ compactDualResidualCell M K r :=
    (compactDualResidualCell_inter_convexHull M K hKM s.2.1 hrK Finset.inter_subset_left)
      ▸ ⟨hx.1, hxr⟩
  have hrle : r.card ≤ 3 := by
    have hle : r.card ≤ 4 := (Finset.card_le_card Finset.inter_subset_left).trans_eq s.2.2
    by_contra hn
    have hr4 : r.card = 4 := by omega
    have hrs : r = s.1 := Finset.eq_of_subset_of_card_le Finset.inter_subset_left
      (by rw [s.2.2, hr4])
    have hst' : s.1 ⊆ t.1 := hrs ▸ (show r ⊆ t.1 from Finset.inter_subset_right)
    exact hst (Subtype.ext (Finset.eq_of_subset_of_card_le hst' (by rw [s.2.2, t.2.2])))
  have hrge : 3 ≤ r.card := by
    by_contra hn
    have hr2 : r.card ≤ 2 := by omega
    let L := restrict K (section34CompactGraphSkeleton K)
    have hLM : L.faces ⊆ M.faces := (restrict_faces_subset K _).trans hKM
    have hconvN : convexHull ℝ (r : Set E3) ⊆ compactDualNeighborhood M K := by
      have hN : compactDualNeighborhood M K = (derivedNeighborhood M L).space := by
        change (⋃ v ∈ K.vertices, (graphDualCell M L v).space) = _
        rw [vertices_eq_setOf_restrict_section34CompactGraphSkeleton]
        exact iUnion_graphDualCell_space M L hLM
      rw [hN]
      intro y hy
      apply subcomplex_space_subset_derivedNeighborhood hLM
      change y ∈ (restrict K (section34CompactGraphSkeleton K)).space
      rw [restrict_section34CompactGraphSkeleton_space K]
      exact convexHull_subset_section34CompactGraphSkeleton hrK hr2 hy
    change x ∈ closure (convexHull ℝ (r : Set E3) \ compactDualNeighborhood M K) at hxR
    rw [sdiff_eq_empty.mpr hconvN, closure_empty] at hxR
    exact hxR
  let f : Section34CompactSimplexIndex K 3 := ⟨r, hrK, by omega⟩
  exact ⟨f, (Finset.coe_subset.mpr Finset.inter_subset_left).trans (subset_convexHull ℝ _),
    (Finset.coe_subset.mpr Finset.inter_subset_right).trans (subset_convexHull ℝ _), hxR⟩

open Classical in
theorem compactDualCutBoundary_tetraBall_eq_union
    (M K : Geometry.SimplicialComplex ℝ E3) [Finite M.faces]
    (hKM : K.faces ⊆ M.faces) (hM : IsCombinatorialManifoldWithBoundary 3 M)
    (t : Section34CompactSimplexIndex K 4) :
    compactDualCutBoundary M K hKM (.tetraBall t) =
      (⋃ (s : Section34CompactSimplexIndex K 3) (_ : Section34Incident s.1 t.1),
        compactDualCutCell M K hKM (.faceDisk s)) ∪
      ⋃ (p : Section34CompactPatchIndex K K) (_ : p.1.1 = t),
        compactDualCutCell M K hKM (.patch p) := by
  let : DecidableEq E3 := Classical.decEq E3
  let R := compactDualResidualCell M K t.1
  let N := compactDualNeighborhood M K
  let T := convexHull ℝ (t.1 : Set E3)
  let L := restrict K (section34CompactGraphSkeleton K)
  let _ : Finite (derivedNeighborhood M L).faces :=
    (derivedNeighborhood_faces_finite M L).to_subtype
  have hN : N = (derivedNeighborhood M L).space := by
    change (⋃ v ∈ K.vertices, (graphDualCell M L v).space) = _
    rw [vertices_eq_setOf_restrict_section34CompactGraphSkeleton]
    exact iUnion_graphDualCell_space M L ((restrict_faces_subset K _).trans hKM)
  have hNc : IsClosed N := by
    rw [hN]
    exact (SimplicialComplex.isCompact_geometricSpace _).isClosed
  have hRT : R ⊆ T :=
    closure_minimal sdiff_subset (t.1.finite_toSet.isCompact_convexHull ℝ).isClosed
  have hRc : IsClosed R := isClosed_closure
  have hbd : compactDualCutBoundary M K hKM (.tetraBall t) = frontier R :=
    (isPLCellOn_compactDualTetraBall M K hKM t).boundary_eq_frontier
  rw [hbd]
  apply Subset.antisymm
  · intro x hxF
    have hxR := hRc.frontier_subset hxF
    by_cases hxN : x ∈ N
    · have hxV : x ∈ ⋃ w : Section34CompactVertexIndex K K, compactDualVertexBall M K w :=
        (iUnion_compactDualVertexBall M K).symm ▸ hxN
      obtain ⟨w, hxw⟩ := mem_iUnion.mp hxV
      let v := w.1.centroid ℝ id
      have hvM : {v} ∈ M.faces := by
        rw [singleton_centroid_eq_compactVertexIndex w]
        exact hKM w.2.1
      have hvt : v ∈ t.1 := by
        by_contra hvt
        have h := graphDualCell_space_inter_convexHull_eq_empty L hvM (hKM t.2.1) hvt
        exact (h ▸ (show x ∈ (graphDualCell M L v).space ∩ T from ⟨hxw, hRT hxR⟩)).elim
      have hwt : Section34Incident w.1 t.1 := by
        rw [← singleton_centroid_eq_compactVertexIndex w]
        intro z hz
        have hzv : z = v := by simpa only [Finset.coe_singleton, mem_singleton_iff] using hz
        subst z
        exact subset_convexHull ℝ _ hvt
      let p : Section34CompactPatchIndex K K := ⟨(t, w), hwt⟩
      exact Or.inr (mem_iUnion₂.mpr ⟨p, rfl, hxR, hxw⟩)
    · have hxFT : x ∈ frontier T := by
        refine ⟨subset_closure (hRT hxR), ?_⟩
        intro hxT
        apply hxF.2
        refine mem_interior.mpr ⟨interior T ∩ Nᶜ, ?_,
          isOpen_interior.inter hNc.isOpen_compl, hxT, hxN⟩
        rintro y ⟨hyT, hyN⟩
        exact subset_closure ⟨interior_subset hyT, hyN⟩
      change x ∈ frontier (convexHull ℝ (t.1 : Set E3)) at hxFT
      rw [frontier_convexHull_eq_simplexBoundary (K.indep t.2.1)
          (by rw [t.2.2, finrank_euclideanSpace_fin]),
        simplexBoundary_space t.1 (K.indep t.2.1) (by rw [t.2.2]; decide)] at hxFT
      obtain ⟨v, hvt, hxS⟩ := mem_iUnion₂.mp hxFT
      have hsc : (t.1.erase v).card = 3 := by rw [Finset.card_erase_of_mem hvt, t.2.2]
      have hsK : t.1.erase v ∈ K.faces := K.down_closed t.2.1 (Finset.erase_subset _ _)
        (Finset.card_pos.mp (by rw [hsc]; decide))
      let s : Section34CompactSimplexIndex K 3 := ⟨t.1.erase v, hsK, hsc⟩
      have hst : Section34Incident s.1 t.1 :=
        (Finset.coe_subset.mpr (Finset.erase_subset _ _)).trans (subset_convexHull ℝ _)
      have hxs : x ∈ compactDualResidualCell M K s.1 :=
        (compactDualResidualCell_inter_convexHull M K hKM t.2.1 hsK
          (Finset.erase_subset _ _)) ▸ ⟨hxR, hxS⟩
      exact Or.inl (mem_iUnion₂.mpr ⟨s, hst, hxs⟩)
  · rintro x (hxS | hxP)
    · obtain ⟨s, hst, hxs⟩ := mem_iUnion₂.mp hxS
      have hST : convexHull ℝ (s.1 : Set E3) ⊆ T :=
        convexHull_min hst (convex_convexHull ℝ _)
      have hxR : x ∈ R := closure_mono (sdiff_subset_sdiff_left hST) hxs
      have hxS : x ∈ convexHull ℝ (s.1 : Set E3) :=
        closure_minimal sdiff_subset (s.1.finite_toSet.isCompact_convexHull ℝ).isClosed hxs
      refine ⟨subset_closure hxR, ?_⟩
      intro hxint
      have hxopen : x ∈ openSimplex t.1 := by
        rw [← interior_convexHull_eq_openSimplex (K.indep t.2.1)
          (by rw [t.2.2, finrank_euclideanSpace_fin])]
        exact interior_mono hRT hxint
      have hts := face_subset_of_mem_openSimplex_of_mem_convexHull K t.2.1 s.2.1 hxopen hxS
      have hle := Finset.card_le_card hts
      rw [t.2.2, s.2.2] at hle
      omega
    · obtain ⟨p, hpt, hxp⟩ := mem_iUnion₂.mp hxP
      change x ∈ compactDualResidualCell M K p.1.1.1 ∩ compactDualVertexBall M K p.1.2 at hxp
      rw [hpt] at hxp
      have hxB := compactDualResidualCell_inter_neighborhood_subset_boundary M K hKM hM t
        ⟨hxp.1, compactDualVertexBall_subset_neighborhood M K p.1.2 hxp.2⟩
      exact hbd ▸ hxB

end DifferentialGeometry.Topology.PiecewiseLinear
