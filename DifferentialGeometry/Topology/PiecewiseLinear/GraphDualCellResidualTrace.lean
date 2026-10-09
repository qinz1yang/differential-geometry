/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.GraphDualCellIncidence
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubcomplexBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CompactResidualCells
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexNhdsWithin

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem graphDualCell_inter_residual_eq_boundary_remainder
    (K L : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 3 K) (hLK : L.faces ⊆ K.faces)
    (hcard : ∀ s ∈ L.faces, s.card ≤ 2) {v : E} (hv : {v} ∈ L.faces) :
    let C := graphDualCell K L v
    let I := {e : Finset E // e ∈ L.faces ∧ e.card = 2 ∧ v ∈ e}
    C.space ∩ closure (K.space \ (derivedNeighborhood K L).space) =
      closure ((boundaryComplex 3 C).space \ ((boundaryComplex 3 K).space ∪
        ⋃ e : I, (splittingDisk K e.1 (hLK e.2.1)).space)) := by
  let C := graphDualCell K L v
  let N := derivedNeighborhood K L
  let R := closure (K.space \ N.space)
  let B := boundaryComplex 3 K
  let F := boundaryComplex 3 C
  let I := {e : Finset E // e ∈ L.faces ∧ e.card = 2 ∧ v ∈ e}
  let U := B.space ∪ ⋃ e : I, (splittingDisk K e.1 (hLK e.2.1)).space
  let _ : Finite C.faces := (graphDualCell_faces_finite K L v).to_subtype
  let _ : Finite B.faces := (boundaryComplex_faces_finite 3 K).to_subtype
  have hC : IsPLBall 3 C.space := hK.isPLBall_graphDualCell K L hLK hcard hv
  have hCN : C.space ⊆ N.space := graphDualCell_space_subset K L v
  have hCK : C.space ⊆ K.space := hCN.trans (derivedNeighborhood_space_subset K L)
  have hFC : F.space ⊆ C.space := boundaryComplex_space_subset 3 C
  have hCRF : C.space ∩ R ⊆ F.space := by
    rintro x ⟨hxC, hxR⟩
    apply inter_closure_sdiff_subset_boundaryComplex K C hK
      hC.isCombinatorialManifoldWithBoundary hCK
    exact ⟨hxC, closure_mono (sdiff_subset_sdiff_right hCN) hxR⟩
  have hfree : F.space \ U ⊆ C.space ∩ R := by
    rintro x ⟨hxF, hxU⟩
    have hxC := hFC hxF
    refine ⟨hxC, ?_⟩
    by_contra hxR
    let O := ⋃ w ∈ L.vertices \ {v}, (graphDualCell K L w).space
    have hfinV : L.vertices.Finite :=
      Set.Finite.preimage Finset.singleton_injective.injOn ((Set.toFinite K.faces).subset hLK)
    have hOc : IsClosed O :=
      (hfinV.subset sdiff_subset).isClosed_biUnion fun w hw =>
        (hK.isPLBall_graphDualCell K L hLK hcard hw.1).isPolyhedron.isClosed
    have hxO : x ∉ O := by
      intro hx
      obtain ⟨w, ⟨hw, hwv⟩, hxw⟩ := mem_iUnion₂.mp hx
      have hvw : v ≠ w := fun h => hwv h.symm
      by_cases he : {v, w} ∈ L.faces
      · apply hxU
        right
        refine mem_iUnion.mpr ⟨⟨{v, w}, he, by simp [hvw], by simp⟩, ?_⟩
        rw [← graphDualCell_space_inter K L hLK hcard hvw he]
        exact ⟨hxC, hxw⟩
      · have hi := graphDualCell_space_inter_eq_empty K L hLK hcard hv hw hvw he
        have hxI : x ∈ (graphDualCell K L v).space ∩ (graphDualCell K L w).space :=
          ⟨hxC, hxw⟩
        exact (hi ▸ hxI).elim
    have hnhds : C.space ∈ 𝓝[K.space] x := by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds (isClosed_closure.isOpen_compl.mem_nhds hxR),
        mem_nhdsWithin_of_mem_nhds (hOc.isOpen_compl.mem_nhds hxO)] with y hyK hyR hyO
      have hyN : y ∈ N.space := by
        by_contra hyN
        exact hyR (subset_closure ⟨hyK, hyN⟩)
      have hNU := iUnion_graphDualCell_space K L hLK
      have hyU : y ∈ ⋃ w ∈ L.vertices, (graphDualCell K L w).space := hNU.symm ▸ hyN
      obtain ⟨w, hw, hyw⟩ := mem_iUnion₂.mp hyU
      by_cases hwv : w = v
      · change y ∈ (graphDualCell K L v).space
        rwa [hwv] at hyw
      · exact (hyO (mem_iUnion₂.mpr ⟨w, ⟨hw, hwv⟩, hyw⟩)).elim
    have hxB := (mem_boundaryComplex_space_iff_of_space_mem_nhdsWithin K C hK
      hC.isCombinatorialManifoldWithBoundary hCK hxC hnhds).mp hxF
    exact hxU (Or.inl hxB)
  change C.space ∩ R = closure (F.space \ U)
  apply Subset.antisymm
  · rintro x ⟨hxC, hxR⟩
    have hR : R = ⋃ σ ∈ {σ : Finset E | σ ∈ K.faces ∧ σ ∉ L.faces},
        (derivedNeighborhoodCell K σ).space :=
      closure_space_sdiff_derivedNeighborhood_space (A := K) Subset.rfl hLK
    obtain ⟨σ, hσ, hxσ⟩ := mem_iUnion₂.mp (hR ▸ hxR)
    obtain ⟨u, huC, hxu⟩ := exists_face_mem_openSimplex C hxC
    have huK := derivedNeighborhood_faces_subset K L (graphDualCell_faces_subset K L v huC)
    have huσ := mem_faces_of_mem_openSimplex_of_mem_space
      (derivedNeighborhoodCell_faces_subset K σ) huK hxu hxσ
    obtain ⟨D, hD, hne, rfl⟩ := huK
    obtain ⟨hDN, hDA⟩ := (mem_graphDualCell_faces_iff_of_flag L (hLK hv) hD hne).mp huC
    have hDσ := (mem_derivedNeighborhoodCell_faces_iff_of_flag hσ.1 hD hne).mp huσ
    obtain ⟨a, ha, hatop⟩ := hD.exists_top hne
    obtain ⟨d, hd, hdne, hdv, had⟩ := (mem_dualCell_faces_iff K (hLK hv)).mp (hDA a ha)
    obtain ⟨s, hs, hstop⟩ := hd.exists_top hdne
    obtain ⟨t, ht, hst, htcard⟩ := hK.exists_face_superset_card_eq (hd.mem_faces hs)
    have hdt : ∀ r ∈ d, r ⊆ t := fun r hr => (hstop r hr).trans hst
    have hvt : ({v} : Finset E) ⊆ t := (hdv s hs).trans hst
    have hdtflag : IsFlag K (insert t d) := by
      refine ⟨?_, ?_⟩
      · intro r hr
        rcases Finset.mem_insert.mp hr with rfl | hr
        · exact ht
        · exact hd.mem_faces hr
      · intro r hr q hq
        rcases Finset.mem_insert.mp hr with hrt | hrd
        · rw [hrt]
          rcases Finset.mem_insert.mp hq with hqt | hqd
          · rw [hqt]
            exact Or.inl subset_rfl
          · exact Or.inr (hdt q hqd)
        · rcases Finset.mem_insert.mp hq with hqt | hqd
          · rw [hqt]
            exact Or.inl (hdt r hrd)
          · exact hd.subset_or_subset hrd hqd
    have hsmall : ∀ r ∈ insert t d, ({v} : Finset E) ⊆ r := by
      intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hr
      · exact hvt
      · exact hdv r hr
    let d' := insert {v} (insert t d)
    have hd' : IsFlag K d' := hdtflag.insert_of_subset (hLK hv) hsmall
    have hd'ne : d'.Nonempty := Finset.insert_nonempty _ _
    let a' := d'.image fun r => r.centroid ℝ id
    have ha'K : a' ∈ (barycentricSubdivision K).faces := ⟨d', hd', hd'ne, rfl⟩
    have ha'A : a' ∈ (dualCell K {v} (hLK hv)).faces := by
      apply (mem_dualCell_faces_iff_of_flag (hLK hv) hd' hd'ne).mpr
      intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hr
      · exact subset_rfl
      · exact hsmall r hr
    have haa' : a ⊆ a' := by
      rw [had]
      exact Finset.image_subset_image ((Finset.subset_insert _ _).trans
        (Finset.subset_insert _ _))
    have hDa' : ∀ r ∈ D, r ⊆ a' := fun r hr => (hatop r hr).trans haa'
    have hva' : v ∈ a' := by
      have h := Finset.mem_image_of_mem (fun r : Finset E => r.centroid ℝ id)
        (Finset.mem_insert_self {v} (insert t d))
      simpa only [Finset.centroid_singleton, id_eq] using h
    have hta' : t.centroid ℝ id ∈ a' :=
      Finset.mem_image_of_mem _ (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
    have hσa' : σ.centroid ℝ id ∈ a' := haa' (hDσ a ha)
    have hD' : IsFlag (barycentricSubdivision K) (insert a' D) := by
      refine ⟨?_, ?_⟩
      · intro r hr
        rcases Finset.mem_insert.mp hr with rfl | hr
        · exact ha'K
        · exact hD.mem_faces hr
      · intro r hr q hq
        rcases Finset.mem_insert.mp hr with rfl | hr <;>
          rcases Finset.mem_insert.mp hq with rfl | hq
        · exact Or.inl subset_rfl
        · exact Or.inr (hDa' q hq)
        · exact Or.inl (hDa' r hr)
        · exact hD.subset_or_subset hr hq
    have hD'ne : (insert a' D).Nonempty := Finset.insert_nonempty _ _
    let u' := (insert a' D).image fun r => r.centroid ℝ id
    have hu'K : u' ∈ (secondDerived K).faces := ⟨_, hD', hD'ne, rfl⟩
    have hu'C : u' ∈ C.faces := by
      apply (mem_graphDualCell_faces_iff_of_flag L (hLK hv) hD' hD'ne).mpr
      constructor
      · intro r hr
        rcases Finset.mem_insert.mp hr with rfl | hr
        · exact ⟨{v}, hv, by simpa only [Finset.centroid_singleton, id_eq] using hva'⟩
        · exact hDN r hr
      · intro r hr
        rcases Finset.mem_insert.mp hr with rfl | hr
        · exact ha'A
        · exact hDA r hr
    have hu'σ : u' ∈ (derivedNeighborhoodCell K σ).faces := by
      apply (mem_derivedNeighborhoodCell_faces_iff_of_flag hσ.1 hD' hD'ne).mpr
      intro r hr
      rcases Finset.mem_insert.mp hr with rfl | hr
      · exact hσa'
      · exact hDσ r hr
    have hu'B : u' ∉ (secondDerived B).faces := by
      intro huB
      have hcB : a'.centroid ℝ id ∈ B.space := by
        rw [← (secondDerived_isSubdivision B).space_eq]
        exact (secondDerived B).subset_space huB
          (Finset.mem_image_of_mem _ (Finset.mem_insert_self _ _))
      have ha'B : a' ∈ (barycentricSubdivision B).faces := by
        apply mem_faces_of_mem_openSimplex_of_mem_space
          (barycentricSubdivision_faces_subset (boundaryComplex_faces_subset 3 K)) ha'K
          (centroid_mem_openSimplex ((barycentricSubdivision K).nonempty_of_mem_faces ha'K))
        rwa [(barycentricSubdivision_isSubdivision B).space_eq]
      have hctB : t.centroid ℝ id ∈ B.space := by
        rw [← (barycentricSubdivision_isSubdivision B).space_eq]
        exact (barycentricSubdivision B).subset_space ha'B hta'
      have htB : t ∈ B.faces := mem_faces_of_mem_openSimplex_of_mem_space
        (boundaryComplex_faces_subset 3 K) ht (centroid_mem_openSimplex_of_mem_faces K t ht) hctB
      have hle := ((hK.mem_boundaryComplex_faces_iff K).mp htB).2.1
      omega
    have hu'E : ∀ e : I, u' ∉ (splittingDisk K e.1 (hLK e.2.1)).faces := by
      intro e huE
      have hsplit := (mem_splittingDisk_faces_iff_of_flag (hLK e.2.1) hD' hD'ne).mp huE
      have hvD : v ∈ (dualCell K e.1 (hLK e.2.1)).space :=
        (dualCell K e.1 (hLK e.2.1)).subset_space
          (hsplit.1 a' (Finset.mem_insert_self _ _)) hva'
      have hes : e.1 ⊆ {v} := subset_of_mem_dualCell_of_mem_convexHull K (hLK e.2.1)
        (hLK hv) hvD (by simp)
      have hle := Finset.card_le_card hes
      simp only [e.2.2.1, Finset.card_singleton] at hle
      omega
    have hopen : openSimplex u' ⊆ F.space \ U := by
      intro z hz
      have hzconv := openSimplex_subset_convexHull u' hz
      refine ⟨hCRF ⟨C.convexHull_subset_space hu'C hzconv, ?_⟩, ?_⟩
      · rw [hR]
        exact mem_iUnion₂.mpr ⟨σ, hσ, (derivedNeighborhoodCell K σ).convexHull_subset_space
          hu'σ hzconv⟩
      · rintro (hzB | hzE)
        · apply hu'B
          apply mem_faces_of_mem_openSimplex_of_mem_space
            (secondDerived_faces_subset (boundaryComplex_faces_subset 3 K)) hu'K hz
          rwa [(secondDerived_isSubdivision B).space_eq]
        · obtain ⟨e, hze⟩ := mem_iUnion.mp hzE
          exact hu'E e (mem_faces_of_mem_openSimplex_of_mem_space
            (splittingDisk_faces_subset K (hLK e.2.1)) hu'K hz hze)
    have hu'sub : (D.image fun r => r.centroid ℝ id) ⊆ u' :=
      Finset.image_subset_image (Finset.subset_insert _ _)
    exact closure_mono hopen (convexHull_subset_closure_openSimplex (hD'ne.image _)
      (convexHull_mono (Finset.coe_subset.mpr hu'sub) (openSimplex_subset_convexHull _ hxu)))
  · exact closure_minimal hfree (hC.isPolyhedron.isClosed.inter isClosed_closure)

end DifferentialGeometry.Topology.PiecewiseLinear
