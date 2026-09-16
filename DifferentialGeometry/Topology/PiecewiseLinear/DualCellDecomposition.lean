import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodCells
import DifferentialGeometry.Topology.PiecewiseLinear.SubcomplexBallGluing

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem union_mem_faces_of_nonempty_dualCell_inter
    (K : Geometry.SimplicialComplex ℝ E) {s t : Finset E}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces)
    (hne : ((dualCell K s hs).space ∩ (dualCell K t ht).space).Nonempty) :
    s ∪ t ∈ K.faces := by
  obtain ⟨x, hxs, hxt⟩ := hne
  obtain ⟨u, hu, hxu⟩ := exists_face_mem_openSimplex (dualCell K s hs) hxs
  have hut := mem_faces_of_mem_openSimplex_of_mem_space (dualCell_faces_subset K ht)
    (dualCell_faces_subset K hs hu) hxu hxt
  obtain ⟨d, hd, hdne, rfl⟩ := dualCell_faces_subset K hs hu
  have hsd := (mem_dualCell_faces_iff_of_flag hs hd hdne).mp hu
  have htd := (mem_dualCell_faces_iff_of_flag ht hd hdne).mp hut
  obtain ⟨e, he⟩ := hdne
  exact K.down_closed (hd.mem_faces he) (Finset.union_subset (hsd e he) (htd e he))
    ((K.nonempty_of_mem_faces hs).mono Finset.subset_union_left)

open Classical in
theorem disjoint_dualCell_space (K : Geometry.SimplicialComplex ℝ E) {s t : Finset E}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hst : s ∪ t ∉ K.faces) :
    Disjoint (dualCell K s hs).space (dualCell K t ht).space :=
  disjoint_left.mpr fun x hxs hxt =>
    hst (union_mem_faces_of_nonempty_dualCell_inter K hs ht ⟨x, hxs, hxt⟩)

open Classical in
theorem dualCell_space_eq_singleton_of_card (K : Geometry.SimplicialComplex ℝ E)
    {s : Finset E} (hs : s ∈ K.faces) (hcard : ∀ t ∈ K.faces, t.card ≤ s.card) :
    (dualCell K s hs).space = {s.centroid ℝ id} := by
  have hsub : (dualCell K s hs).space ⊆ K.space := by
    rw [← (barycentricSubdivision_isSubdivision K).space_eq]
    exact space_mono_of_faces_subset (dualCell_faces_subset K hs)
  have h := dualCell_space_inter K K Subset.rfl hs hcard
  rwa [inter_eq_left.mpr hsub] at h

open Classical in
theorem finite_inter_dualCell_space_inter (K : Geometry.SimplicialComplex ℝ E)
    {s t u : Finset E} (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hu : u ∈ K.faces)
    (hcard : ∀ v ∈ K.faces, v.card ≤ (s ∪ t ∪ u).card) :
    ((dualCell K s hs).space ∩ (dualCell K t ht).space ∩ (dualCell K u hu).space).Finite := by
  by_cases hst : s ∪ t ∈ K.faces
  · rw [dualCell_space_inter_eq_dualCell K hs ht hst]
    by_cases hstu : s ∪ t ∪ u ∈ K.faces
    · rw [dualCell_space_inter_eq_dualCell K hst hu hstu,
        dualCell_space_eq_singleton_of_card K hstu hcard]
      exact finite_singleton _
    · rw [(disjoint_dualCell_space K hst hu hstu).inter_eq]
      exact finite_empty
  · rw [(disjoint_dualCell_space K hs ht hst).inter_eq, empty_inter]
    exact finite_empty

open Classical in
theorem iUnion_dualCell_singleton_space (K : Geometry.SimplicialComplex ℝ E) :
    (⋃ v : {v : E // ({v} : Finset E) ∈ K.faces}, (dualCell K {v.1} v.2).space) = K.space := by
  apply Subset.antisymm
  · apply iUnion_subset
    intro v
    rw [← (barycentricSubdivision_isSubdivision K).space_eq]
    exact space_mono_of_faces_subset (dualCell_faces_subset K v.2)
  · intro x hx
    have hx' : x ∈ (barycentricSubdivision K).space :=
      (barycentricSubdivision_isSubdivision K).space_eq.symm ▸ hx
    obtain ⟨u, ⟨d, hd, hdne, rfl⟩, hxu⟩ := (barycentricSubdivision K).mem_space_iff.mp hx'
    obtain ⟨s, hs, hbot⟩ := hd.exists_bot hdne
    obtain ⟨v, hvs⟩ := K.nonempty_of_mem_faces (hd.mem_faces hs)
    have hv : {v} ∈ K.faces := K.down_closed (hd.mem_faces hs)
      (Finset.singleton_subset_iff.mpr hvs) (Finset.singleton_nonempty v)
    refine mem_iUnion.mpr ⟨⟨v, hv⟩, (dualCell K {v} hv).convexHull_subset_space ?_ hxu⟩
    exact (mem_dualCell_faces_iff_of_flag hv hd hdne).mpr fun t ht =>
      Finset.singleton_subset_iff.mpr (hbot t ht hvs)

open Classical in
theorem IsCombinatorialManifoldWithBoundary.isPLBall_inter_dualCell_singleton
    [FiniteDimensional ℝ E] {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 2) K) {v w : E}
    (hv : {v} ∈ K.faces) (hw : {w} ∈ K.faces) (hvw : v ≠ w) (hpair : {v, w} ∈ K.faces) :
    IsPLBall (n + 1) ((dualCell K {v} hv).space ∩ (dualCell K {w} hw).space) := by
  have hpair' : {v} ∪ {w} ∈ K.faces := by simpa only [Finset.singleton_union] using hpair
  rw [dualCell_space_inter_eq_dualCell K hv hw hpair']
  simpa only [Finset.singleton_union, Nat.add_sub_cancel] using
    hK.isPLBall_dualCell K hpair (k := 1) (by simp [hvw]) (by omega)

open Classical in
theorem IsCombinatorialManifoldWithBoundary.inter_dualCell_singleton_subset_boundaryComplex
    [FiniteDimensional ℝ E] {n : ℕ} (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 2) K) {v w : E}
    (hv : {v} ∈ K.faces) (hw : {w} ∈ K.faces) (hvw : v ≠ w) (hpair : {v, w} ∈ K.faces) :
    (dualCell K {v} hv).space ∩ (dualCell K {w} hw).space ⊆
      (boundaryComplex (n + 2) (dualCell K {v} hv)).space := by
  let _ : Finite (dualCell K {v} hv).faces := (dualCell_faces_finite K hv).to_subtype
  let _ : Finite (dualCell K {w} hw).faces := (dualCell_faces_finite K hw).to_subtype
  exact PiecewiseLinear.inter_subset_boundaryComplex_of_isPLBall (PiecewiseLinear.barycentricSubdivision K)
    (dualCell K {v} hv) (dualCell K {w} hw) hK.barycentricSubdivision
    (hK.isPLBall_dualCell K hv (k := 0) (Finset.card_singleton v) (by omega))
    (hK.isPLBall_dualCell K hw (k := 0) (Finset.card_singleton w) (by omega))
    (dualCell_faces_subset K hv) (dualCell_faces_subset K hw)
    (hK.isPLBall_inter_dualCell_singleton K hv hw hvw hpair)

open Classical in
theorem IsCombinatorialManifoldWithBoundary.finite_inter_dualCell_singleton_inter
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K) {u v w : E}
    (hu : {u} ∈ K.faces) (hv : {v} ∈ K.faces) (hw : {w} ∈ K.faces)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w) :
    ((dualCell K {u} hu).space ∩ (dualCell K {v} hv).space ∩
      (dualCell K {w} hw).space).Finite := by
  apply finite_inter_dualCell_space_inter K hu hv hw
  intro t ht
  simpa [huv, huw, hvw] using hK.card_le K ht

open Classical in
theorem IsCombinatorialManifoldWithBoundary.finite_inter_dualCell_singleton_iUnion
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K)
    (d : Finset {v : E // ({v} : Finset E) ∈ K.faces})
    {u v : {v : E // ({v} : Finset E) ∈ K.faces}}
    (huv : u ≠ v) (hu : u ∉ d) (hv : v ∉ d) :
    ((dualCell K {u.1} u.2).space ∩ (dualCell K {v.1} v.2).space ∩
      (⋃ w ∈ d, (dualCell K {w.1} w.2).space)).Finite := by
  have hfinite : ∀ w ∈ d, ((dualCell K {u.1} u.2).space ∩
      (dualCell K {v.1} v.2).space ∩ (dualCell K {w.1} w.2).space).Finite := by
    intro w hw
    exact hK.finite_inter_dualCell_singleton_inter K u.2 v.2 w.2
      (fun heq => huv (Subtype.ext heq))
      (fun heq => hu ((Subtype.ext heq : u = w).symm ▸ hw))
      (fun heq => hv ((Subtype.ext heq : v = w).symm ▸ hw))
  have h := d.finite_toSet.biUnion hfinite
  simpa only [inter_iUnion, Finset.mem_coe] using h

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_boundary_arcs_cover_inter_dualCell_iUnion
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary 2 K)
    (d : Finset {v : E // ({v} : Finset E) ∈ K.faces})
    {v : {v : E // ({v} : Finset E) ∈ K.faces}} (hv : v ∉ d) :
    ∃ e : Finset {v : E // ({v} : Finset E) ∈ K.faces}, e ⊆ d ∧
      (∀ w ∈ e, IsPLBall 1 ((dualCell K {v.1} v.2).space ∩ (dualCell K {w.1} w.2).space) ∧
        (dualCell K {v.1} v.2).space ∩ (dualCell K {w.1} w.2).space ⊆
          (boundaryComplex 2 (dualCell K {v.1} v.2)).space) ∧
      (⋃ w ∈ e, (dualCell K {v.1} v.2).space ∩ (dualCell K {w.1} w.2).space) =
        (dualCell K {v.1} v.2).space ∩ (⋃ w ∈ d, (dualCell K {w.1} w.2).space) := by
  let e := d.filter (fun w => ({v.1, w.1} : Finset E) ∈ K.faces)
  refine ⟨e, Finset.filter_subset _ _, ?_, ?_⟩
  · intro w hw
    obtain ⟨hwd, hpair⟩ := Finset.mem_filter.mp hw
    have hvw : v.1 ≠ w.1 := fun heq => hv ((Subtype.ext heq : v = w).symm ▸ hwd)
    exact ⟨hK.isPLBall_inter_dualCell_singleton K v.2 w.2 hvw hpair,
      hK.inter_dualCell_singleton_subset_boundaryComplex K v.2 w.2 hvw hpair⟩
  · apply Subset.antisymm
    · intro x hx
      obtain ⟨w, hx⟩ := mem_iUnion.mp hx
      obtain ⟨hw, hxv, hxw⟩ := mem_iUnion.mp hx
      exact ⟨hxv, mem_iUnion.mpr ⟨w, mem_iUnion.mpr ⟨(Finset.mem_filter.mp hw).1, hxw⟩⟩⟩
    · rintro x ⟨hxv, hx⟩
      obtain ⟨w, hx⟩ := mem_iUnion.mp hx
      obtain ⟨hw, hxw⟩ := mem_iUnion.mp hx
      have hpair : ({v.1, w.1} : Finset E) ∈ K.faces := by
        simpa only [Finset.singleton_union] using
          union_mem_faces_of_nonempty_dualCell_inter K v.2 w.2 ⟨x, hxv, hxw⟩
      exact mem_iUnion.mpr ⟨w, mem_iUnion.mpr ⟨Finset.mem_filter.mpr ⟨hw, hpair⟩, hxv, hxw⟩⟩
end DifferentialGeometry.Topology.PiecewiseLinear
