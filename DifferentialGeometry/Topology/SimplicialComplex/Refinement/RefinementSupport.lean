import DifferentialGeometry.Topology.SimplicialComplex.Refinement.RefinementRestriction

namespace DifferentialGeometry.Topology.Engulfing

open Set _root_.Geometry

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [DecidableEq E] in
theorem simplicialRefines.convexHull_subset_old_face_of_centroid_mem
    {P K : SimplicialComplex ℝ E} (href : simplicialRefines P K)
    {s t : Finset E} (hs : s ∈ P.faces) (ht : t ∈ K.faces)
    (hc : s.centroid ℝ id ∈ convexHull ℝ (t : Set E)) :
    convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E) := by
  classical
  let u := s.filter (fun x => x ∈ convexHull ℝ (t : Set E))
  have hcu : s.centroid ℝ id ∈ convexHull ℝ (u : Set E) := by
    rw [← href.convexHull_inter_old_face hs ht]
    exact ⟨s.centroid_mem_convexHull (P.nonempty_of_mem_faces hs), hc⟩
  have hu : u.Nonempty := Finset.coe_nonempty.mp (convexHull_nonempty_iff.mp ⟨_, hcu⟩)
  have hsu := face_subset_of_centroid_mem P hs
    (P.down_closed hs (Finset.filter_subset _ _) hu) hcu
  apply convexHull_min _ (convex_convexHull ℝ _)
  intro x hx
  exact (Finset.mem_filter.mp (hsu hx)).2

omit [DecidableEq E] in
theorem simplicialRefines.exists_old_face_of_convexHull_subset
    {P K H : SimplicialComplex ℝ E} (href : simplicialRefines P K)
    (hHK : H.faces ⊆ K.faces) {s : Finset E} (hs : s ∈ P.faces)
    (hH : convexHull ℝ (s : Set E) ⊆ H.space) :
    ∃ t ∈ H.faces, convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E) := by
  classical
  obtain ⟨t, ht, hct⟩ := SimplicialComplex.mem_space_iff.mp
    (hH (s.centroid_mem_convexHull (P.nonempty_of_mem_faces hs)))
  exact ⟨t, ht, href.convexHull_subset_old_face_of_centroid_mem hs (hHK ht) hct⟩

omit [DecidableEq E] in
theorem simplicialRefines.convexHull_subset_or_of_subset_union
    {P K H J : SimplicialComplex ℝ E} (href : simplicialRefines P K)
    (hHK : H.faces ⊆ K.faces) (hJK : J.faces ⊆ K.faces)
    {s : Finset E} (hs : s ∈ P.faces)
    (hH : convexHull ℝ (s : Set E) ⊆ H.space ∪ J.space) :
    convexHull ℝ (s : Set E) ⊆ H.space ∨ convexHull ℝ (s : Set E) ⊆ J.space := by
  classical
  have hc := hH (s.centroid_mem_convexHull (P.nonempty_of_mem_faces hs))
  rcases hc with hc | hc
  · obtain ⟨t, ht, hct⟩ := SimplicialComplex.mem_space_iff.mp hc
    exact Or.inl ((href.convexHull_subset_old_face_of_centroid_mem hs (hHK ht) hct).trans
      (H.convexHull_subset_space ht))
  · obtain ⟨t, ht, hct⟩ := SimplicialComplex.mem_space_iff.mp hc
    exact Or.inr ((href.convexHull_subset_old_face_of_centroid_mem hs (hJK ht) hct).trans
      (J.convexHull_subset_space ht))

omit [DecidableEq E] in
theorem simplicialRefines.convexHull_subset_or_old_face
    {P K H : SimplicialComplex ℝ E} (href : simplicialRefines P K)
    (hHK : H.faces ⊆ K.faces) {s t : Finset E} (hs : s ∈ P.faces) (ht : t ∈ K.faces)
    (hH : convexHull ℝ (s : Set E) ⊆ H.space ∪ convexHull ℝ (t : Set E)) :
    convexHull ℝ (s : Set E) ⊆ H.space ∨
      convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E) := by
  classical
  have hc := hH (s.centroid_mem_convexHull (P.nonempty_of_mem_faces hs))
  rcases hc with hc | hc
  · obtain ⟨u, hu, hcu⟩ := SimplicialComplex.mem_space_iff.mp hc
    exact Or.inl ((href.convexHull_subset_old_face_of_centroid_mem hs (hHK hu) hcu).trans
      (H.convexHull_subset_space hu))
  · exact Or.inr (href.convexHull_subset_old_face_of_centroid_mem hs ht hc)

end DifferentialGeometry.Topology.Engulfing
