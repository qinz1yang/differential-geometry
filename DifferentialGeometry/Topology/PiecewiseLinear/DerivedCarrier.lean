import DifferentialGeometry.Topology.PiecewiseLinear.Derived
import DifferentialGeometry.Topology.PiecewiseLinear.SimplicialMap

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem carrierFace_centroid {K : Geometry.SimplicialComplex ℝ E} {s : Finset E}
    (hs : s ∈ K.faces) : carrierFace K (s.centroid ℝ id) = s := by
  have hx := centroid_mem_openSimplex (K.nonempty_of_mem_faces hs)
  have hxK := K.convexHull_subset_space hs (openSimplex_subset_convexHull s hx)
  exact face_eq_of_mem_openSimplex K (carrierFace_mem hxK) hs
    (mem_openSimplex_carrierFace hxK) hx

open Classical in
theorem carrierFace_mem_of_mem_barycentricSubdivision
    {K : Geometry.SimplicialComplex ℝ E} {f : Finset E}
    (hf : f ∈ (barycentricSubdivision K).faces) {x : E} (hx : x ∈ f) :
    carrierFace K x ∈ K.faces := by
  obtain ⟨d, hd, _, rfl⟩ := hf
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
  rw [carrierFace_centroid (hd.mem_faces hs)]
  exact hd.mem_faces hs

open Classical in
theorem centroid_carrierFace_of_mem_barycentricSubdivision
    {K : Geometry.SimplicialComplex ℝ E} {f : Finset E}
    (hf : f ∈ (barycentricSubdivision K).faces) {x : E} (hx : x ∈ f) :
    (carrierFace K x).centroid ℝ id = x := by
  obtain ⟨d, hd, _, rfl⟩ := hf
  obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hx
  rw [carrierFace_centroid (hd.mem_faces hs)]

open Classical in
theorem exists_face_superset_carrierFaces_of_mem_barycentricSubdivision
    {K : Geometry.SimplicialComplex ℝ E} {f : Finset E}
    (hf : f ∈ (barycentricSubdivision K).faces) :
    ∃ s ∈ K.faces, ∀ x ∈ f, carrierFace K x ⊆ s := by
  obtain ⟨d, hd, hne, rfl⟩ := hf
  obtain ⟨s, hs, htop⟩ := hd.exists_top hne
  refine ⟨s, hd.mem_faces hs, ?_⟩
  intro x hx
  obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hx
  rw [carrierFace_centroid (hd.mem_faces ht)]
  exact htop t ht

open Classical in
theorem pair_centroid_mem_barycentricSubdivision
    {K : Geometry.SimplicialComplex ℝ E} {s t : Finset E}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces) (hst : s ⊆ t) :
    {s.centroid ℝ id, t.centroid ℝ id} ∈ (barycentricSubdivision K).faces := by
  refine ⟨{s, t}, ?_, Finset.insert_nonempty _ _, ?_⟩
  · constructor
    · intro u hu
      rcases Finset.mem_insert.mp hu with rfl | hu
      · exact hs
      · exact (Finset.mem_singleton.mp hu).symm ▸ ht
    · intro u hu v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hu hv
      rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
      · exact Or.inl (Finset.Subset.refl _)
      · exact Or.inl hst
      · exact Or.inr hst
      · exact Or.inl (Finset.Subset.refl _)
  · rw [Finset.image_insert, Finset.image_singleton]

end DifferentialGeometry.Topology.PiecewiseLinear
