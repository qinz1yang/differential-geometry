import DifferentialGeometry.Topology.PiecewiseLinear.Gluing

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def subcomplexGeneratedBy (K : Geometry.SimplicialComplex ℝ E) (A : Set (Finset E)) :
    Geometry.SimplicialComplex ℝ E where
  faces := {s | ∃ t ∈ K.faces ∩ A, s ⊆ t ∧ s.Nonempty}
  isRelLowerSet_faces := by
    rintro s ⟨t, ht, hst, hs⟩
    exact ⟨hs, fun u hus hu => ⟨t, ht, hus.trans hst, hu⟩⟩
  indep hs := K.indep (K.down_closed hs.choose_spec.1.1 hs.choose_spec.2.1 hs.choose_spec.2.2)
  inter_subset_convexHull hs ht := K.inter_subset_convexHull
    (K.down_closed hs.choose_spec.1.1 hs.choose_spec.2.1 hs.choose_spec.2.2)
    (K.down_closed ht.choose_spec.1.1 ht.choose_spec.2.1 ht.choose_spec.2.2)

theorem subcomplexGeneratedBy_faces_subset (K : Geometry.SimplicialComplex ℝ E) (A : Set (Finset E)) :
    (subcomplexGeneratedBy K A).faces ⊆ K.faces := by
  rintro s ⟨t, ht, hst, hs⟩
  exact K.down_closed ht.1 hst hs

theorem subcomplexGeneratedBy_faces_finite (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (A : Set (Finset E)) : (subcomplexGeneratedBy K A).faces.Finite :=
  (Set.toFinite K.faces).subset (subcomplexGeneratedBy_faces_subset K A)

theorem subcomplexGeneratedBy_space (K : Geometry.SimplicialComplex ℝ E) (A : Set (Finset E)) :
    (subcomplexGeneratedBy K A).space = ⋃ t ∈ K.faces ∩ A, convexHull ℝ (t : Set E) := by
  ext x
  constructor
  · intro hx
    obtain ⟨s, ⟨t, ht, hst, -⟩, hxs⟩ := (subcomplexGeneratedBy K A).mem_space_iff.mp hx
    exact mem_iUnion₂.mpr ⟨t, ht, convexHull_mono (Finset.coe_subset.mpr hst) hxs⟩
  · intro hx
    obtain ⟨t, ht, hxt⟩ := mem_iUnion₂.mp hx
    exact (subcomplexGeneratedBy K A).convexHull_subset_space
      ⟨t, ht, Finset.Subset.rfl, K.nonempty_of_mem_faces ht.1⟩ hxt

theorem exists_face_superset_card_eq_subcomplexGeneratedBy
    (K : Geometry.SimplicialComplex ℝ E) (A : Set (Finset E)) {n : ℕ}
    (hcard : ∀ t ∈ K.faces ∩ A, t.card = n) {s : Finset E}
    (hs : s ∈ (subcomplexGeneratedBy K A).faces) :
    ∃ t ∈ (subcomplexGeneratedBy K A).faces, s ⊆ t ∧ t.card = n := by
  obtain ⟨t, ht, hst, -⟩ := hs
  exact ⟨t, ⟨t, ht, Finset.Subset.rfl, K.nonempty_of_mem_faces ht.1⟩, hst, hcard t ht⟩

theorem mem_subcomplexGeneratedBy_faces_of_card
    (K : Geometry.SimplicialComplex ℝ E) (A : Set (Finset E)) {n : ℕ}
    (hcard : ∀ t ∈ K.faces ∩ A, t.card = n) {s : Finset E} (hscard : s.card = n) :
    s ∈ (subcomplexGeneratedBy K A).faces ↔ s ∈ K.faces ∩ A := by
  constructor
  · rintro ⟨t, ht, hst, -⟩
    have heq : s = t := Finset.eq_of_subset_of_card_le hst (by rw [hcard t ht, hscard])
    exact heq.symm ▸ ht
  · intro hs
    exact ⟨s, hs, Finset.Subset.rfl, K.nonempty_of_mem_faces hs.1⟩

end DifferentialGeometry.Topology.PiecewiseLinear
