import DifferentialGeometry.Topology.PiecewiseLinear.Barycentric

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [AddCommGroup E] [Module ℝ E]

def IsSubdivision (K' K : Geometry.SimplicialComplex ℝ E) : Prop :=
  K'.space = K.space ∧
    ∀ s ∈ K'.faces, ∃ t ∈ K.faces, convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E)

namespace IsSubdivision

variable {K K' K'' : Geometry.SimplicialComplex ℝ E}

theorem refl (K : Geometry.SimplicialComplex ℝ E) : IsSubdivision K K :=
  ⟨rfl, fun s hs => ⟨s, hs, subset_rfl⟩⟩

theorem space_eq (h : IsSubdivision K' K) : K'.space = K.space := h.1

theorem exists_face_subset (h : IsSubdivision K' K) {s : Finset E} (hs : s ∈ K'.faces) :
    ∃ t ∈ K.faces, convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E) := h.2 s hs

theorem trans (h₁ : IsSubdivision K'' K') (h₂ : IsSubdivision K' K) : IsSubdivision K'' K := by
  refine ⟨h₁.1.trans h₂.1, fun s hs => ?_⟩
  obtain ⟨t, ht, hst⟩ := h₁.exists_face_subset hs
  obtain ⟨u, hu, htu⟩ := h₂.exists_face_subset ht
  exact ⟨u, hu, hst.trans htu⟩

theorem convexHull_subset_of_mem_openSimplex (h : IsSubdivision K' K) {t : Finset E}
    (ht : t ∈ K.faces) {s : Finset E} (hs : s ∈ K'.faces) {x : E} (hx : x ∈ openSimplex s)
    (hxt : x ∈ convexHull ℝ (t : Set E)) :
    convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E) := by
  classical
  obtain ⟨t', ht', hst'⟩ := h.exists_face_subset hs
  have hx' : x ∈ convexHull ℝ ((t ∩ t' : Finset E) : Set E) := by
    rw [Finset.coe_inter]
    exact K.inter_subset_convexHull ht ht' ⟨hxt, hst' (openSimplex_subset_convexHull s hx)⟩
  have hsub := subset_convexHull_of_mem_openSimplex (K.indep ht') Finset.inter_subset_right
    ((subset_convexHull ℝ _).trans hst') hx hx'
  exact (convexHull_min hsub (convex_convexHull ℝ _)).trans
    (convexHull_mono (Finset.coe_subset.mpr Finset.inter_subset_left))

theorem convexHull_eq_biUnion (h : IsSubdivision K' K) {t : Finset E} (ht : t ∈ K.faces) :
    convexHull ℝ (t : Set E) =
      ⋃ s ∈ {s ∈ K'.faces | convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E)},
        convexHull ℝ (s : Set E) := by
  apply Subset.antisymm
  · intro x hx
    have hx' : x ∈ K'.space := h.1 ▸ K.convexHull_subset_space ht hx
    obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex K' hx'
    exact mem_biUnion (x := s) ⟨hs, h.convexHull_subset_of_mem_openSimplex ht hs hxs hx⟩
      (openSimplex_subset_convexHull s hxs)
  · exact iUnion₂_subset fun s hs => hs.2

theorem exists_face_subset_of_mem (h : IsSubdivision K' K) {t : Finset E} (ht : t ∈ K.faces)
    {x : E} (hx : x ∈ convexHull ℝ (t : Set E)) :
    ∃ s ∈ K'.faces, x ∈ convexHull ℝ (s : Set E) ∧
      convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E) := by
  have hx' : x ∈ K'.space := h.1 ▸ K.convexHull_subset_space ht hx
  obtain ⟨s, hs, hxs⟩ := exists_face_mem_openSimplex K' hx'
  exact ⟨s, hs, openSimplex_subset_convexHull s hxs,
    h.convexHull_subset_of_mem_openSimplex ht hs hxs hx⟩

end IsSubdivision

end DifferentialGeometry.Topology.PiecewiseLinear
