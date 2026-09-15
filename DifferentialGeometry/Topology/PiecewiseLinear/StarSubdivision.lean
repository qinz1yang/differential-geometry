import DifferentialGeometry.Topology.PiecewiseLinear.Subcomplex
import DifferentialGeometry.Topology.PiecewiseLinear.OpenStar
import DifferentialGeometry.Topology.PiecewiseLinear.LinkRadial

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem closedStar_subset_biUnion_of_mem_convexHull
    (K : Geometry.SimplicialComplex ℝ E) {s : Finset E} (hs : s ∈ K.faces)
    {x : E} (hx : x ∈ convexHull ℝ (s : Set E)) :
    closedStar K x ⊆ ⋃ v ∈ s, closedStar K v := by
  classical
  intro y hy
  obtain ⟨t, ⟨ht, hxt⟩, hyt⟩ := mem_iUnion₂.mp hy
  have hxst : x ∈ convexHull ℝ ((s ∩ t : Finset E) : Set E) := by
    rw [Finset.coe_inter]
    exact K.inter_subset_convexHull hs ht ⟨hx, hxt⟩
  have hne : (s ∩ t).Nonempty := by
    by_contra hne
    rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.coe_empty, convexHull_empty] at hxst
    exact hxst
  obtain ⟨v, hv⟩ := hne
  have hvs := (Finset.mem_inter.mp hv).1
  have hvt := (Finset.mem_inter.mp hv).2
  exact mem_iUnion₂.mpr ⟨v, hvs,
    mem_iUnion₂.mpr ⟨t, ⟨ht, subset_convexHull ℝ _ hvt⟩, hyt⟩⟩

theorem IsSubdivision.closedStars_subset_closedStars
    {R K : Geometry.SimplicialComplex ℝ E} (hR : IsSubdivision R K)
    {s t : Finset E} (ht : t ∈ K.faces)
    (hst : convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E)) :
    (⋃ v ∈ s, closedStar R v) ⊆ ⋃ w ∈ t, closedStar K w := by
  intro y hy
  obtain ⟨v, hv, hyv⟩ := mem_iUnion₂.mp hy
  exact closedStar_subset_biUnion_of_mem_convexHull K ht (hst (subset_convexHull ℝ _ hv))
    (closedStar_subset_of_isSubdivision hR v hyv)

theorem IsSubdivision.closedStars_subset_cover
    {R K : Geometry.SimplicialComplex ℝ E} (hR : IsSubdivision R K)
    {ι : Type*} {U : ι → Set E}
    (hK : ∀ t ∈ K.faces, ∃ i, (⋃ v ∈ t, closedStar K v) ⊆ U i) :
    ∀ s ∈ R.faces, ∃ i, (⋃ v ∈ s, closedStar R v) ⊆ U i := by
  intro s hs
  obtain ⟨t, ht, hst⟩ := hR.exists_face_subset hs
  obtain ⟨i, hi⟩ := hK t ht
  exact ⟨i, (hR.closedStars_subset_closedStars ht hst).trans hi⟩

theorem exists_isSubdivision_subcomplexes_closedStars_subset_openStar [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {J : Type*} [Finite J] (Q : J → Set E) (hQ : ∀ j, IsPolyhedron (Q j))
    (hQK : ∀ j, Q j ⊆ K.space) :
    ∃ R : Geometry.SimplicialComplex ℝ E, IsSubdivision R K ∧ R.faces.Finite ∧
      (∀ j, (restrict R (Q j)).space = Q j) ∧
      ∀ s ∈ R.faces, ∃ v ∈ K.vertices, (⋃ w ∈ s, closedStar R w) ⊆ openStar K v := by
  have hcover : K.space ⊆ ⋃ v : K.vertices, openStar K v := by
    intro x hx
    obtain ⟨v, hv, hxv⟩ := exists_vertex_mem_openStar K hx
    exact mem_iUnion.mpr ⟨⟨v, hv⟩, hxv⟩
  obtain ⟨R, hR, hfinite, hQR, hstars⟩ :=
    exists_isSubdivision_subcomplexes_closedStars_subset_cover K Q hQ hQK
      (fun v : K.vertices => openStar K v) (fun v => isOpen_preimage_openStar K v) hcover
  exact ⟨R, hR, hfinite, hQR, fun s hs => by
    obtain ⟨v, hv⟩ := hstars s hs
    exact ⟨v, v.property, hv⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
