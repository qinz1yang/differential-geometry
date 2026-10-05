import DifferentialGeometry.Topology.PiecewiseLinear.ConeComplex
import DifferentialGeometry.Topology.PiecewiseLinear.Derived
import DifferentialGeometry.Topology.PiecewiseLinear.LinkSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.Polyhedra
import DifferentialGeometry.Topology.PiecewiseLinear.Triangulation

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem closedStar_subset_of_isSubdivision {K' K : Geometry.SimplicialComplex ℝ E}
    (h : IsSubdivision K' K) (x : E) : closedStar K' x ⊆ closedStar K x := by
  intro y hy
  obtain ⟨t, ⟨ht, hxt⟩, hyt⟩ := mem_iUnion₂.mp hy
  obtain ⟨s, hs, hsub⟩ := h.exists_face_subset ht
  exact mem_iUnion₂.mpr ⟨s, ⟨hs, hsub hxt⟩, hsub hyt⟩

theorem exists_isPLHomeomorphOn_geometricLink_of_isConeBase [FiniteDimensional ℝ E]
    [DecidableEq E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {u : E}
    (hu : {u} ∈ K.faces) (J : Geometry.SimplicialComplex ℝ E) [Finite J.faces]
    (hJ : IsConeBase u J)
    (hstar : ∀ x ∈ closedStar K u, x ≠ u →
      ∃ τ ∈ J.faces, x ∈ convexHull ℝ ((insert u τ : Finset E) : Set E))
    (hseg : ∀ y ∈ J.space, ∀ t : ℝ, 0 < t → t ≤ 1 → u + t • (y - u) ∈ K.space) :
    ∃ f : E → E, IsPLHomeomorphOn f (SimplicialComplex.geometricLink K {u}).space J.space := by
  classical
  have huK : u ∈ K.space := K.convexHull_subset_space hu (subset_convexHull ℝ _ (by simp))
  have hQ : ∀ τ : J.faces,
      IsPolyhedron (convexHull ℝ ((insert u (τ : Finset E) : Finset E) : Set E)) := by
    intro τ
    refine isPolyhedron_convexHull_of_affineIndependent _ ?_
    have h : AffineIndependent ℝ ((↑) : (insert u ((τ : Finset E) : Set E) : Set E) → E) :=
      hJ.indep τ τ.2
    rwa [← Finset.coe_insert] at h
  have hQK : ∀ τ : J.faces,
      convexHull ℝ ((insert u (τ : Finset E) : Finset E) : Set E) ⊆ K.space := by
    intro τ x hx
    have huτ : u ∉ (τ : Finset E) := hJ.notMem_face τ.2
    rcases exists_combo_of_mem_convexHull_insert huτ hx with rfl | ⟨z, hz, s, hs0, hs1, rfl⟩
    · exact huK
    · exact hseg z (J.convexHull_subset_space τ.2 hz) s hs0 hs1
  obtain ⟨K', hK', hfin, hQ'⟩ := exists_isSubdivision_subcomplexes K
    (fun τ : J.faces => convexHull ℝ ((insert u (τ : Finset E) : Finset E) : Set E)) hQ hQK
  have : Finite K'.faces := hfin.to_subtype
  have hu' : {u} ∈ K'.faces := hK'.singleton_mem hu
  have hadapt : ∀ σ ∈ (SimplicialComplex.geometricLink K' {u}).faces, ∃ τ ∈ J.faces, ∀ w ∈ σ,
      ∃ s : ℝ, 0 < s ∧ u + s • (w - u) ∈ convexHull ℝ (τ : Set E) := by
    intro σ hσ
    obtain ⟨hσne, huσ, hins⟩ := (SimplicialComplex.mem_geometricLink_singleton K' u σ).mp hσ
    obtain ⟨x, hx⟩ : ∃ x, x ∈ openSimplex (insert u σ) :=
      ⟨_, centroid_mem_openSimplex (Finset.insert_nonempty u σ)⟩
    have hxconv : x ∈ convexHull ℝ ((insert u σ : Finset E) : Set E) :=
      openSimplex_subset_convexHull _ hx
    have hxu : x ≠ u := by
      intro hxu
      have hsub := face_subset_of_mem_openSimplex_of_mem_convexHull K' hins hu' hx
        (by rw [hxu]; exact subset_convexHull ℝ _ (by simp))
      obtain ⟨w, hw⟩ := hσne
      have hw' := Finset.mem_singleton.mp (hsub (Finset.mem_insert_of_mem hw))
      exact huσ (hw' ▸ hw)
    have hxstar : x ∈ closedStar K u := by
      obtain ⟨t, ht, hsub⟩ := hK'.exists_face_subset hins
      exact mem_iUnion₂.mpr ⟨t, ⟨ht, hsub (subset_convexHull ℝ _ (by simp))⟩, hsub hxconv⟩
    obtain ⟨τ, hτ, hxτ⟩ := hstar x hxstar hxu
    have hxQ : convexHull ℝ ((insert u τ : Finset E) : Set E) =
        ⋃ s ∈ {s ∈ K'.faces | convexHull ℝ (s : Set E) ⊆
          convexHull ℝ ((insert u τ : Finset E) : Set E)}, convexHull ℝ (s : Set E) :=
      hQ' ⟨τ, hτ⟩
    rw [hxQ] at hxτ
    obtain ⟨s, ⟨hs, hsQ⟩, hxs⟩ := mem_iUnion₂.mp hxτ
    have hsub : insert u σ ⊆ s :=
      face_subset_of_mem_openSimplex_of_mem_convexHull K' hins hs hx hxs
    refine ⟨τ, hτ, fun w hw => ?_⟩
    have hwQ : w ∈ convexHull ℝ ((insert u τ : Finset E) : Set E) :=
      hsQ (subset_convexHull ℝ _ (Finset.mem_coe.mpr (hsub (Finset.mem_insert_of_mem hw))))
    exact exists_ray_mem_convexHull_of_mem_convexHull_insert hwQ (ne_of_mem_of_not_mem hw huσ)
  have hsurj : ∀ x ∈ J.space, ∃ s : ℝ, 0 < s ∧
      u + s • (x - u) ∈ (SimplicialComplex.geometricLink K' {u}).space := by
    intro x hx
    have hxu : x ≠ u := ne_of_mem_of_not_mem hx hJ.notMem_space
    refine exists_ray_mem_geometricLink_space K' hu' (fun t ht0 ht1 => ?_) hxu
    rw [hK'.space_eq]
    exact hseg x hx t ht0 ht1
  obtain ⟨f, hf⟩ := exists_isPLHomeomorphOn_of_radial u J
    (SimplicialComplex.geometricLink K' {u}) hJ.radial (isConeBase_geometricLink K') hadapt hsurj
  obtain ⟨g, hg⟩ := exists_isPLHomeomorphOn_geometricLink_of_isSubdivision hK' hu
  exact ⟨_, hg.symm.trans hf⟩

end DifferentialGeometry.Topology.PiecewiseLinear
