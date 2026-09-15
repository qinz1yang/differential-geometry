import DifferentialGeometry.Topology.PiecewiseLinear.Triangulation
import DifferentialGeometry.Topology.PiecewiseLinear.Mesh
import DifferentialGeometry.Topology.PiecewiseLinear.PLImage

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem simplicialMap_eq_of_forall_affineOn (K : Geometry.SimplicialComplex ℝ E) (f : E → F)
    (hf : ∀ s ∈ K.faces, ∃ A : E →ᵃ[ℝ] F, EqOn f A (convexHull ℝ (s : Set E))) :
    EqOn (simplicialMap K f) f K.space := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
  obtain ⟨A, hA⟩ := hf s hs
  rw [simplicialMap_eq_of_mem K f hs hxs, hA hxs]
  calc ∑ v ∈ s, weights s x v • f v = ∑ v ∈ s, weights s x v • A v :=
        Finset.sum_congr rfl fun v hv => by
          rw [hA (subset_convexHull ℝ _ (Finset.mem_coe.mpr hv))]
    _ = A (∑ v ∈ s, weights s x v • v) := (affineMap_apply_sum_smul A (sum_weights hxs)).symm
    _ = A x := by rw [sum_weights_smul hxs]

section Restrict

variable (K : Geometry.SimplicialComplex ℝ E) (Q : Set E)

def restrict : Geometry.SimplicialComplex ℝ E where
  faces := {s ∈ K.faces | convexHull ℝ (s : Set E) ⊆ Q}
  isRelLowerSet_faces := by
    rintro s ⟨hs, hsQ⟩
    exact ⟨K.nonempty_of_mem_faces hs, fun t hts ht => ⟨K.down_closed hs hts ht,
      (convexHull_mono (Finset.coe_subset.mpr hts)).trans hsQ⟩⟩
  indep hs := K.indep hs.1
  inter_subset_convexHull hs ht := K.inter_subset_convexHull hs.1 ht.1

theorem mem_restrict_faces_iff {s : Finset E} :
    s ∈ (restrict K Q).faces ↔ s ∈ K.faces ∧ convexHull ℝ (s : Set E) ⊆ Q := Iff.rfl

theorem restrict_faces_subset : (restrict K Q).faces ⊆ K.faces := fun _ hs => hs.1

theorem restrict_faces_finite [Finite K.faces] : (restrict K Q).faces.Finite :=
  (Set.toFinite K.faces).subset (restrict_faces_subset K Q)

theorem restrict_space_subset : (restrict K Q).space ⊆ Q := by
  intro x hx
  obtain ⟨s, hs, hxs⟩ := (restrict K Q).mem_space_iff.mp hx
  exact hs.2 hxs

theorem restrict_space_of_eq_biUnion
    (h : Q = ⋃ s ∈ {s ∈ K.faces | convexHull ℝ (s : Set E) ⊆ Q}, convexHull ℝ (s : Set E)) :
    (restrict K Q).space = Q :=
  h.symm

variable {K Q}

theorem restrict_isSubdivision (L : Geometry.SimplicialComplex ℝ E)
    (hL : ∀ t ∈ L.faces, convexHull ℝ (t : Set E) =
      ⋃ s ∈ {s ∈ K.faces | convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E)},
        convexHull ℝ (s : Set E)) :
    IsSubdivision (restrict K L.space) L := by
  refine ⟨Subset.antisymm (restrict_space_subset K L.space) fun x hx => ?_, ?_⟩
  · obtain ⟨t, ht, hxt⟩ := L.mem_space_iff.mp hx
    rw [hL t ht] at hxt
    obtain ⟨s, ⟨hs, hst⟩, hxs⟩ := mem_iUnion₂.mp hxt
    exact (restrict K L.space).convexHull_subset_space
      ⟨hs, hst.trans (L.convexHull_subset_space ht)⟩ hxs
  · rintro s ⟨hs, hsL⟩
    have hx : s.centroid ℝ id ∈ openSimplex s := centroid_mem_openSimplex (K.nonempty_of_mem_faces hs)
    have hxL : s.centroid ℝ id ∈ L.space := hsL (openSimplex_subset_convexHull s hx)
    obtain ⟨t, ht, hxt⟩ := L.mem_space_iff.mp hxL
    rw [hL t ht] at hxt
    obtain ⟨s', ⟨hs', hs't⟩, hxs'⟩ := mem_iUnion₂.mp hxt
    refine ⟨t, ht, (convexHull_mono ?_).trans hs't⟩
    exact Finset.coe_subset.mpr (face_subset_of_mem_openSimplex_of_mem_convexHull K hs hs' hx hxs')

theorem exists_isSubdivision_restrict_space [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] {Q : Set E} (hQ : IsPolyhedron Q)
    (hQK : Q ⊆ K.space) :
    ∃ K' : Geometry.SimplicialComplex ℝ E, IsSubdivision K' K ∧ K'.faces.Finite ∧
      (restrict K' Q).space = Q := by
  obtain ⟨K', hK', hfin, hQ'⟩ :=
    exists_isSubdivision_subcomplexes K (fun _ : Unit => Q) (fun _ => hQ) fun _ => hQK
  exact ⟨K', hK', hfin, restrict_space_of_eq_biUnion K' Q (hQ' ())⟩

theorem exists_isSubdivision_restrict_isSubdivision [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (L : Geometry.SimplicialComplex ℝ E)
    [Finite L.faces] (hLK : L.space ⊆ K.space) :
    ∃ K' : Geometry.SimplicialComplex ℝ E, IsSubdivision K' K ∧ K'.faces.Finite ∧
      IsSubdivision (restrict K' L.space) L := by
  obtain ⟨K', hK', hfin, hQ'⟩ := exists_isSubdivision_subcomplexes K
    (fun t : L.faces => convexHull ℝ ((t : Finset E) : Set E))
    (fun t => isPolyhedron_convexHull_of_affineIndependent _ (L.indep t.2))
    fun t => (L.convexHull_subset_space t.2).trans hLK
  exact ⟨K', hK', hfin, restrict_isSubdivision L fun t ht => hQ' ⟨t, ht⟩⟩

theorem IsSubdivision.restrict {R : Geometry.SimplicialComplex ℝ E}
    (hR : IsSubdivision R K) (L : Geometry.SimplicialComplex ℝ E) (hLK : L.faces ⊆ K.faces) :
    IsSubdivision (restrict R L.space) L :=
  restrict_isSubdivision L fun _ ht => hR.convexHull_eq_biUnion (hLK ht)

theorem exists_isSubdivision_subcomplexes_closedStars_subset_cover [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {J : Type*} [Finite J] (Q : J → Set E) (hQ : ∀ j, IsPolyhedron (Q j))
    (hQK : ∀ j, Q j ⊆ K.space) {ι : Type*} (U : ι → Set E)
    (hU : ∀ i, IsOpen (((↑) : K.space → E) ⁻¹' U i)) (hcover : K.space ⊆ ⋃ i, U i) :
    ∃ R : Geometry.SimplicialComplex ℝ E, IsSubdivision R K ∧ R.faces.Finite ∧
      (∀ j, (restrict R (Q j)).space = Q j) ∧
      ∀ s ∈ R.faces, ∃ i, (⋃ v ∈ s, closedStar R v) ⊆ U i := by
  obtain ⟨K₀, hK₀, hfinite₀, hQ₀⟩ := exists_isSubdivision_subcomplexes K Q hQ hQK
  have : Finite K₀.faces := hfinite₀.to_subtype
  have hU₀ : ∀ i, IsOpen (((↑) : K₀.space → E) ⁻¹' U i) := by
    rw [hK₀.space_eq]
    exact hU
  have hcover₀ : K₀.space ⊆ ⋃ i, U i := by rwa [hK₀.space_eq]
  obtain ⟨R, hR, hfinite, hstars⟩ :=
    exists_isSubdivision_closedStars_subset_cover K₀ U hU₀ hcover₀
  refine ⟨R, hR.trans hK₀, hfinite, fun j => ?_, hstars⟩
  have hsub := hR.restrict (restrict K₀ (Q j)) (restrict_faces_subset K₀ (Q j))
  rw [restrict_space_of_eq_biUnion K₀ (Q j) (hQ₀ j)] at hsub
  exact hsub.space_eq.trans (restrict_space_of_eq_biUnion K₀ (Q j) (hQ₀ j))

end Restrict

end DifferentialGeometry.Topology.PiecewiseLinear
