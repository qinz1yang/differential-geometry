import DifferentialGeometry.Topology.SimplicialComplex.VertexStar

set_option autoImplicit false
noncomputable section
open Set Finset

namespace DifferentialGeometry.Topology.SimplicialComplex

universe u
variable {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] [LinearOrder E]
  (K : Geometry.SimplicialComplex ℝ E) (s : Finset E) (hs : s ∈ K.faces)


def geometricFaceBarycenter : K.space :=
  ⟨s.centroid ℝ id, Geometry.SimplicialComplex.convexHull_subset_space hs
    (s.centroid_mem_convexHull (K.nonempty_of_mem_faces hs))⟩

omit [LinearOrder E] in
@[simp]
theorem geometricFaceBarycenter_val :
    (geometricFaceBarycenter K s hs).val = s.centroid ℝ id := rfl

omit [LinearOrder E] in
theorem geometricFaceHomeomorphism_barycenter [Nonempty s] :
    (geometricFaceHomeomorphism K hs stdSimplex.barycenter).val = s.centroid ℝ id := by
  rw [← Finset.centroid_univ ℝ s, Finset.centroid_def,
    Finset.affineCombination_eq_linear_combination _ _ _
      (Finset.sum_centroidWeights_eq_one_of_nonempty ℝ _ Finset.univ_nonempty)]
  simp only [geometricFaceHomeomorphism_apply, DifferentialGeometry.Simplex.vertexMap_apply,
    stdSimplex.barycenter_apply, Finset.centroidWeights_apply, Finset.card_univ]

omit [LinearOrder E] in
theorem geometricFaceBarycenter_mem_convexHull :
    (geometricFaceBarycenter K s hs).val ∈ convexHull ℝ (s : Set E) :=
  s.centroid_mem_convexHull (K.nonempty_of_mem_faces hs)

theorem vertexHeight_geometricFaceBarycenter [Finite K.faces] (p : E) :
    vertexHeight K p (geometricFaceBarycenter K s hs) =
      if p ∈ s then (s.card : ℝ)⁻¹ else 0 := by
  let : Nonempty s := (K.nonempty_of_mem_faces hs).to_subtype
  have he : (⟨(geometricFaceHomeomorphism K hs stdSimplex.barycenter).val,
      Geometry.SimplicialComplex.convexHull_subset_space hs
        (geometricFaceHomeomorphism K hs stdSimplex.barycenter).prop⟩ : K.space) =
      geometricFaceBarycenter K s hs :=
    Subtype.ext (geometricFaceHomeomorphism_barycenter K s hs)
  rw [← he]
  by_cases hp : p ∈ s
  · rw [vertexHeight_face_of_mem K p hs hp, if_pos hp]
    simp only [stdSimplex.barycenter_apply, Fintype.card_coe]
  · rw [vertexHeight_face_of_not_mem K p hs hp, if_neg hp]

theorem vertexHeight_geometricFaceBarycenter_pos_iff [Finite K.faces] (p : E) :
    0 < vertexHeight K p (geometricFaceBarycenter K s hs) ↔ p ∈ s := by
  rw [vertexHeight_geometricFaceBarycenter]
  split_ifs with hp
  · exact iff_of_true (inv_pos.mpr (Nat.cast_pos.mpr
      (Finset.card_pos.mpr (K.nonempty_of_mem_faces hs)))) hp
  · exact iff_of_false (lt_irrefl 0) hp

omit [LinearOrder E] in
theorem geometricFaceBarycenter_not_mem_costar :
    (geometricFaceBarycenter K s hs).val ∉ (geometricFaceCostar K s).space := by
  let : Nonempty s := (K.nonempty_of_mem_faces hs).to_subtype
  intro h
  rw [geometricFaceBarycenter_val, ← geometricFaceHomeomorphism_barycenter K s hs] at h
  have hb := (vertexMap_mem_geometricFaceCostar_iff K hs stdSimplex.barycenter).mp h
  exact DifferentialGeometry.Simplex.boundary_ne_barycenter hb rfl

omit [LinearOrder E] in
theorem geometricFaceBarycenter_mem_face_iff (t : Finset E) (ht : t ∈ K.faces) :
    (geometricFaceBarycenter K s hs).val ∈ convexHull ℝ (t : Set E) ↔ s ⊆ t := by
  constructor
  · intro hx
    by_contra hst
    exact geometricFaceBarycenter_not_mem_costar K s hs
      (Geometry.SimplicialComplex.mem_space_iff.mpr ⟨t, ⟨ht, hst⟩, hx⟩)
  · intro hst
    exact convexHull_mono (show (s : Set E) ⊆ t from hst)
      (geometricFaceBarycenter_mem_convexHull K s hs)

omit [LinearOrder E] in
theorem geometricFaceBarycenter_mem_subcomplex_iff (L : Geometry.SimplicialComplex ℝ E)
    (hLK : L ≤ K) :
    (geometricFaceBarycenter K s hs).val ∈ L.space ↔ s ∈ L.faces := by
  constructor
  · intro hx
    obtain ⟨t, ht, hxt⟩ := Geometry.SimplicialComplex.mem_space_iff.mp hx
    exact L.down_closed ht ((geometricFaceBarycenter_mem_face_iff K s hs t (hLK ht)).mp hxt)
      (K.nonempty_of_mem_faces hs)
  · intro hsL
    exact Geometry.SimplicialComplex.convexHull_subset_space hsL
      (geometricFaceBarycenter_mem_convexHull K s hs)

omit [LinearOrder E] in
theorem geometricFaceBarycenter_eq_iff (t : Finset E) (ht : t ∈ K.faces) :
    geometricFaceBarycenter K s hs = geometricFaceBarycenter K t ht ↔ s = t := by
  constructor
  · intro he
    have hval := congrArg Subtype.val he
    apply Finset.Subset.antisymm
    · apply (geometricFaceBarycenter_mem_face_iff K s hs t ht).mp
      rw [hval]
      exact geometricFaceBarycenter_mem_convexHull K t ht
    · apply (geometricFaceBarycenter_mem_face_iff K t ht s hs).mp
      rw [← hval]
      exact geometricFaceBarycenter_mem_convexHull K s hs
  · rintro rfl
    rfl

end DifferentialGeometry.Topology.SimplicialComplex
