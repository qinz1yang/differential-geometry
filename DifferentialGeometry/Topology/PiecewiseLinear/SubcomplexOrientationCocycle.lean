import DifferentialGeometry.Topology.PiecewiseLinear.CocycleMonodromy
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.OrientationCocycle

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {K L : Geometry.SimplicialComplex ℝ E}

theorem carrierFace_eq_of_faces_subset (hLK : L.faces ⊆ K.faces) {x : E} (hx : x ∈ L.space) :
    carrierFace L x = carrierFace K x := by
  have hxK : x ∈ K.space := space_mono_of_faces_subset hLK hx
  exact Finset.Subset.antisymm
    (face_subset_of_mem_openSimplex_of_mem_convexHull K (hLK (carrierFace_mem hx))
      (carrierFace_mem hxK) (mem_openSimplex_carrierFace hx) (mem_convexHull_carrierFace hxK))
    (face_subset_of_mem_openSimplex_of_mem_convexHull K (carrierFace_mem hxK)
      (hLK (carrierFace_mem hx)) (mem_openSimplex_carrierFace hxK) (mem_convexHull_carrierFace hx))

open Classical in
theorem faceStarComplex_mono (hLK : L.faces ⊆ K.faces) (s : Finset E) :
    faceStarComplex L s ≤ faceStarComplex K s := fun _ ht => ⟨hLK ht.1, hLK ht.2⟩

variable [FiniteDimensional ℝ E] [Finite K.faces] [Finite L.faces] {n : ℕ}

local instance finite_faceStarComplex_faces_subcomplexCocycle
    (M : Geometry.SimplicialComplex ℝ E) [Finite M.faces] (s : Finset E) :
    Finite (faceStarComplex M s).faces := (faceStarComplex_faces_finite M s).to_subtype

open Classical in
noncomputable def orientationOfLe (hLK : L.faces ⊆ K.faces)
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (hL : IsCombinatorialManifoldWithBoundary n L)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s))
    (s : Finset E) (hs : s ∈ L.faces) : CoherentOrientation n (faceStarComplex L s) :=
  (o s (hLK hs)).restrict (faceStarComplex K s) (faceStarComplex L s)
    (faceStarComplex_mono hLK s) (hK.faceStar (hLK hs)) (hL.faceStar hs)

open Classical in
theorem localOrientationSign_orientationOfLe (hLK : L.faces ⊆ K.faces)
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (hL : IsCombinatorialManifoldWithBoundary n L)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s))
    (r : LinearOrder E) {s : Finset E} (hs : s ∈ L.faces) (t : Finset E) :
    localOrientationSign r (orientationOfLe hLK hK hL o) s t =
      localOrientationSign r o s t := by
  rw [localOrientationSign, dif_pos hs, localOrientationSign, dif_pos (hLK hs)]
  rfl

open Classical in
theorem localSubdivisionOrientationSign_orientationOfLe (hLK : L.faces ⊆ K.faces)
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (hL : IsCombinatorialManifoldWithBoundary n L)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s))
    {a : E} (ha : a ∈ L.space) {q : Finset E} (hq : q.centroid ℝ id ∈ L.space) :
    localSubdivisionOrientationSign (orientationOfLe hLK hK hL o) a q =
      localSubdivisionOrientationSign o a q := by
  have hcarrier : carrierFace K a ∈ L.faces := by
    rw [← carrierFace_eq_of_faces_subset hLK ha]
    exact carrierFace_mem ha
  simp only [localSubdivisionOrientationSign, carrierFace_eq_of_faces_subset hLK hq,
    carrierFace_eq_of_faces_subset hLK ha]
  split_ifs with h1 h2
  · exact congrArg _ (localOrientationSign_orientationOfLe hLK hK hL o _ hcarrier _)
  · rfl
  · rfl

open Classical in
theorem orientationCocycle_parity_of_faces_subset (hLK : L.faces ⊆ K.faces)
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (hL : IsCombinatorialManifoldWithBoundary n L)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s))
    {a b : E} (hab : {a, b} ∈ (barycentricSubdivision L).faces) :
    (orientationCocycle hL (orientationOfLe hLK hK hL o)).parity a b =
      (orientationCocycle hK o).parity a b := by
  have hsub := barycentricSubdivision_faces_subset hLK
  obtain ⟨q, hq, habq, hqcard⟩ := hL.barycentricSubdivision.exists_face_superset_card_eq hab
  have ha : a ∈ q := habq (by simp)
  have hb : b ∈ q := habq (by simp)
  have hspaceL : (barycentricSubdivision L).space = L.space :=
    (barycentricSubdivision_isSubdivision L).space_eq
  have haL : a ∈ L.space := by
    rw [← hspaceL]
    exact (barycentricSubdivision L).subset_space hq ha
  have hbL : b ∈ L.space := by
    rw [← hspaceL]
    exact (barycentricSubdivision L).subset_space hq hb
  have hcL : q.centroid ℝ id ∈ L.space := by
    rw [← hspaceL]
    exact (barycentricSubdivision L).convexHull_subset_space hq
      (openSimplex_subset_convexHull q
        (centroid_mem_openSimplex ((barycentricSubdivision L).nonempty_of_mem_faces hq)))
  rw [orientationCocycle_parity_eq_localSubdivisionOrientationSign hL
      (orientationOfLe hLK hK hL o) hq ha hb hqcard,
    orientationCocycle_parity_eq_localSubdivisionOrientationSign hK o (hsub hq) ha hb hqcard,
    localSubdivisionOrientationSign_orientationOfLe hLK hK hL o haL hcL,
    localSubdivisionOrientationSign_orientationOfLe hLK hK hL o hbL hcL]

open Classical in
theorem isOrientable_of_isCoboundary_ofLe (hLK : L.faces ⊆ K.faces)
    (hK : IsCombinatorialManifoldWithBoundary n K)
    (hL : IsCombinatorialManifoldWithBoundary n L)
    (o : ∀ s ∈ K.faces, CoherentOrientation n (faceStarComplex K s))
    (h : ((orientationCocycle hK o).ofLe
      (barycentricSubdivision_faces_subset hLK)).IsCoboundary) :
    IsOrientable n L := by
  refine (orientationCocycle_isCoboundary_iff hL (orientationOfLe hLK hK hL o)).mp ?_
  obtain ⟨δ, hδ⟩ := h
  exact ⟨δ, fun a b hab =>
    (orientationCocycle_parity_of_faces_subset hLK hK hL o hab).trans (hδ a b hab)⟩

end DifferentialGeometry.Topology.PiecewiseLinear
