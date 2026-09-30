import DifferentialGeometry.Topology.SimplicialComplex.Barycentric.Subdivision.BarycentricComplexSubdivision
import DifferentialGeometry.Topology.SimplicialComplex.Barycentric.Coordinates.BarycentricMesh
import Mathlib.Order.Interval.Finset.Nat

namespace DifferentialGeometry.Topology.Engulfing

set_option linter.unusedSectionVars false

open Set Metric _root_.Topology

variable {E : Type*} [DecidableEq E] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem isFaceChain.card_le_parent {ι : Type*}
    {C : Finset (Finset ι)} (hC : isFaceChain C) {T : Finset ι}
    (hT : ∀ s ∈ C, s ⊆ T) : C.card ≤ T.card := by
  classical
  have hmap : Set.MapsTo Finset.card (C : Set (Finset ι))
      (Finset.Icc 1 T.card : Finset ℕ) := by
    intro s hs
    exact Finset.mem_Icc.mpr ⟨Finset.card_pos.mpr (hC.1 s hs),
      Finset.card_le_card (hT s hs)⟩
  have hinj : (C : Set (Finset ι)).InjOn Finset.card := by
    intro s hs t ht heq
    rcases hC.2 s hs t ht with hst | hts
    · exact Finset.eq_of_subset_of_card_le hst heq.ge
    · exact (Finset.eq_of_subset_of_card_le hts heq.le).symm
  simpa using Finset.card_le_card_of_injOn Finset.card hmap hinj

theorem barycentricSubdivision_face_card_le (K : Geometry.SimplicialComplex ℝ E)
    {d : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) :
    ∀ s ∈ (barycentricSubdivision K).faces, s.card ≤ d + 1 := by
  classical
  rintro s ⟨C, hCne, hC, hCK, rfl⟩
  obtain ⟨V, hVC, hCV⟩ := hC.exists_largest hCne
  have himage : (chainCentroids (id : E → E) C).card ≤ C.card := by
    unfold chainCentroids
    exact @Finset.card_image_le (Finset E) E C (fun s => s.centroid ℝ id)
      (Classical.decEq E)
  exact himage.trans ((hC.card_le_parent hCV).trans (hd V (hCK V hVC)))

def simplicialRefines (L K : Geometry.SimplicialComplex ℝ E) : Prop :=
  ∀ s ∈ L.faces, ∃ t ∈ K.faces,
    convexHull ℝ (s : Set E) ⊆ convexHull ℝ (t : Set E)

omit [DecidableEq E] in
theorem simplicialRefines.refl (K : Geometry.SimplicialComplex ℝ E) : simplicialRefines K K := by
  classical
  exact fun s hs => ⟨s, hs, subset_rfl⟩

omit [DecidableEq E] in
theorem simplicialRefines.trans {L K J : Geometry.SimplicialComplex ℝ E}
    (hLK : simplicialRefines L K) (hKJ : simplicialRefines K J) : simplicialRefines L J := by
  classical
  intro s hs
  obtain ⟨t, ht, hst⟩ := hLK s hs
  obtain ⟨u, hu, htu⟩ := hKJ t ht
  exact ⟨u, hu, hst.trans htu⟩

theorem barycentricSubdivision_refines (K : Geometry.SimplicialComplex ℝ E) :
    simplicialRefines (barycentricSubdivision K) K := by
  rintro s ⟨C, hCne, hC, hCK, rfl⟩
  obtain ⟨V, hVC, hCV⟩ := hC.exists_largest hCne
  exact ⟨V, hCK V hVC, hC.convexHull_chainCentroids_subset V hCV⟩

def hasMeshLE (K : Geometry.SimplicialComplex ℝ E) (D : ℝ) : Prop :=
  ∀ s ∈ K.faces, diam (convexHull ℝ (s : Set E)) ≤ D

omit [DecidableEq E] in
theorem exists_mesh_bound (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite) :
    ∃ D : ℝ, 0 ≤ D ∧ hasMeshLE K D := by
  classical
  obtain ⟨D, hD⟩ := (hK.image (fun s : Finset E => diam (convexHull ℝ (s : Set E)))).bddAbove
  exact ⟨max D 0, le_max_right _ _, fun s hs =>
    (hD (mem_image_of_mem _ hs)).trans (le_max_left _ _)⟩

theorem hasMeshLE.barycentricSubdivision_of_face_card_le
    {K : Geometry.SimplicialComplex ℝ E} {D : ℝ} (hK : hasMeshLE K D) (hD : 0 ≤ D)
    {d : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) :
    hasMeshLE (barycentricSubdivision K) ((d : ℝ) / (d + 1) * D) := by
  classical
  rintro s ⟨C, hCne, hC, hCK, rfl⟩
  obtain ⟨V, hVC, hCV⟩ := hC.exists_largest hCne
  have hV : V ∈ K.faces := hCK V hVC
  have hdist : ∀ i ∈ V, ∀ j ∈ V, dist (id i) (id j) ≤ D := by
    intro i hi j hj
    exact (dist_le_diam_of_mem (isBounded_convexHull.mpr V.finite_toSet.isBounded)
      (subset_convexHull ℝ _ hi) (subset_convexHull ℝ _ hj)).trans (hK V hV)
  have h := hC.diam_convexHull_centroids_le id (hd V hV) hCV hD hdist
  simpa only [chainCentroids, Finset.coe_image] using h

theorem hasMeshLE.barycentricSubdivision [FiniteDimensional ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} {D : ℝ} (hK : hasMeshLE K D) (hD : 0 ≤ D) :
    hasMeshLE (barycentricSubdivision K)
      ((Module.finrank ℝ E : ℝ) / (Module.finrank ℝ E + 1) * D) := by
  classical
  rintro s ⟨C, hCne, hC, hCK, rfl⟩
  obtain ⟨V, hVC, hCV⟩ := hC.exists_largest hCne
  have hV : V ∈ K.faces := hCK V hVC
  have hdist : ∀ i ∈ V, ∀ j ∈ V, dist (id i) (id j) ≤ D := by
    intro i hi j hj
    exact (dist_le_diam_of_mem (isBounded_convexHull.mpr V.finite_toSet.isBounded)
      (subset_convexHull ℝ _ hi) (subset_convexHull ℝ _ hj)).trans (hK V hV)
  have h := hC.diam_convexHull_centroids_le_finrank id (K.indep hV) hCV hD hdist
  simpa only [chainCentroids, Finset.coe_image] using h

noncomputable def barycentricSubdivisionIter (K : Geometry.SimplicialComplex ℝ E) :
    ℕ → Geometry.SimplicialComplex ℝ E
  | 0 => K
  | n + 1 => barycentricSubdivision (barycentricSubdivisionIter K n)

@[simp] theorem barycentricSubdivisionIter_zero (K : Geometry.SimplicialComplex ℝ E) :
    barycentricSubdivisionIter K 0 = K := rfl

@[simp] theorem barycentricSubdivisionIter_succ (K : Geometry.SimplicialComplex ℝ E) (n : ℕ) :
    barycentricSubdivisionIter K (n + 1) =
      barycentricSubdivision (barycentricSubdivisionIter K n) := rfl

theorem barycentricSubdivisionIter_space (K : Geometry.SimplicialComplex ℝ E) (n : ℕ) :
    (barycentricSubdivisionIter K n).space = K.space := by
  induction n with
  | zero => rfl
  | succ n ih => rw [barycentricSubdivisionIter_succ, barycentricSubdivision_space, ih]

theorem barycentricSubdivisionIter_finite_faces (K : Geometry.SimplicialComplex ℝ E)
    (hK : K.faces.Finite) (n : ℕ) : (barycentricSubdivisionIter K n).faces.Finite := by
  induction n with
  | zero => exact hK
  | succ n ih => exact barycentricSubdivision_finite_faces _ ih

theorem barycentricSubdivisionIter_refines (K : Geometry.SimplicialComplex ℝ E) (n : ℕ) :
    simplicialRefines (barycentricSubdivisionIter K n) K := by
  induction n with
  | zero => exact simplicialRefines.refl K
  | succ n ih => exact (barycentricSubdivision_refines _).trans ih

theorem barycentricSubdivisionIter_face_card_le (K : Geometry.SimplicialComplex ℝ E)
    {d : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) (n : ℕ) :
    ∀ s ∈ (barycentricSubdivisionIter K n).faces, s.card ≤ d + 1 := by
  induction n with
  | zero => exact hd
  | succ n ih => exact barycentricSubdivision_face_card_le _ ih

theorem hasMeshLE.barycentricSubdivisionIter_of_face_card_le
    {K : Geometry.SimplicialComplex ℝ E} {D : ℝ} (hK : hasMeshLE K D) (hD : 0 ≤ D)
    {d : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) (n : ℕ) :
    hasMeshLE (barycentricSubdivisionIter K n) (((d : ℝ) / (d + 1)) ^ n * D) := by
  induction n with
  | zero => simpa using hK
  | succ n ih =>
    have hbound := ih.barycentricSubdivision_of_face_card_le
      (mul_nonneg (pow_nonneg (by positivity) _) hD)
      (barycentricSubdivisionIter_face_card_le K hd n)
    intro s hs
    apply (hbound s hs).trans_eq
    rw [pow_succ]
    ring

omit [DecidableEq E] in
theorem exists_fine_subdivision_of_face_card_le
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite)
    {d : ℕ} (hd : ∀ s ∈ K.faces, s.card ≤ d + 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ L : Geometry.SimplicialComplex ℝ E, L.faces.Finite ∧ L.space = K.space ∧
      simplicialRefines L K ∧
      (∀ s ∈ L.faces, diam (convexHull ℝ (s : Set E)) < ε) ∧
      ∀ s ∈ L.faces, s.card ≤ d + 1 := by
  classical
  obtain ⟨D, hD, hmesh⟩ := exists_mesh_bound K hK
  obtain ⟨N, hN⟩ := exists_barycentric_mesh_bound_lt d D hε
  refine ⟨barycentricSubdivisionIter K N, barycentricSubdivisionIter_finite_faces K hK N,
    barycentricSubdivisionIter_space K N, barycentricSubdivisionIter_refines K N, ?_,
    barycentricSubdivisionIter_face_card_le K hd N⟩
  intro s hs
  exact (hmesh.barycentricSubdivisionIter_of_face_card_le hD hd N s hs).trans_lt (hN N le_rfl)

theorem hasMeshLE.barycentricSubdivisionIter [FiniteDimensional ℝ E]
    {K : Geometry.SimplicialComplex ℝ E} {D : ℝ} (hK : hasMeshLE K D) (hD : 0 ≤ D) (n : ℕ) :
    hasMeshLE (barycentricSubdivisionIter K n)
      (((Module.finrank ℝ E : ℝ) / (Module.finrank ℝ E + 1)) ^ n * D) := by
  induction n with
  | zero => simpa using hK
  | succ n ih =>
    have hbound := ih.barycentricSubdivision (mul_nonneg (pow_nonneg (by positivity) _) hD)
    intro s hs
    apply (hbound s hs).trans_eq
    rw [pow_succ]
    ring

omit [DecidableEq E] in
theorem exists_fine_subdivision [FiniteDimensional ℝ E]
    (K : Geometry.SimplicialComplex ℝ E) (hK : K.faces.Finite) {ε : ℝ} (hε : 0 < ε) :
    ∃ L : Geometry.SimplicialComplex ℝ E, L.faces.Finite ∧ L.space = K.space ∧
      simplicialRefines L K ∧
      (∀ s ∈ L.faces, diam (convexHull ℝ (s : Set E)) < ε) ∧
      ∀ s ∈ L.faces, s.card ≤ Module.finrank ℝ E + 1 := by
  classical
  obtain ⟨D, hD, hmesh⟩ := exists_mesh_bound K hK
  obtain ⟨N, hN⟩ := exists_barycentric_mesh_bound_lt (Module.finrank ℝ E) D hε
  refine ⟨barycentricSubdivisionIter K N, barycentricSubdivisionIter_finite_faces K hK N,
    barycentricSubdivisionIter_space K N, barycentricSubdivisionIter_refines K N, ?_, ?_⟩
  · intro s hs
    exact (hmesh.barycentricSubdivisionIter hD N s hs).trans_lt (hN N le_rfl)
  · intro s hs
    simpa only [Fintype.card_coe] using
      ((barycentricSubdivisionIter K N).indep hs).card_le_finrank_succ.trans
        (Nat.add_le_add_right (Submodule.finrank_le _) 1)

end DifferentialGeometry.Topology.Engulfing
