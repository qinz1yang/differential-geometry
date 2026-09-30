import DifferentialGeometry.Topology.PiecewiseLinear.Combinatorial
import DifferentialGeometry.Topology.PiecewiseLinear.DerivedNeighborhoodManifold
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedralManifold
import Mathlib.Topology.Compactness.SigmaCompact

open Set Topology Metric

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
theorem derivedNeighborhood_space_subset_of_forall_face
    (K L : Geometry.SimplicialComplex ℝ E) {O : Set E}
    (hO : ∀ s ∈ L.faces, ∀ t ∈ K.faces, s.centroid ℝ id ∈ convexHull ℝ (t : Set E) →
      convexHull ℝ (t : Set E) ⊆ O) : (derivedNeighborhood K L).space ⊆ O := by
  classical
  intro x hx
  obtain ⟨u, hu, hxu⟩ := (derivedNeighborhood K L).mem_space_iff.mp hx
  obtain ⟨D, hD, hne, hL, rfl⟩ := hu
  obtain ⟨e, he, htop⟩ := hD.exists_top hne
  obtain ⟨t, ht, het⟩ := (barycentricSubdivision_isSubdivision K).exists_face_subset
    (hD.mem_faces he)
  obtain ⟨s, hs, hse⟩ := hL e he
  have hst : s.centroid ℝ id ∈ convexHull ℝ (t : Set E) :=
    het (subset_convexHull ℝ _ hse)
  apply hO s hs t ht hst
  apply het
  refine convexHull_min ?_ (convex_convexHull ℝ _) hxu
  rintro y hy
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hy
  exact convexHull_mono (Finset.coe_subset.mpr (htop f hf))
    (f.centroid_mem_convexHull ((barycentricSubdivision K).nonempty_of_mem_faces (hD.mem_faces hf)))

open Classical in
theorem IsCombinatorialManifoldWithBoundary.exists_isSubdivision_neighborhood
    [FiniteDimensional ℝ E] {n : ℕ} {K : Geometry.SimplicialComplex ℝ E} [Finite K.faces]
    (hK : IsCombinatorialManifoldWithBoundary (n + 1) K) {C O : Set E}
    (hC : IsCompact C) (hCK : C ⊆ K.space) (hO : IsOpen O) (hCO : C ⊆ O) :
    ∃ K' L : Geometry.SimplicialComplex ℝ E, IsSubdivision K' K ∧ K'.faces.Finite ∧
      L.faces ⊆ K'.faces ∧ IsCombinatorialManifoldWithBoundary (n + 1) L ∧
      L.space ⊆ O ∧ ∀ x ∈ C, L.space ∈ 𝓝[K.space] x := by
  classical
  obtain ⟨δ, hδ, hthick⟩ := hC.exists_cthickening_subset_open hO hCO
  obtain ⟨J, hJ, hJfin, -, hdiam⟩ := exists_isSubdivision_diam_lt K (N := n + 1)
    (fun _ hs => hK.card_le K hs) (half_pos hδ)
  have : Finite J.faces := hJfin.to_subtype
  let Q : Set E := {x | ∀ t ∈ J.faces, x ∈ convexHull ℝ (t : Set E) →
    convexHull ℝ (t : Set E) ⊆ O}
  let L := restrict J Q
  have hCL : C ⊆ L.space := by
    intro x hx
    have hxJ : x ∈ J.space := hJ.space_eq.symm ▸ hCK hx
    obtain ⟨s, hs, hxs⟩ := J.mem_space_iff.mp hxJ
    refine L.convexHull_subset_space ⟨hs, ?_⟩ hxs
    intro y hys t ht hyt z hzt
    apply hthick
    apply mem_cthickening_of_dist_le z x δ C hx
    have hzy : dist z y < δ / 2 :=
      (dist_le_diam_of_mem (t.finite_toSet.isCompact_convexHull ℝ).isBounded hzt hyt).trans_lt
        (hdiam t ht)
    have hyx : dist y x < δ / 2 :=
      (dist_le_diam_of_mem (s.finite_toSet.isCompact_convexHull ℝ).isBounded hys hxs).trans_lt
        (hdiam s hs)
    have hzx := dist_triangle z y x
    linarith
  refine ⟨PiecewiseLinear.secondDerived J, PiecewiseLinear.derivedNeighborhood J L,
    (secondDerived_isSubdivision J).trans hJ,
    Set.toFinite _, derivedNeighborhood_faces_subset J L,
    (hK.of_isSubdivision hJ).derivedNeighborhood L, ?_, ?_⟩
  · apply derivedNeighborhood_space_subset_of_forall_face
    intro s hs t ht hst
    exact hs.2 (s.centroid_mem_convexHull (J.nonempty_of_mem_faces hs.1)) t ht hst
  · intro x hx
    rw [← hJ.space_eq]
    exact derivedNeighborhood_mem_nhdsWithin (restrict_faces_subset J Q) (hCL hx)

universe u

variable {n : ℕ} {X : Type u} [TopologicalSpace X]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) X]

def PLTriangulation.toPieceIn (T : PLTriangulation n X) :
    PLPieceIn (EuclideanSpace ℝ (Fin T.ambientDim)) n X univ where
  complex := T.complex
  finite_faces := by
    have := T.finite_faces
    exact Set.toFinite _
  map := T.map
  bijOn := T.bijOn
  continuousOn := T.continuousOn
  isPiecewiseAffineOn_chart := T.isPiecewiseAffineOn_chart
  isPiecewiseAffineOn_chart_symm := fun e he => by
    rw [preimage_univ, inter_univ]
    exact T.isPiecewiseAffineOn_chart_symm e he

theorem PLPieceIn.image_mem_nhds [FiniteDimensional ℝ E] [T2Space X]
    (T : PLPieceIn E n X univ) {x : E} (hx : x ∈ T.complex.space) {A : Set E}
    (hA : A ∈ 𝓝[T.complex.space] x) : T.map '' A ∈ 𝓝 (T.map x) := by
  have := T.finite_faces.to_subtype
  obtain ⟨O, hO, hxO, hOA⟩ := mem_nhdsWithin.mp hA
  have hcompact := (PiecewiseLinear.isPolyhedron_space T.complex).isCompact.diff hO
  have hclosed := (hcompact.image_of_continuousOn (T.continuousOn.mono sdiff_subset)).isClosed
  have hxnot : T.map x ∉ T.map '' (T.complex.space \ O) := by
    rintro ⟨y, ⟨hy, hyO⟩, hxy⟩
    exact hyO ((T.bijOn.injOn hy hx hxy).symm ▸ hxO)
  apply Filter.mem_of_superset (hclosed.isOpen_compl.mem_nhds hxnot)
  intro y hy
  obtain ⟨z, hz, rfl⟩ := T.bijOn.surjOn (mem_univ y)
  have hzO : z ∈ O := by
    by_contra hzO
    exact hy ⟨z, ⟨hz, hzO⟩, rfl⟩
  exact mem_image_of_mem _ (hOA ⟨hzO, hz⟩)

open Classical in
theorem PLPieceIn.exists_isPolyhedralManifoldWithBoundary_neighborhood
    [FiniteDimensional ℝ E] [T2Space X] (T : PLPieceIn E n X univ) {m : ℕ}
    (hT : IsCombinatorialManifoldWithBoundary (m + 1) T.complex) {C U : Set X}
    (hC : IsCompact C) (hU : IsOpen U) (hCU : C ⊆ U) :
    ∃ P : Set X, IsCompact P ∧ IsPolyhedralManifoldWithBoundary (n := n) (m + 1) P ∧
      C ⊆ interior P ∧ P ⊆ U := by
  classical
  have := T.finite_faces.to_subtype
  have hcompact := (PiecewiseLinear.isPolyhedron_space T.complex).isCompact
  obtain ⟨O, hO, hpre⟩ := continuousOn_iff'.mp T.continuousOn U hU
  have hpreC : IsCompact (T.complex.space ∩ T.map ⁻¹' C) :=
    hcompact.of_isClosed_subset
      (T.continuousOn.preimage_isClosed_of_isClosed hcompact.isClosed hC.isClosed)
      inter_subset_left
  have hCO : T.complex.space ∩ T.map ⁻¹' C ⊆ O := by
    intro z hz
    have hzU : z ∈ T.map ⁻¹' U ∩ T.complex.space := ⟨hCU hz.2, hz.1⟩
    rw [hpre] at hzU
    exact hzU.1
  obtain ⟨K', L, hK', hK'fin, hL, hman, hLO, hnhds⟩ :=
    hT.exists_isSubdivision_neighborhood hpreC inter_subset_left hO hCO
  let P := (T.subdivide K' hK' hK'fin).restrict L hL
  have hspace : L.space ⊆ T.complex.space := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := L.mem_space_iff.mp hx
    exact hK'.space_eq ▸ K'.convexHull_subset_space (hL hs) hxs
  refine ⟨T.map '' L.space, P.isCompact,
    isPolyhedralManifoldWithBoundary_of_pieceIn P hman, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := T.bijOn.surjOn (mem_univ y)
    exact mem_interior_iff_mem_nhds.mpr (T.image_mem_nhds hx (hnhds x ⟨hx, hy⟩))
  · rintro y ⟨x, hx, rfl⟩
    have hxO : x ∈ O ∩ T.complex.space := ⟨hLO hx, hspace hx⟩
    rw [← hpre] at hxO
    exact hxO.1

theorem exists_exhaustion {m : ℕ} {X : Type u} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) X] [CompactSpace X] [T2Space X]
    [SecondCountableTopology X] [Nonempty X] [HasGroupoid X (plGroupoid (m + 1))]
    {U : Set X} (hU : IsOpen U) :
    ∃ N : ℕ → Set X, (∀ i, IsCompact (N i) ∧
      IsPolyhedralManifoldWithBoundary (n := m + 1) (m + 1) (N i) ∧
      N i ⊆ interior (N (i + 1))) ∧ ⋃ i, N i = U := by
  classical
  obtain ⟨T, hT⟩ := plManifoldTriangulation (m + 1)
    (inferInstance : ChartedSpace (EuclideanSpace ℝ (Fin (m + 1))) X) inferInstance
  have := hU.locallyCompactSpace
  let C : ℕ → Set X := fun i => ((↑) : U → X) '' compactCovering U i
  have hC : ∀ i, IsCompact (C i) := fun i =>
    (isCompact_compactCovering U i).image continuous_subtype_val
  have hCU : ∀ i, C i ⊆ U := by
    rintro i x ⟨y, _, rfl⟩
    exact y.property
  have hcover : ∀ x ∈ U, ∃ i, x ∈ C i := by
    intro x hx
    obtain ⟨i, hi⟩ := exists_mem_compactCovering (⟨x, hx⟩ : U)
    exact ⟨i, ⟨x, hx⟩, hi, rfl⟩
  have hbetween : ∀ {B : Set X}, IsCompact B → B ⊆ U →
      ∃ P : Set X, IsCompact P ∧ IsPolyhedralManifoldWithBoundary (n := m + 1) (m + 1) P ∧
        B ⊆ interior P ∧ P ⊆ U := by
    intro B hB hBU
    exact T.toPieceIn.exists_isPolyhedralManifoldWithBoundary_neighborhood
      hT.isCombinatorialManifoldWithBoundary hB hU hBU
  let S := {P : Set X // IsCompact P ∧
    IsPolyhedralManifoldWithBoundary (n := m + 1) (m + 1) P ∧ P ⊆ U}
  obtain ⟨P₀, hP₀c, hP₀m, _, hP₀U⟩ := hbetween isCompact_empty (empty_subset U)
  let start : S := ⟨P₀, hP₀c, hP₀m, hP₀U⟩
  have hstep : ∀ i (P : S), ∃ Q : S, P.val ∪ C i ⊆ interior Q.val := by
    intro i P
    obtain ⟨Q, hQc, hQm, hPQ, hQU⟩ := hbetween (P.property.1.union (hC i))
      (union_subset P.property.2.2 (hCU i))
    exact ⟨⟨Q, hQc, hQm, hQU⟩, hPQ⟩
  choose f hf using hstep
  let seq : ℕ → S := Nat.rec start (fun i P => f i P)
  refine ⟨fun i => (seq i).val, fun i =>
    ⟨(seq i).property.1, (seq i).property.2.1, ?_⟩, ?_⟩
  · intro x hx
    exact hf i (seq i) (Or.inl hx)
  · apply Subset.antisymm
    · intro x hx
      obtain ⟨i, hi⟩ := mem_iUnion.mp hx
      exact (seq i).property.2.2 hi
    · intro x hx
      obtain ⟨i, hi⟩ := hcover x hx
      exact mem_iUnion.mpr ⟨i + 1, interior_subset (hf i (seq i) (Or.inr hi))⟩

end DifferentialGeometry.Topology.PiecewiseLinear
