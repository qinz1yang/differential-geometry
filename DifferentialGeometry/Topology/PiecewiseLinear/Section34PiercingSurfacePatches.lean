import DifferentialGeometry.Topology.PiecewiseLinear.Exhaustion

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

private theorem image_mem_nhdsWithin_of_piece
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {n : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] {S : Set X}
    (T : PLPieceIn E n X S) {x : E} (hx : x ∈ T.complex.space) {A : Set E}
    (hA : A ∈ 𝓝[T.complex.space] x) : T.map '' A ∈ 𝓝[S] T.map x := by
  have : Finite T.complex.faces := T.finite_faces.to_subtype
  obtain ⟨O, hO, hxO, hOA⟩ := mem_nhdsWithin.mp hA
  have hclosed := (((isPolyhedron_space T.complex).isCompact.diff hO).image_of_continuousOn
    (T.continuousOn.mono sdiff_subset)).isClosed
  have hxnot : T.map x ∉ T.map '' (T.complex.space \ O) := by
    rintro ⟨y, ⟨hy, hyO⟩, hxy⟩
    exact hyO ((T.bijOn.injOn hy hx hxy).symm ▸ hxO)
  refine mem_nhdsWithin.mpr ⟨_, hclosed.isOpen_compl, hxnot, ?_⟩
  rintro y ⟨hy, hyS⟩
  obtain ⟨z, hz, rfl⟩ := T.bijOn.surjOn hyS
  have hzO : z ∈ O := by
    by_contra hzO
    exact hy ⟨z, ⟨hz, hzO⟩, rfl⟩
  exact mem_image_of_mem _ (hOA ⟨hzO, hz⟩)

theorem IsPolyhedralManifoldWithBoundary.exists_patch
    {n m : ℕ} {X : Type*} [TopologicalSpace X] [T2Space X]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] {S C O : Set X}
    (hS : IsPolyhedralManifoldWithBoundary (n := n) (m + 1) S)
    (hC : IsCompact C) (hCS : C ⊆ S) (hO : IsOpen O) (hCO : C ⊆ O) :
    ∃ W : Set X, IsPolyhedralManifoldWithBoundary (n := n) (m + 1) W ∧
      W ⊆ S ∩ O ∧ C ⊆ W ∧ ∀ x ∈ C, W ∈ 𝓝[S] x := by
  classical
  obtain ⟨P, hP⟩ := hS
  let T := P.piece
  have : Finite T.complex.faces := T.finite_faces.to_subtype
  have hcompact := (isPolyhedron_space T.complex).isCompact
  obtain ⟨V, hV, hpre⟩ := continuousOn_iff'.mp T.continuousOn O hO
  have hpreC : IsCompact (T.complex.space ∩ T.map ⁻¹' C) :=
    hcompact.of_isClosed_subset
      (T.continuousOn.preimage_isClosed_of_isClosed hcompact.isClosed hC.isClosed)
      inter_subset_left
  have hCV : T.complex.space ∩ T.map ⁻¹' C ⊆ V := by
    intro z hz
    have hzO : z ∈ T.map ⁻¹' O ∩ T.complex.space := ⟨hCO hz.2, hz.1⟩
    rw [hpre] at hzO
    exact hzO.1
  obtain ⟨K, L, hK, hKfin, hLK, hL, hLV, hnhds⟩ :=
    hP.exists_isSubdivision_neighborhood hpreC inter_subset_left hV hCV
  let Q := (T.subdivide K hK hKfin).restrict L hLK
  have hLS : L.space ⊆ T.complex.space := by
    rw [← hK.space_eq]
    exact space_mono_of_faces_subset hLK
  have hWnhds : ∀ x ∈ C, T.map '' L.space ∈ 𝓝[S] x := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := T.bijOn.surjOn (hCS hx)
    exact image_mem_nhdsWithin_of_piece T hy (hnhds y ⟨hy, hx⟩)
  refine ⟨T.map '' L.space, isPolyhedralManifoldWithBoundary_of_pieceIn Q hL, ?_,
    fun x hx => mem_of_mem_nhdsWithin (hCS hx) (hWnhds x hx), hWnhds⟩
  rintro y ⟨x, hx, rfl⟩
  refine ⟨T.bijOn.mapsTo (hLS hx), ?_⟩
  have hxV : x ∈ V ∩ T.complex.space := ⟨hLV hx, hLS hx⟩
  rw [← hpre] at hxV
  exact hxV.1

end DifferentialGeometry.Topology.PiecewiseLinear
