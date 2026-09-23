import DifferentialGeometry.Topology.PiecewiseLinear.Section34NestedPiercingRegularNeighborhood
import DifferentialGeometry.Topology.PiecewiseLinear.RelativeSubdivision
import DifferentialGeometry.Topology.PiecewiseLinear.SubdivisionSubordinateToCover

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_isSubdivision_union_of_preserved_intersection
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (K B C : Geometry.SimplicialComplex ℝ E)
    (hB : B.faces ⊆ K.faces) (hC : C.faces ⊆ K.faces)
    (hcover : K.faces = B.faces ∪ C.faces)
    (R : Geometry.SimplicialComplex ℝ E) (hR : IsSubdivision R B)
    (hkeep : B.faces ∩ C.faces ⊆ R.faces) :
    ∃ S : Geometry.SimplicialComplex ℝ E,
      IsSubdivision S K ∧ S.faces = R.faces ∪ C.faces := by
  classical
  have hcompat : ∀ s ∈ R.faces, ∀ t ∈ C.faces,
      convexHull ℝ (s : Set E) ∩ convexHull ℝ (t : Set E) ⊆
        convexHull ℝ ((s : Set E) ∩ (t : Set E)) := by
    intro s hs t ht x hx
    obtain ⟨u, hu, hsu⟩ := hR.exists_face_subset hs
    have hxi : x ∈ convexHull ℝ ((u ∩ t : Finset E) : Set E) := by
      simpa only [Finset.coe_inter] using
        K.inter_subset_convexHull (hB hu) (hC ht) ⟨hsu hx.1, hx.2⟩
    have hne : (u ∩ t).Nonempty := by
      by_contra hn
      simp only [Finset.not_nonempty_iff_eq_empty.mp hn, Finset.coe_empty,
        convexHull_empty, mem_empty_iff_false] at hxi
    have hiR : u ∩ t ∈ R.faces := hkeep
      ⟨B.down_closed hu Finset.inter_subset_left hne,
        C.down_closed ht Finset.inter_subset_right hne⟩
    apply convexHull_mono (inter_subset_inter_right (s : Set E)
      (show ((u ∩ t : Finset E) : Set E) ⊆ (t : Set E) from
        Finset.coe_subset.mpr Finset.inter_subset_right))
    exact R.inter_subset_convexHull hs hiR ⟨hx.1, hxi⟩
  let S := unionComplex R C hcompat
  refine ⟨S, ⟨?_, ?_⟩, rfl⟩
  · rw [unionComplex_space, hR.space_eq]
    ext x
    constructor
    · exact fun hx => hx.elim (fun h => space_mono_of_faces_subset hB h)
        (fun h => space_mono_of_faces_subset hC h)
    · intro hx
      obtain ⟨s, hs, hxs⟩ := K.mem_space_iff.mp hx
      rw [hcover] at hs
      exact hs.elim (fun h => Or.inl (B.convexHull_subset_space h hxs))
        (fun h => Or.inr (C.convexHull_subset_space h hxs))
  · intro s hs
    rcases hs with hs | hs
    · obtain ⟨t, ht, hst⟩ := hR.exists_face_subset hs
      exact ⟨t, hB ht, hst⟩
    · exact ⟨s, hC hs, Subset.rfl⟩

theorem exists_isSubdivision_restrict_space_of_finite_patch
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    (K B C : Geometry.SimplicialComplex ℝ E) [Finite B.faces]
    (hB : B.faces ⊆ K.faces) (hC : C.faces ⊆ K.faces)
    (hcover : K.faces = B.faces ∪ C.faces) {Q : Set E} (hQ : IsPolyhedron Q)
    (hQB : Q ⊆ B.space)
    (hdis : Disjoint (regularNeighborhoodIn B (restrict B C.space).space).space Q) :
    ∃ R : Geometry.SimplicialComplex ℝ E,
      IsSubdivision R K ∧ (R.faces \ K.faces).Finite ∧ C.faces ⊆ R.faces ∧
        (restrict R Q).space = Q := by
  obtain ⟨B', hB', hB'fin, hkeep, hQ'⟩ :=
    exists_isSubdivision_restrict_space_preserving_subcomplex B (restrict B C.space)
      (restrict_faces_subset B C.space) hQ hQB hdis
  have hkeep' : B.faces ∩ C.faces ⊆ B'.faces := fun s hs =>
    hkeep ((mem_restrict_faces_iff_of_faces_subset K B C hB hC).mpr hs)
  obtain ⟨R, hR, hfaces⟩ :=
    exists_isSubdivision_union_of_preserved_intersection K B C hB hC hcover B' hB' hkeep'
  have hB'R : B'.faces ⊆ R.faces := by rw [hfaces]; exact subset_union_left
  refine ⟨R, hR, ?_, ?_, Subset.antisymm (restrict_space_subset R Q) ?_⟩
  · apply hB'fin.subset
    rintro s ⟨hs, hsK⟩
    rw [hfaces] at hs
    exact hs.resolve_right fun h => hsK (hC h)
  · rw [hfaces]
    exact subset_union_right
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := (restrict B' Q).mem_space_iff.mp (hQ'.symm ▸ hx)
    exact (restrict R Q).convexHull_subset_space ⟨hB'R hs.1, hs.2⟩ hxs

theorem LocallyFinitePLPieceIn.exists_isSubdivision_restrict_space_finite_change
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] {U : Set X}
    (T : LocallyFinitePLPieceIn E 3 X U)
    (A : ℕ → Geometry.SimplicialComplex ℝ E)
    (hA : T.complex.faces = ⋃ i, (A i).faces)
    (hfin : ∀ i, (A i).faces.Finite) (hmono : Monotone fun i => (A i).faces)
    {Q : Set E} (hQ : IsPolyhedron Q) (hQT : Q ⊆ T.complex.space) :
    ∃ R : Geometry.SimplicialComplex ℝ E,
      IsSubdivision R T.complex ∧ (R.faces \ T.complex.faces).Finite ∧
        (restrict R Q).space = Q := by
  classical
  let F := {s : Finset E | s ∈ T.complex.faces ∧
    (convexHull ℝ (s : Set E) ∩ Q).Nonempty}
  have hF : F.Finite := T.finite_faces_inter_of_isCompact hQ.isCompact hQT
  let P := ⋃ s ∈ F, convexHull ℝ (s : Set E)
  have hP : IsCompact P :=
    hF.isCompact_biUnion fun s _ => s.finite_toSet.isCompact_convexHull ℝ
  have hPT : P ⊆ T.complex.space := by
    rintro x hx
    obtain ⟨s, hs, hxs⟩ := mem_iUnion₂.mp hx
    exact T.complex.convexHull_subset_space hs.1 hxs
  let F' := {s : Finset E | s ∈ T.complex.faces ∧
    (convexHull ℝ (s : Set E) ∩ P).Nonempty}
  have hF' : F'.Finite := T.finite_faces_inter_of_isCompact hP hPT
  have : Finite F' := hF'.to_subtype
  choose j hj using fun s : F' => mem_iUnion.mp (hA ▸ s.2.1)
  obtain ⟨k, hk⟩ := (finite_range j).bddAbove
  have hFA (s : Finset E) (hs : s ∈ F') : s ∈ (A k).faces :=
    hmono (hk (mem_range_self ⟨s, hs⟩)) (hj ⟨s, hs⟩)
  have hFF' : F ⊆ F' := by
    intro s hs
    obtain ⟨x, hxs, -⟩ := hs.2
    exact ⟨hs.1, x, hxs, mem_iUnion₂.mpr ⟨s, hs, hxs⟩⟩
  have hB : (A k).faces ⊆ T.complex.faces := by
    rw [hA]
    exact subset_iUnion (fun j => (A j).faces) k
  let C := subcomplexGeneratedBy T.complex (A k).facesᶜ
  have hC : C.faces ⊆ T.complex.faces :=
    subcomplexGeneratedBy_faces_subset T.complex (A k).facesᶜ
  have hcover : T.complex.faces = (A k).faces ∪ C.faces := by
    apply Subset.antisymm
    · intro s hs
      by_cases hsA : s ∈ (A k).faces
      · exact Or.inl hsA
      · exact Or.inr ⟨s, ⟨hs, hsA⟩, Finset.Subset.refl s,
          T.complex.nonempty_of_mem_faces hs⟩
    · exact union_subset hB hC
  have hQB : Q ⊆ (A k).space := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := T.complex.mem_space_iff.mp (hQT hx)
    exact (A k).convexHull_subset_space (hFA s (hFF' ⟨hs, x, hxs, hx⟩)) hxs
  have hdis : Disjoint (regularNeighborhoodIn (A k) (restrict (A k) C.space).space).space Q := by
    apply Set.disjoint_left.mpr
    intro x hx hxQ
    obtain ⟨s, ⟨-, t, ht, hst, y, hyt, hyI⟩, hxs⟩ :=
      (regularNeighborhoodIn (A k) (restrict (A k) C.space).space).mem_space_iff.mp hx
    have htF : t ∈ F :=
      ⟨hB ht, x, convexHull_mono (Finset.coe_subset.mpr hst) hxs, hxQ⟩
    have hyP : y ∈ P := mem_iUnion₂.mpr ⟨t, htF, hyt⟩
    obtain ⟨u, ⟨v, ⟨hvT, hvA⟩, huv, -⟩, hyu⟩ :=
      C.mem_space_iff.mp (restrict_space_subset (A k) C.space hyI)
    exact hvA (hFA v ⟨hvT, y, convexHull_mono (Finset.coe_subset.mpr huv) hyu, hyP⟩)
  have : Finite (A k).faces := (hfin k).to_subtype
  obtain ⟨R, hR, hnew, -, hRQ⟩ := exists_isSubdivision_restrict_space_of_finite_patch
    T.complex (A k) C hB hC hcover hQ hQB hdis
  exact ⟨R, hR, hnew, hRQ⟩

theorem LocallyFinitePLPieceIn.locallyFinite_of_isSubdivision_of_finite_new_faces
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {n : ℕ}
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin n)) X] {U : Set X}
    (T : LocallyFinitePLPieceIn E n X U) {R : Geometry.SimplicialComplex ℝ E}
    (hR : IsSubdivision R T.complex) (hfinite : (R.faces \ T.complex.faces).Finite) :
    LocallyFinite fun s : R.faces =>
      (Subtype.val : R.space → E) ⁻¹' convexHull ℝ ((s : Finset E) : Set E) := by
  rw [hR.space_eq]
  intro x
  obtain ⟨V, hV, hfin⟩ := T.locallyFinite x
  refine ⟨V, hV, ?_⟩
  have hbig := (hfin.image fun s : T.complex.faces => (s : Finset E)).union hfinite
  have hbound := hbig.preimage
    (f := fun s : R.faces => (s : Finset E)) Subtype.val_injective.injOn
  apply hbound.subset
  intro s hs
  by_cases hsK : (s : Finset E) ∈ T.complex.faces
  · exact Or.inl ⟨⟨s, hsK⟩, hs, rfl⟩
  · exact Or.inr ⟨s.2, hsK⟩

theorem restrict_faces_finite_of_finite_new_faces
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K R B : Geometry.SimplicialComplex ℝ E} (hB : B.faces ⊆ K.faces)
    (hfinB : B.faces.Finite) (hnew : (R.faces \ K.faces).Finite) :
    (restrict R B.space).faces.Finite := by
  apply (hfinB.union hnew).subset
  rintro s ⟨hsR, hsB⟩
  by_cases hsK : s ∈ K.faces
  · left
    exact mem_faces_of_mem_openSimplex_of_mem_space hB hsK
      (centroid_mem_openSimplex (K.nonempty_of_mem_faces hsK))
      (hsB (s.centroid_mem_convexHull (K.nonempty_of_mem_faces hsK)))
  · exact Or.inr ⟨hsR, hsK⟩

theorem LocallyFinitePLPieceIn.isLocallyFiniteRegularNeighborhoodOf_subdivision
    {m : ℕ} {X : Type*} [TopologicalSpace X]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] {U : Set X} (hU : IsOpen U)
    (T : LocallyFinitePLPieceIn (EuclideanSpace ℝ (Fin m)) 3 X U)
    (A : ℕ → Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m)))
    (hA : T.complex.faces = ⋃ i, (A i).faces)
    (hfin : ∀ i, (A i).faces.Finite) (hmono : Monotone fun i => (A i).faces)
    (hman : ∀ i, IsCombinatorialManifoldWithBoundary 3 (A i))
    (R : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m)))
    (hR : IsSubdivision R T.complex) (hnew : (R.faces \ T.complex.faces).Finite)
    (G : Geometry.SimplicialComplex ℝ (EuclideanSpace ℝ (Fin m))) [Finite G.faces]
    (hG : G.faces ⊆ R.faces) (hcard : ∀ s ∈ G.faces, s.card ≤ 2) :
    IsLocallyFiniteRegularNeighborhoodOf (n := 3)
      (T.map '' (@derivedNeighborhood _ _ _ (Classical.decEq _) R G).space)
      (T.map '' G.space) U := by
  let T' := T.subdivide R hR
    (T.locallyFinite_of_isSubdivision_of_finite_new_faces hR hnew)
  let B (i : ℕ) := restrict R (A i).space
  have hsub (i : ℕ) : (A i).faces ⊆ T.complex.faces := by
    rw [hA]
    exact subset_iUnion (fun j => (A j).faces) i
  have hcover : T'.complex.faces = ⋃ i, (B i).faces := by
    apply Subset.antisymm
    · intro s hs
      obtain ⟨t, ht, hst⟩ := hR.exists_face_subset hs
      obtain ⟨i, hi⟩ := mem_iUnion.mp (hA ▸ ht)
      exact mem_iUnion.mpr ⟨i, hs, hst.trans ((A i).convexHull_subset_space hi)⟩
    · exact iUnion_subset fun i => restrict_faces_subset R (A i).space
  have hBfin (i : ℕ) : (B i).faces.Finite :=
    restrict_faces_finite_of_finite_new_faces (hsub i) (hfin i) hnew
  have hBmono : Monotone fun i => (B i).faces := by
    intro i j hij s hs
    exact ⟨hs.1, hs.2.trans (space_mono_of_faces_subset (hmono hij))⟩
  have hBman (i : ℕ) : IsCombinatorialManifoldWithBoundary 3 (B i) := by
    have : Finite (A i).faces := (hfin i).to_subtype
    have : Finite (B i).faces := (hBfin i).to_subtype
    exact (hman i).of_isSubdivision (hR.restrict (A i) (hsub i))
  exact T'.isLocallyFiniteRegularNeighborhoodOf_derivedNeighborhood hU B hcover hBfin
    hBmono hBman G hG hcard

theorem LocallyFinitePLPieceIn.isPLSphere_preimage_of_isPolyhedralSphere
    {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X] {U : Set X}
    (T : LocallyFinitePLPieceIn E 3 X U)
    (A : ℕ → Geometry.SimplicialComplex ℝ E)
    (hA : T.complex.faces = ⋃ i, (A i).faces)
    (hfin : ∀ i, (A i).faces.Finite) (hmono : Monotone fun i => (A i).faces)
    {d : ℕ} {C : Set X} (hC : IsPolyhedralSphere (n := 3) d C) (hCU : C ⊆ U) :
    IsPLSphere d (T.complex.space ∩ T.map ⁻¹' C) := by
  classical
  obtain ⟨P, hP⟩ := hC
  have hCc : IsCompact C := by
    rw [← P.piece.bijOn.image_eq]
    exact P.piece.isPolyhedron_space.isCompact.image_of_continuousOn P.piece.continuousOn
  have hrange : Set.range (fun x : T.complex.space => T.map x) = U :=
    (Set.image_eq_range T.map T.complex.space).symm.trans T.bijOn.image_eq
  have hpre : IsCompact ((fun x : T.complex.space => T.map x) ⁻¹' C) := by
    apply T.isEmbedding.isCompact_iff.mpr
    rwa [image_preimage_eq_iff.mpr (hrange.symm ▸ hCU)]
  let Q := T.complex.space ∩ T.map ⁻¹' C
  have hQc : IsCompact Q := by
    convert hpre.image continuous_subtype_val using 1
    ext x
    simp only [mem_image, mem_preimage, Subtype.exists, exists_and_right,
      exists_eq_right, mem_inter_iff, Q, exists_prop]
  let F := {s : Finset E | s ∈ T.complex.faces ∧
    (convexHull ℝ (s : Set E) ∩ Q).Nonempty}
  have hF : F.Finite := T.finite_faces_inter_of_isCompact hQc inter_subset_left
  have : Finite F := hF.to_subtype
  choose j hj using fun s : F => mem_iUnion.mp (hA ▸ s.2.1)
  obtain ⟨k, hk⟩ := (finite_range j).bddAbove
  have hQk : Q ⊆ (A k).space := by
    intro x hx
    obtain ⟨s, hs, hxs⟩ := T.complex.mem_space_iff.mp hx.1
    have hsF : s ∈ F := ⟨hs, x, hxs, hx⟩
    exact (A k).convexHull_subset_space
      (hmono (hk (mem_range_self ⟨s, hsF⟩)) (hj ⟨s, hsF⟩)) hxs
  have hsub : (A k).space ⊆ T.complex.space := space_mono_of_faces_subset (by
    rw [hA]
    exact subset_iUnion (fun i => (A i).faces) k)
  have : Finite (A k).faces := (hfin k).to_subtype
  let S := T.finiteRestriction (A k) hsub
  have hCS : C ⊆ T.map '' (A k).space := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := T.bijOn.surjOn (hCU hx)
    exact ⟨y, hQk ⟨hy, hx⟩, rfl⟩
  have htransition := P.piece.isPLHomeomorphOn_transition_of_subset S hCS
  have heq : (A k).space ∩ T.map ⁻¹' C = Q :=
    Subset.antisymm (fun x hx => ⟨hsub hx.1, hx.2⟩) (fun x hx => ⟨hQk hx, hx.2⟩)
  change IsPLSphere d Q
  rw [← heq]
  exact hP.of_isPLHomeomorphOn htransition

theorem IsPLDerivedNeighborhoodExhaustion.exists_regularNeighborhood_of_isPolyhedralSphere
    {X : Type*} [TopologicalSpace X] [ChartedSpace (EuclideanSpace ℝ (Fin 3)) X]
    {N K U C : Set X} (h : IsPLDerivedNeighborhoodExhaustion (n := 3) N K U)
    (hU : IsOpen U) (hC : IsPolyhedralSphere (n := 3) 1 C) (hCU : C ⊆ U) :
    ∃ S : Set X, IsLocallyFiniteRegularNeighborhoodOf (n := 3) S C U := by
  classical
  obtain ⟨m, T, A, -, hcover, hfin, -, -, hman, -, hmono, -⟩ := h
  let _ : DecidableEq (EuclideanSpace ℝ (Fin m)) := Classical.decEq _
  let Q := T.complex.space ∩ T.map ⁻¹' C
  have hQ : IsPLSphere 1 Q :=
    T.isPLSphere_preimage_of_isPolyhedralSphere A hcover hfin hmono hC hCU
  obtain ⟨R, hR, hnew, hRQ⟩ := T.exists_isSubdivision_restrict_space_finite_change
    A hcover hfin hmono hQ.isPolyhedron inter_subset_left
  let T' := T.subdivide R hR
    (T.locallyFinite_of_isSubdivision_of_finite_new_faces hR hnew)
  let G := restrict R Q
  have hQR : Q ⊆ R.space := inter_subset_left.trans hR.space_eq.symm.subset
  have hfaces : G.faces.Finite := by
    apply (T'.finite_faces_inter_of_isCompact hQ.isPolyhedron.isCompact hQR).subset
    rintro s ⟨hs, hsQ⟩
    have hcent : s.centroid ℝ id ∈ convexHull ℝ (s : Set (EuclideanSpace ℝ (Fin m))) :=
      s.centroid_mem_convexHull (R.nonempty_of_mem_faces hs)
    exact ⟨hs, s.centroid ℝ id, hcent, hsQ hcent⟩
  have : Finite G.faces := hfaces.to_subtype
  have hG : IsPLSphere 1 G.space := hRQ.symm ▸ hQ
  have hcard : ∀ s ∈ G.faces, s.card ≤ 2 := fun s hs => card_le_of_isPLSphere G hG hs
  have hreg := T.isLocallyFiniteRegularNeighborhoodOf_subdivision hU A hcover hfin hmono
    hman R hR hnew G (restrict_faces_subset R Q) hcard
  have himage : T.map '' G.space = C := by
    rw [hRQ]
    change T.map '' (T.complex.space ∩ T.map ⁻¹' C) = C
    rw [image_inter_preimage, T.bijOn.image_eq, inter_eq_right.mpr hCU]
  exact ⟨_, himage ▸ hreg⟩

end DifferentialGeometry.Topology.PiecewiseLinear
