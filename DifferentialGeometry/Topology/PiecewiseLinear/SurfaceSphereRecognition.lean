import DifferentialGeometry.Topology.PiecewiseLinear.DualCellDecomposition
import DifferentialGeometry.Topology.PiecewiseLinear.EulerPolyhedra
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldSubcomplexBoundary
import DifferentialGeometry.Topology.PiecewiseLinear.SurfaceTreeNeighborhood

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
noncomputable def derivedNeighborhoodCellsComplex
    (K : Geometry.SimplicialComplex ℝ E) (S : Set (Finset E)) :
    Geometry.SimplicialComplex ℝ E where
  faces := {u | ∃ s ∈ S, u ∈ (derivedNeighborhoodCell K s).faces}
  isRelLowerSet_faces := by
    rintro u ⟨s, hsS, hu⟩
    exact ⟨(derivedNeighborhoodCell K s).nonempty_of_mem_faces hu,
      fun t htu ht => ⟨s, hsS, (derivedNeighborhoodCell K s).down_closed hu htu ht⟩⟩
  indep := by
    rintro u ⟨s, -, hu⟩
    exact (secondDerived K).indep (derivedNeighborhoodCell_faces_subset K s hu)
  inter_subset_convexHull := by
    rintro u v ⟨s, -, hu⟩ ⟨t, -, hv⟩
    exact (secondDerived K).inter_subset_convexHull
      (derivedNeighborhoodCell_faces_subset K s hu)
      (derivedNeighborhoodCell_faces_subset K t hv)

theorem mem_derivedNeighborhoodCellsComplex_faces_iff
    (K : Geometry.SimplicialComplex ℝ E) (S : Set (Finset E)) {u : Finset E} :
    u ∈ (derivedNeighborhoodCellsComplex K S).faces ↔
      ∃ s ∈ S, u ∈ (derivedNeighborhoodCell K s).faces :=
  Iff.rfl

open Classical in
theorem derivedNeighborhoodCellsComplex_faces_subset
    (K : Geometry.SimplicialComplex ℝ E) (S : Set (Finset E)) :
    (derivedNeighborhoodCellsComplex K S).faces ⊆ (secondDerived K).faces := by
  rintro u ⟨s, -, hu⟩
  exact derivedNeighborhoodCell_faces_subset K s hu

open Classical in
theorem derivedNeighborhoodCellsComplex_faces_finite
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces] (S : Set (Finset E)) :
    (derivedNeighborhoodCellsComplex K S).faces.Finite :=
  (Set.toFinite (secondDerived K).faces).subset
    (derivedNeighborhoodCellsComplex_faces_subset K S)

open Classical in
theorem derivedNeighborhoodCellsComplex_space
    (K : Geometry.SimplicialComplex ℝ E) (S : Set (Finset E)) :
    (derivedNeighborhoodCellsComplex K S).space =
      ⋃ s ∈ S, (derivedNeighborhoodCell K s).space := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨u, ⟨s, hsS, hu⟩, hxu⟩ := (derivedNeighborhoodCellsComplex K S).mem_space_iff.mp hx
    exact mem_iUnion₂.mpr ⟨s, hsS,
      (derivedNeighborhoodCell K s).convexHull_subset_space hu hxu⟩
  · intro x hx
    obtain ⟨s, hsS, hxs⟩ := mem_iUnion₂.mp hx
    obtain ⟨u, hu, hxu⟩ := (derivedNeighborhoodCell K s).mem_space_iff.mp hxs
    exact (derivedNeighborhoodCellsComplex K S).convexHull_subset_space ⟨s, hsS, hu⟩ hxu

open Classical in
theorem exists_mem_derivedNeighborhoodCell_of_mem_secondDerived
    (K : Geometry.SimplicialComplex ℝ E) {u : Finset E}
    (hu : u ∈ (secondDerived K).faces) :
    ∃ s ∈ K.faces, u ∈ (derivedNeighborhoodCell K s).faces := by
  obtain ⟨d, hd, hdne, rfl⟩ := hu
  obtain ⟨e, he, hbot⟩ := hd.exists_bot hdne
  obtain ⟨s, hs, hse⟩ :=
    exists_mem_image_centroid_of_mem_barycentricSubdivision (hd.mem_faces he)
  refine ⟨s, hs, (mem_derivedNeighborhoodCell_faces_iff_of_flag hs hd hdne).mpr ?_⟩
  intro q hq
  exact hbot q hq hse

def commonFacesComplex (A B : Geometry.SimplicialComplex ℝ E) :
    Geometry.SimplicialComplex ℝ E where
  faces := A.faces ∩ B.faces
  isRelLowerSet_faces := by
    rintro s ⟨hsA, hsB⟩
    exact ⟨A.nonempty_of_mem_faces hsA, fun t hts ht =>
      ⟨A.down_closed hsA hts ht, B.down_closed hsB hts ht⟩⟩
  indep hs := A.indep hs.1
  inter_subset_convexHull hs ht := A.inter_subset_convexHull hs.1 ht.1

theorem commonFacesComplex_faces_finite
    (A B : Geometry.SimplicialComplex ℝ E) (hA : A.faces.Finite) :
    (commonFacesComplex A B).faces.Finite :=
  hA.subset fun _ hs => hs.1

instance finite_commonFacesComplex_faces
    (A B : Geometry.SimplicialComplex ℝ E) [Finite A.faces] :
    Finite (commonFacesComplex A B).faces :=
  (commonFacesComplex_faces_finite A B (Set.toFinite A.faces)).to_subtype

open Classical in
theorem commonFacesComplex_space_eq_inter_of_faces_subset
    (R A B : Geometry.SimplicialComplex ℝ E)
    (hAR : A.faces ⊆ R.faces) (hBR : B.faces ⊆ R.faces) :
    (commonFacesComplex A B).space = A.space ∩ B.space := by
  apply Subset.antisymm
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := (commonFacesComplex A B).mem_space_iff.mp hx
    exact ⟨A.convexHull_subset_space hs.1 hxs, B.convexHull_subset_space hs.2 hxs⟩
  · rintro x ⟨hxA, hxB⟩
    obtain ⟨s, hsA, hxs⟩ := exists_face_mem_openSimplex A hxA
    have hsB := mem_faces_of_mem_openSimplex_of_mem_space hBR (hAR hsA) hxs hxB
    exact (commonFacesComplex A B).convexHull_subset_space ⟨hsA, hsB⟩
      (openSimplex_subset_convexHull s hxs)

open Classical in
theorem union_space_eq_of_faces_cover
    (R A B : Geometry.SimplicialComplex ℝ E)
    (hAR : A.faces ⊆ R.faces) (hBR : B.faces ⊆ R.faces)
    (hcover : ∀ s ∈ R.faces, s ∈ A.faces ∨ s ∈ B.faces) :
    A.space ∪ B.space = R.space := by
  apply Subset.antisymm
  · exact union_subset (space_mono_of_faces_subset hAR) (space_mono_of_faces_subset hBR)
  · intro x hx
    obtain ⟨s, hs, hxs⟩ := R.mem_space_iff.mp hx
    rcases hcover s hs with hsA | hsB
    · exact Or.inl (A.convexHull_subset_space hsA hxs)
    · exact Or.inr (B.convexHull_subset_space hsB hxs)

open Classical in
theorem subcomplexGeneratedBy_compl_eq_of_faces_cover_of_pure_inter
    [FiniteDimensional ℝ E] (R A B : Geometry.SimplicialComplex ℝ E)
    [Finite B.faces] (hB : IsPLBall 2 B.space)
    (hBR : B.faces ⊆ R.faces)
    (hcover : ∀ s ∈ R.faces, s ∈ A.faces ∨ s ∈ B.faces)
    (hpure : ∀ s, s ∈ A.faces → s ∈ B.faces →
      ∃ t ∈ A.faces ∩ B.faces, s ⊆ t ∧ t.card = 2) :
    subcomplexGeneratedBy R A.facesᶜ = B := by
  ext s
  constructor
  · rintro ⟨t, ⟨htR, htA⟩, hst, hs⟩
    rcases hcover t htR with htA' | htB
    · exact (htA htA').elim
    · exact B.down_closed htB hst hs
  · intro hsB
    obtain ⟨t, htB, hst, htcard⟩ := exists_face_superset_card_eq_of_isPLBall B hB hsB
    refine ⟨t, ⟨hBR htB, ?_⟩, hst, B.nonempty_of_mem_faces hsB⟩
    intro htA
    obtain ⟨u, -, htu, hucard⟩ := hpure t htA htB
    have hcard := Finset.card_le_card htu
    omega

open Classical in
theorem isPLSphere_two_of_isPLBall_faces_cover
    [FiniteDimensional ℝ E] (R A B : Geometry.SimplicialComplex ℝ E)
    [Finite R.faces] [Finite A.faces] [Finite B.faces]
    (hR : IsCombinatorialManifold 2 R)
    (hA : IsPLBall 2 A.space) (hB : IsPLBall 2 B.space)
    (hAR : A.faces ⊆ R.faces) (hBR : B.faces ⊆ R.faces)
    (hcover : ∀ s ∈ R.faces, s ∈ A.faces ∨ s ∈ B.faces)
    (hpure : ∀ s, s ∈ A.faces → s ∈ B.faces →
      ∃ t ∈ A.faces ∩ B.faces, s ⊆ t ∧ t.card = 2) :
    IsPLSphere 2 R.space := by
  let A' := boundaryRelSubdivision 2 A
  let I := boundaryComplex 2 A
  let _ : Finite A'.faces := (boundaryRelSubdivision_faces_finite 2 A).to_subtype
  let _ : Finite I.faces := (boundaryComplex_faces_finite 2 A).to_subtype
  have hcompA : subcomplexGeneratedBy R A.facesᶜ = B :=
    subcomplexGeneratedBy_compl_eq_of_faces_cover_of_pure_inter R A B hB hBR hcover hpure
  have hcompB : subcomplexGeneratedBy R B.facesᶜ = A :=
    subcomplexGeneratedBy_compl_eq_of_faces_cover_of_pure_inter R B A hA hAR
      (fun s hs => (hcover s hs).symm) fun s hsB hsA => by
        obtain ⟨t, ht, hst, htcard⟩ := hpure s hsA hsB
        exact ⟨t, ⟨ht.2, ht.1⟩, hst, htcard⟩
  have hBA : closure (R.space \ A.space) = B.space := by
    rw [closure_space_sdiff_space_eq_subcomplexGeneratedBy R R A Subset.rfl hAR, hcompA]
  have hAB : closure (R.space \ B.space) = A.space := by
    rw [closure_space_sdiff_space_eq_subcomplexGeneratedBy R R B Subset.rfl hBR, hcompB]
  have hinterA := inter_closure_sdiff_space_eq_boundaryComplex_of_isCombinatorialManifold
    R A hR hA.isCombinatorialManifoldWithBoundary hAR
  have hinterB := inter_closure_sdiff_space_eq_boundaryComplex_of_isCombinatorialManifold
    R B hR hB.isCombinatorialManifoldWithBoundary hBR
  rw [hBA] at hinterA
  rw [hAB] at hinterB
  have hboundary : boundaryComplex 2 A = boundaryComplex 2 B := by
    apply eq_of_faces_subset_of_space_eq (boundaryComplex 2 A) (boundaryComplex 2 B) R
    · exact (boundaryComplex_faces_subset 2 A).trans hAR
    · exact (boundaryComplex_faces_subset 2 B).trans hBR
    · calc
        (boundaryComplex 2 A).space = A.space ∩ B.space := hinterA.symm
        _ = B.space ∩ A.space := inter_comm _ _
        _ = (boundaryComplex 2 B).space := hinterB
  have hAsub : IsSubdivision A' A := boundaryRelSubdivision_isSubdivision 2 A
  have hA' : IsPLBall 2 A'.space := by
    rw [hAsub.space_eq]
    exact hA
  have hI1 : I = boundaryComplex 2 A' := by
    dsimp only [I, A']
    exact (boundaryComplex_boundaryRelSubdivision A
      hA.isCombinatorialManifoldWithBoundary).symm
  have hI2 : I = boundaryComplex 2 B := by
    simpa only [I] using hboundary
  have hIA' : I.faces ⊆ A'.faces := by
    rw [hI1]
    exact boundaryComplex_faces_subset 2 A'
  have hIB : I.faces ⊆ B.faces := by
    rw [hI2]
    exact boundaryComplex_faces_subset 2 B
  have hfull : ∀ s ∈ A'.faces, (∀ v ∈ s, {v} ∈ I.faces) → s ∈ I.faces := by
    intro s hs hv
    exact boundaryComplex_full_boundaryRelSubdivision 2 A s hs hv
  have hsphere := isPLSphere_gluedComplex_of_isPLBall A' B I hA' hB hI1 hI2 hfull
  have hgA : IsPLHomeomorphOn id A'.space A.space := by
    rw [hAsub.space_eq]
    exact (isPolyhedron_space A).isPLHomeomorphOn_id
  have hgB : IsPLHomeomorphOn id B.space B.space :=
    (isPolyhedron_space B).isPLHomeomorphOn_id
  have hcompat : ∀ x ∈ I.space, id (simplicialMap I id x) = id x := by
    intro x hx
    simpa only [id_eq] using simplicialMap_id_eq_of_mem I hx
  have hoverlap : A.space ∩ B.space = id '' I.space := by
    rw [hinterA]
    simp only [I, image_id]
  have hmap := isPLHomeomorphOn_gluedMap_of_full A' B I I id id
    (isGlueIso_id I) hIA' hIB hfull id id A.space B.space hgA hgB hcompat hoverlap
  have hunion : IsPLSphere 2 (A.space ∪ B.space) := hsphere.of_isPLHomeomorphOn hmap
  rwa [union_space_eq_of_faces_cover R A B hAR hBR hcover] at hunion

open Classical in
noncomputable def primalTreeCellFaces (K : Geometry.SimplicialComplex ℝ E)
    (T : SimpleGraph K.vertices) : Set (Finset E) :=
  {s | s ∈ K.faces ∧ (s.card = 1 ∨ s ∈ spanningTreeFaces K T)}

open Classical in
noncomputable def dualCotreeCellFaces (K : Geometry.SimplicialComplex ℝ E)
    (T : SimpleGraph K.vertices) : Set (Finset E) :=
  {s | s ∈ K.faces ∧
    (s.card = 3 ∨ s.card = 2 ∧ s ∉ spanningTreeFaces K T)}

open Classical in
noncomputable def primalTreeCellComplex (K : Geometry.SimplicialComplex ℝ E)
    (T : SimpleGraph K.vertices) : Geometry.SimplicialComplex ℝ E :=
  derivedNeighborhoodCellsComplex K (primalTreeCellFaces K T)

open Classical in
noncomputable def dualCotreeCellComplex (K : Geometry.SimplicialComplex ℝ E)
    (T : SimpleGraph K.vertices) : Geometry.SimplicialComplex ℝ E :=
  derivedNeighborhoodCellsComplex K (dualCotreeCellFaces K T)

open Classical in
theorem primalTreeCellFaces_subset_faces
    (K : Geometry.SimplicialComplex ℝ E) (T : SimpleGraph K.vertices) :
    primalTreeCellFaces K T ⊆ K.faces :=
  fun _ hs => hs.1

open Classical in
theorem dualCotreeCellFaces_subset_faces
    (K : Geometry.SimplicialComplex ℝ E) (T : SimpleGraph K.vertices) :
    dualCotreeCellFaces K T ⊆ K.faces :=
  fun _ hs => hs.1

open Classical in
theorem primalTreeCellFaces_disjoint_dualCotreeCellFaces
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {T : SimpleGraph K.vertices} (hT : T ≤ SimplicialComplex.edgeGraph K) :
    Disjoint (primalTreeCellFaces K T) (dualCotreeCellFaces K T) := by
  rw [Set.disjoint_left]
  intro s hsP hsD
  rcases hsP.2 with hcard | hsT
  · rcases hsD.2 with hcard' | hcard'
    · omega
    · omega
  · have hcard := (SimplicialComplex.mem_facesOfCard
      K.toPreAbstractSimplicialComplex).mp
        (spanningTreeFaces_subset_facesOfCard_two K hT hsT) |>.2
    rcases hsD.2 with hcard' | hcard'
    · omega
    · exact hcard'.2 hsT

open Classical in
theorem mem_primalTreeCellFaces_or_mem_dualCotreeCellFaces
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) {T : SimpleGraph K.vertices}
    {s : Finset E} (hs : s ∈ K.faces) :
    s ∈ primalTreeCellFaces K T ∨ s ∈ dualCotreeCellFaces K T := by
  have hpos : 0 < s.card := Finset.card_pos.mpr (K.nonempty_of_mem_faces hs)
  have hle : s.card ≤ 3 := by simpa using hK.card_le K hs
  rcases (show s.card = 1 ∨ s.card = 2 ∨ s.card = 3 by omega) with hcard | hcard | hcard
  · exact Or.inl ⟨hs, Or.inl hcard⟩
  · by_cases hst : s ∈ spanningTreeFaces K T
    · exact Or.inl ⟨hs, Or.inr hst⟩
    · exact Or.inr ⟨hs, Or.inr ⟨hcard, hst⟩⟩
  · exact Or.inr ⟨hs, Or.inl hcard⟩

open Classical in
theorem primalTreeCellComplex_space
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    {T : SimpleGraph K.vertices} (hT : T ≤ SimplicialComplex.edgeGraph K) :
    (primalTreeCellComplex K T).space =
      embeddedGraphDerivedNeighborhood K T (fun v => v) := by
  rw [primalTreeCellComplex, derivedNeighborhoodCellsComplex_space]
  apply Subset.antisymm
  · intro x hx
    obtain ⟨s, ⟨hsK, hs⟩, hxs⟩ := mem_iUnion₂.mp hx
    rcases hs with hscard | hsT
    · obtain ⟨v, rfl⟩ := Finset.card_eq_one.mp hscard
      have hv : {v} ∈ K.faces := hsK
      exact mem_embeddedGraphDerivedNeighborhood_iff.mpr
        (Or.inl ⟨⟨v, hv⟩, by simpa only [embeddedVertexFace] using hxs⟩)
    · obtain ⟨e, heT, heq⟩ := hsT
      induction e using Sym2.inductionOn with
      | _ u v =>
          have huv : T.Adj u v := T.mem_edgeSet.mp heT
          apply mem_embeddedGraphDerivedNeighborhood_iff.mpr
          refine Or.inr ⟨u, v, huv, ?_⟩
          have hface : embeddedEdgeFace (fun z : K.vertices => z) u v = s := by
            simpa only [embeddedEdgeFace, edgeGraphFace, Sym2.map_mk,
              Sym2.toFinset_mk_eq] using heq
          simpa only [hface] using hxs
  · intro x hx
    rcases mem_embeddedGraphDerivedNeighborhood_iff.mp hx with
        ⟨u, hxu⟩ | ⟨u, v, huv, hxuv⟩
    · refine mem_iUnion₂.mpr ⟨{(u : E)}, ?_, by simpa only [embeddedVertexFace] using hxu⟩
      exact ⟨u.2, Or.inl (Finset.card_singleton _)⟩
    · let e : Sym2 K.vertices := s(u, v)
      have heT : e ∈ T.edgeSet := T.mem_edgeSet.mpr huv
      have heK : e ∈ (SimplicialComplex.edgeGraph K).edgeSet :=
        SimpleGraph.edgeSet_mono hT heT
      let q := edgeGraphFace K e
      refine mem_iUnion₂.mpr ⟨q, ?_, ?_⟩
      · exact ⟨(SimplicialComplex.mem_facesOfCard K.toPreAbstractSimplicialComplex).mp
          (edgeGraphFace_mem_facesOfCard_two K heK) |>.1,
          Or.inr ⟨e, heT, rfl⟩⟩
      · simpa only [q, e, embeddedEdgeFace, edgeGraphFace, Sym2.map_mk,
          Sym2.toFinset_mk_eq] using hxuv

open Classical in
theorem dualCotreeCellComplex_space
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (T : SimpleGraph K.vertices) :
    (dualCotreeCellComplex K T).space =
      embeddedDualTreeDerivedNeighborhood K (dualCotreeGraph K T) (fun s => s) := by
  rw [dualCotreeCellComplex, derivedNeighborhoodCellsComplex_space]
  apply Subset.antisymm
  · intro x hx
    obtain ⟨s, ⟨hsK, hs⟩, hxs⟩ := mem_iUnion₂.mp hx
    rcases hs with hscard | hs
    · let t : {s : Finset E // s ∈ K.faces ∧ s.card = 3} := ⟨s, hsK, hscard⟩
      exact mem_embeddedDualTreeDerivedNeighborhood_iff K (dualCotreeGraph K T) (fun q => q) |>.mpr
        (Or.inl ⟨t, by simpa only [t] using hxs⟩)
    · have hsF : s ∈ SimplicialComplex.facesOfCard K.toPreAbstractSimplicialComplex 2 :=
        (SimplicialComplex.mem_facesOfCard K.toPreAbstractSimplicialComplex).mpr ⟨hsK, hs.1⟩
      obtain ⟨e, he, heq⟩ :=
        (dualGraphSharedFace_bijOn_dualCotreeGraph K hK T).2.2 ⟨hsF, hs.2⟩
      induction e using Sym2.inductionOn with
      | _ u v =>
          have huv : (dualCotreeGraph K T).Adj u v :=
            (dualCotreeGraph K T).mem_edgeSet.mp he
          apply mem_embeddedDualTreeDerivedNeighborhood_iff K (dualCotreeGraph K T) (fun q => q) |>.mpr
          refine Or.inr ⟨u, v, huv, ?_⟩
          have hface : u.1 ∩ v.1 = s := by
            simpa only [dualGraphSharedFace, Sym2.lift_mk] using heq
          simpa only [hface] using hxs
  · intro x hx
    rcases mem_embeddedDualTreeDerivedNeighborhood_iff K (dualCotreeGraph K T) (fun q => q) |>.mp hx with
        ⟨s, hxs⟩ | ⟨s, t, hst, hxst⟩
    · exact mem_iUnion₂.mpr ⟨s.1, ⟨s.2.1, Or.inl s.2.2⟩, hxs⟩
    · let q := s.1 ∩ t.1
      have hqF := dualGraph_sharedFace_mem_facesOfCard_two K hst.1
      obtain ⟨hqK, hqcard⟩ :=
        (SimplicialComplex.mem_facesOfCard K.toPreAbstractSimplicialComplex).mp hqF
      exact mem_iUnion₂.mpr ⟨q, ⟨hqK, Or.inr ⟨hqcard, hst.2⟩⟩,
        by simpa only [q] using hxst⟩

open Classical in
theorem isPLBall_primalTreeCellComplex
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) {T : SimpleGraph K.vertices}
    (hT : T ≤ SimplicialComplex.edgeGraph K) (hTree : T.IsTree) :
    IsPLBall 2 (primalTreeCellComplex K T).space := by
  let _ : Finite K.vertices := (SimplicialComplex.finite_vertices K).to_subtype
  rw [primalTreeCellComplex_space K hT]
  exact isPLBall_embeddedGraphDerivedNeighborhood_of_isTree K hK T (fun v => v)
    Function.injective_id hT hTree

open Classical in
theorem isPLBall_dualCotreeCellComplex
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (T : SimpleGraph K.vertices)
    (hTree : (dualCotreeGraph K T).IsTree) :
    IsPLBall 2 (dualCotreeCellComplex K T).space := by
  have hfinite : Set.Finite {s : Finset E | s ∈ K.faces ∧ s.card = 3} :=
    (Set.toFinite K.faces).subset fun _ hs => hs.1
  let _ : Finite {s : Finset E // s ∈ K.faces ∧ s.card = 3} := hfinite.to_subtype
  rw [dualCotreeCellComplex_space K hK T]
  exact isPLBall_embeddedDualTreeDerivedNeighborhood_of_isTree K hK
    (dualCotreeGraph K T) (fun s => s) Function.injective_id
    (dualCotreeGraph_le_dualGraph K T) hTree

open Classical in
theorem primalTreeCellComplex_faces_subset_secondDerived
    (K : Geometry.SimplicialComplex ℝ E) (T : SimpleGraph K.vertices) :
    (primalTreeCellComplex K T).faces ⊆ (secondDerived K).faces :=
  derivedNeighborhoodCellsComplex_faces_subset K (primalTreeCellFaces K T)

open Classical in
theorem dualCotreeCellComplex_faces_subset_secondDerived
    (K : Geometry.SimplicialComplex ℝ E) (T : SimpleGraph K.vertices) :
    (dualCotreeCellComplex K T).faces ⊆ (secondDerived K).faces :=
  derivedNeighborhoodCellsComplex_faces_subset K (dualCotreeCellFaces K T)

open Classical in
theorem mem_primalTreeCellComplex_or_mem_dualCotreeCellComplex
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (T : SimpleGraph K.vertices)
    {u : Finset E} (hu : u ∈ (secondDerived K).faces) :
    u ∈ (primalTreeCellComplex K T).faces ∨
      u ∈ (dualCotreeCellComplex K T).faces := by
  obtain ⟨s, hsK, hus⟩ := exists_mem_derivedNeighborhoodCell_of_mem_secondDerived K hu
  rcases mem_primalTreeCellFaces_or_mem_dualCotreeCellFaces K hK hsK with hs | hs
  · exact Or.inl ⟨s, hs, hus⟩
  · exact Or.inr ⟨s, hs, hus⟩

open Classical in
theorem primalTreeCellComplex_dualCotreeCellComplex_pure_inter
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) {T : SimpleGraph K.vertices}
    (hT : T ≤ SimplicialComplex.edgeGraph K) {u : Finset E}
    (huP : u ∈ (primalTreeCellComplex K T).faces)
    (huD : u ∈ (dualCotreeCellComplex K T).faces) :
    ∃ v ∈ (primalTreeCellComplex K T).faces ∩ (dualCotreeCellComplex K T).faces,
      u ⊆ v ∧ v.card = 2 := by
  obtain ⟨s, hsP, hus⟩ := huP
  obtain ⟨t, htD, hut⟩ := huD
  have hst : s ≠ t := by
    intro heq
    subst t
    exact Set.disjoint_left.mp
      (primalTreeCellFaces_disjoint_dualCotreeCellFaces K hT) hsP htD
  have huNonempty := (derivedNeighborhoodCell K s).nonempty_of_mem_faces hus
  have hxu := centroid_mem_openSimplex huNonempty
  have hxuConvex := openSimplex_subset_convexHull u hxu
  have hnonempty :
      ((derivedNeighborhoodCell K s).space ∩
        (derivedNeighborhoodCell K t).space).Nonempty :=
    ⟨u.centroid ℝ id,
      (derivedNeighborhoodCell K s).convexHull_subset_space hus hxuConvex,
      (derivedNeighborhoodCell K t).convexHull_subset_space hut hxuConvex⟩
  have hball := hK.isCombinatorialManifoldWithBoundary
    |>.isPLBall_derivedNeighborhoodCell_inter_of_nonempty hsP.1 htD.1 hst hnonempty
  let C := commonFacesComplex (derivedNeighborhoodCell K s) (derivedNeighborhoodCell K t)
  let _ : Finite (derivedNeighborhoodCell K s).faces :=
    (derivedNeighborhoodCell_faces_finite K s).to_subtype
  let _ : Finite C.faces :=
    (commonFacesComplex_faces_finite (derivedNeighborhoodCell K s)
      (derivedNeighborhoodCell K t) (Set.toFinite (derivedNeighborhoodCell K s).faces)).to_subtype
  have hCspace : C.space =
      (derivedNeighborhoodCell K s).space ∩ (derivedNeighborhoodCell K t).space :=
    commonFacesComplex_space_eq_inter_of_faces_subset (secondDerived K)
      (derivedNeighborhoodCell K s) (derivedNeighborhoodCell K t)
      (derivedNeighborhoodCell_faces_subset K s) (derivedNeighborhoodCell_faces_subset K t)
  have hCball : IsPLBall 1 C.space := by
    rw [hCspace]
    exact hball
  have huC : u ∈ C.faces := ⟨hus, hut⟩
  obtain ⟨v, hvC, huv, hvcard⟩ := exists_face_superset_card_eq_of_isPLBall C hCball huC
  exact ⟨v, ⟨⟨s, hsP, hvC.1⟩, ⟨t, htD, hvC.2⟩⟩, huv, hvcard⟩

open Classical in
theorem IsCombinatorialManifold.isPLSphere_two_of_faceEulerChar_eq_two
    [FiniteDimensional ℝ E] (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold 2 K) (hconn : IsConnected K.space)
    (hEuler : SimplicialComplex.faceEulerChar K.toPreAbstractSimplicialComplex = 2) :
    IsPLSphere 2 K.space := by
  obtain ⟨T, hT, hTree, hDualTree⟩ := exists_primalTree_dualCotree K hK hconn hEuler
  let R := _root_.DifferentialGeometry.Topology.PiecewiseLinear.secondDerived K
  let A := primalTreeCellComplex K T
  let B := dualCotreeCellComplex K T
  let _ : Finite R.faces := by
    dsimp only [R]
    infer_instance
  let _ : Finite A.faces := (derivedNeighborhoodCellsComplex_faces_finite K
    (primalTreeCellFaces K T)).to_subtype
  let _ : Finite B.faces := (derivedNeighborhoodCellsComplex_faces_finite K
    (dualCotreeCellFaces K T)).to_subtype
  have hR : IsCombinatorialManifold 2 R := hK.secondDerived
  have hA : IsPLBall 2 A.space := isPLBall_primalTreeCellComplex K hK hT hTree
  have hB : IsPLBall 2 B.space := isPLBall_dualCotreeCellComplex K hK T hDualTree
  have hAR : A.faces ⊆ R.faces := primalTreeCellComplex_faces_subset_secondDerived K T
  have hBR : B.faces ⊆ R.faces := dualCotreeCellComplex_faces_subset_secondDerived K T
  have hcover : ∀ s ∈ R.faces, s ∈ A.faces ∨ s ∈ B.faces :=
    fun _ hs => mem_primalTreeCellComplex_or_mem_dualCotreeCellComplex K hK T hs
  have hpure : ∀ s, s ∈ A.faces → s ∈ B.faces →
      ∃ t ∈ A.faces ∩ B.faces, s ⊆ t ∧ t.card = 2 :=
    fun _ hsA hsB => primalTreeCellComplex_dualCotreeCellComplex_pure_inter K hK hT hsA hsB
  have hsphere : IsPLSphere 2 R.space :=
    isPLSphere_two_of_isPLBall_faces_cover R A B hR hA hB hAR hBR hcover hpure
  rwa [(secondDerived_isSubdivision K).space_eq] at hsphere

end DifferentialGeometry.Topology.PiecewiseLinear
