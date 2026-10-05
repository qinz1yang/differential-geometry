import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0HandleFaceResidual
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0AdaptedV2

/-!
# FC39 GROUP G over the prepared rows V2: owner agreement and the handle face (D58-1, G1b)

Lane FC39-G-GFF(b). The Pr-indexed consumer theorems of `FC39P0FixOwner.lean` (review 49, owner
agreement of every handle-end layer) and `FC39P0HandleFaceResidual.lean` (review 56, D56-3: the
handle face IS the residual face) restated for `LabelledCornerCompatibilityV2` /
`AdaptedEdgeRimDataV2` over `Pr : FC39PreparedV2 W E`. The proofs are the accepted ones: they read
only `Pr.rows`, the edge link and the rim charts (never `Pr.globalFaces`), so they go through
verbatim; the generic lemmas of those files (row-level, not Pr-indexed) are reused.

Same short names inside the V2 namespaces:

* `LabelledCornerCompatibilityV2.handleEnd_index_eq`, `AdaptedEdgeRimDataV2.handleEnd_index_eq`,
  `LabelledCornerCompatibilityV2.handleEnd_eq_of_handleEndLayers`;
* `LabelledCornerCompatibilityV2.endDisk_subset_residualSet`, `.face_handleFace_eq_residualSet`,
  `.eq_handleFace_of_meet`, `.existsUnique_face_residualSet`, `.faceEquiv_handleFace`, and the
  adapted forms `AdaptedEdgeRimDataV2.face_handleFace_eq_residualSet`,
  `.existsUnique_face_residualSet`, `.eq_handleFace_of_meet`;
* `LabelledCornerCompatibility.toV2_handleEnd_index_eq` — on the forgetful image of an old
  compatibility the V2 owner agreement is the old one (consumer of the forgetful map).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

variable {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}

/-! ## Owner agreement (review 49) over V2 -/

/-- **Owner agreement (review 49, derived), V2.** For every handle-end layer `HE` over any face
layer and every vertex link, the vertex of the end `b` of the handle `h` is the owner of the actual
horizontal face of that end. -/
theorem LabelledCornerCompatibilityV2.handleEnd_index_eq {Pr : FC39PreparedV2 W E}
    {H : EdgeLayer W} {circ : CircleRegion W} {K : RimChartLayer W H circ}
    (L : LabelledCornerCompatibilityV2 Pr H circ K) {V : VertexLayer W}
    (vlink : VertexModelLink Pr.rows V) {circ' : CircleRegion W} {S : SeamLayer W V circ'}
    {O : PortLayer W E V} {F : FaceLayer W E V S O} (HE : HandleEndLayer W V H F)
    (h : Fin H.handleCount) (b : Bool) :
    vlink.index (HE.handleEnd h b) = L.handleEndOwner h b := by
  classical
  set e := L.edgeLink.endOfHandle h b with he
  set T := Pr.rows.labelledTubes with hT
  set R := Pr.rows.circle with hR
  -- the rim point of the end disk, inside the raw tube
  have hp : ((1 : Circle), ((0 : ℝ), (0 : ℝ))) ∈ (K.rimChart h b).source :=
    (K.rim_source h b).2 (by simp [rimBox])
  have hyT : K.rimChart h b ((1 : Circle), ((0 : ℝ), (0 : ℝ))) ∈ T.tube e :=
    L.target_in_raw_tube h b ((K.rimChart h b).map_source hp)
  have hyD : K.rimChart h b ((1 : Circle), ((0 : ℝ), (0 : ℝ))) ∈ (H.handle h).endDisk b := by
    have hmem : K.rimChart h b ((1 : Circle), ((0 : ℝ), (0 : ℝ))) ∈
        K.rimChart h b '' {p | p.2 = (0, 0)} := ⟨_, rfl, rfl⟩
    rw [K.rim_label h b] at hmem
    obtain ⟨w, -, hw⟩ := hmem
    exact ⟨w, hw⟩
  have hyB : K.rimChart h b ((1 : Circle), ((0 : ℝ), (0 : ℝ))) ∈
      (V.vertex (HE.handleEnd h b)).boundaryImage := by
    rw [← F.face_exhausted]
    exact mem_iUnion₂.2 ⟨HE.handleFace h b, HE.handleFace_owner h b, HE.handleEnd_face h b hyD⟩
  obtain ⟨m, -, hm⟩ := hyB
  -- an interior point of the owner piece inside the tube
  have hTopen : IsOpen (T.tube e) := R.isOpen_tube (T.base e).isOpen
  obtain ⟨z, hzT, hzI⟩ := exists_mem_inter_interior_range (finrank_euclideanSpace_fin)
    (V.vertex (HE.handleEnd h b)).piece.smooth (V.vertex (HE.handleEnd h b)).piece.mfderiv_bijective
    hTopen (x := m) (by rw [hm]; exact hyT)
  have hzI' : z ∈ interior (Pr.rows.slim.rowSet (vlink.index (HE.handleEnd h b))) := by
    rw [← vlink.image_eq_rowSet, Vertex.image_eq_range_piece]
    exact hzI
  by_contra hne
  have hne' : (Sum.inl (vlink.index (HE.handleEnd h b)) : Pr.rows.slim.RowIndex ⊕ Bool) ≠
      Sum.inl (L.handleEndOwner h b) := fun h' => hne (Sum.inl_injective h')
  -- the tube is covered by the horizontal owner, the edge piece and the region
  have hcover : T.tube e ∩ interior (Pr.rows.slim.rowSet (vlink.index (HE.handleEnd h b))) ⊆
      Pr.rows.slim.rowSet (L.handleEndOwner h b) ∪ Pr.rows.edge.edgePiece ∪ R.region := by
    rintro _ ⟨⟨x, hxB, rfl⟩, -⟩
    by_cases hY : (T.chart e (R.proj x)).2 ≤ 0
    · exact Or.inl (Or.inl ((T.vertex_side (e := e) (x := x) hxB).2 hY))
    · by_cases hX : (T.chart e (R.proj x)).1 ≤ 0
      · exact Or.inl (Or.inr (Pr.rows.edge.wholeComponent_subset_edgePiece _
          ((T.edge_side (e := e) (x := x) hxB).2 ⟨(not_le.1 hY).le, hX⟩)))
      · exact Or.inr ((T.region_side (e := e) (x := x) hxB).2
          ⟨(not_le.1 hX).le, (not_le.1 hY).le⟩)
  have hU := eq_empty_of_subset_union_three_FIX2 (hTopen.inter isOpen_interior)
    (Pr.rows.slim.isClosed_rowSet _) Pr.rows.edge.isClosed_edgePiece hcover
    ((Pr.rows.junctions.interiors_disjoint hne').mono_left inter_subset_right)
    ((Pr.rows.junctions.interiors_disjoint
      (show (Sum.inl (vlink.index (HE.handleEnd h b)) : Pr.rows.slim.RowIndex ⊕ Bool) ≠
        Sum.inr true by simp)).mono_left inter_subset_right)
    ((Pr.rows.junctions.interiors_disjoint
      (show (Sum.inl (vlink.index (HE.handleEnd h b)) : Pr.rows.slim.RowIndex ⊕ Bool) ≠
        Sum.inr false by simp)).mono_left inter_subset_right)
  have hmem : z ∈ T.tube e ∩ interior (Pr.rows.slim.rowSet (vlink.index (HE.handleEnd h b))) :=
    ⟨hzT, hzI'⟩
  rw [hU] at hmem
  exact hmem

/-- **Owner agreement for the adapted data V2** (the form of the assembly targets over V2). -/
theorem AdaptedEdgeRimDataV2.handleEnd_index_eq {Pr : FC39PreparedV2 W E}
    {safe : ProducerSafeNeighbourhoods Pr.rows} (A : AdaptedEdgeRimDataV2 Pr safe)
    {V : VertexLayer W} (vlink : VertexModelLink Pr.rows V) {circ' : CircleRegion W}
    {S : SeamLayer W V circ'} {O : PortLayer W E V} {F : FaceLayer W E V S O}
    (HE : HandleEndLayer W V A.edges F) (h : Fin A.edges.handleCount) (b : Bool) :
    vlink.index (HE.handleEnd h b) = A.labelled.handleEndOwner h b :=
  A.labelled.handleEnd_index_eq vlink HE h b

/-- Two handle-end layers (over any face layers) have the same end vertices (V2). -/
theorem LabelledCornerCompatibilityV2.handleEnd_eq_of_handleEndLayers {Pr : FC39PreparedV2 W E}
    {H : EdgeLayer W} {circ : CircleRegion W} {K : RimChartLayer W H circ}
    (L : LabelledCornerCompatibilityV2 Pr H circ K) {V : VertexLayer W}
    (vlink : VertexModelLink Pr.rows V) {circ₁ circ₂ : CircleRegion W} {S₁ : SeamLayer W V circ₁}
    {S₂ : SeamLayer W V circ₂} {O₁ O₂ : PortLayer W E V} {F₁ : FaceLayer W E V S₁ O₁}
    {F₂ : FaceLayer W E V S₂ O₂} (HE₁ : HandleEndLayer W V H F₁) (HE₂ : HandleEndLayer W V H F₂)
    (h : Fin H.handleCount) (b : Bool) : HE₁.handleEnd h b = HE₂.handleEnd h b :=
  vlink.index.injective
    ((L.handleEnd_index_eq vlink HE₁ h b).trans (L.handleEnd_index_eq vlink HE₂ h b).symm)

/-- On the forgetful image of an old compatibility, the V2 owner agreement is the old one (both are
equations in the same type; consumer of `LabelledCornerCompatibility.toV2`). -/
theorem LabelledCornerCompatibility.toV2_handleEnd_index_eq {Pr : FC39Prepared W E}
    {H : EdgeLayer W} {circ : CircleRegion W} {K : RimChartLayer W H circ}
    (L : LabelledCornerCompatibility Pr H circ K) {V : VertexLayer W}
    (vlink : VertexModelLink Pr.rows V) {circ' : CircleRegion W} {S : SeamLayer W V circ'}
    {O : PortLayer W E V} {F : FaceLayer W E V S O} (HE : HandleEndLayer W V H F)
    (h : Fin H.handleCount) (b : Bool) :
    vlink.index (HE.handleEnd h b) = L.toV2.handleEndOwner h b ∧
      L.toV2.handleEndOwner h b = L.handleEndOwner h b :=
  ⟨L.toV2.handleEnd_index_eq vlink HE h b, L.toV2_handleEndOwner h b⟩

/-! ## The handle face of every handle-end layer (review 56, D56-3) over V2 -/

section Labelled

variable {Pr : FC39PreparedV2 W E} {H : EdgeLayer W} {circ : CircleRegion W}
  {K : RimChartLayer W H circ}

/-- The end disk of `(h, b)` lies in the actual residual face of its horizontal label (V2). -/
theorem LabelledCornerCompatibilityV2.endDisk_subset_residualSet
    (L : LabelledCornerCompatibilityV2 Pr H circ K) (h : Fin H.handleCount) (b : Bool) :
    (H.handle h).endDisk b ⊆
      Pr.rows.slim.residualSet (Pr.rows.junctions.horizontal (L.edgeLink.endOfHandle h b)) := by
  rw [L.edgeLink.endDisk_eq]
  exact Pr.rows.junctions.horizontal_disk _

variable {V : VertexLayer W} {circ' : CircleRegion W} {S : SeamLayer W V circ'}
  {O : PortLayer W E V} {F : FaceLayer W E V S O}
  {N : Pr.rows.SharedFace → TopologicalSpace.Opens W.Carrier}

/-- **D56-3 over V2: the face of `HE` at `(h, b)` IS the actual residual face** of the horizontal
label of that end. -/
theorem LabelledCornerCompatibilityV2.face_handleFace_eq_residualSet
    (L : LabelledCornerCompatibilityV2 Pr H circ K) (vlink : VertexModelLink Pr.rows V)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (HE : HandleEndLayer W V H F)
    (h : Fin H.handleCount) (b : Bool) :
    F.face (HE.handleFace h b) =
      Pr.rows.slim.residualSet (Pr.rows.junctions.horizontal (L.edgeLink.endOfHandle h b)) := by
  obtain ⟨m₁, hm₁⟩ := sf.exists_face_eq_image (HE.handleFace h b)
  obtain ⟨m₂, hm₂⟩ :=
    Pr.rows.exists_residualSet_eq_image (Pr.rows.junctions.horizontal (L.edgeLink.endOfHandle h b))
  have hP : (V.vertex (F.faceOwner (HE.handleFace h b))).piece =
      Pr.rows.rowPiece (Pr.rows.slim.residualOwner
        (Pr.rows.junctions.horizontal (L.edgeLink.endOfHandle h b))) := by
    rw [HE.handleFace_owner, vlink.vertex_piece, L.handleEnd_index_eq vlink HE h b]
    rfl
  obtain ⟨x, hx⟩ : ((H.handle h).endDisk b).Nonempty := ⟨_, ⟨⟨0, by simp⟩, rfl⟩⟩
  rw [hm₁, hm₂]
  refine ModelBoundaryFace.image_eq_of_meet hP ⟨x, ?_, ?_⟩
  · rw [← hm₁]
    exact HE.handleEnd_face h b hx
  · rw [← hm₂]
    exact L.endDisk_subset_residualSet h b hx

/-- **D56-3 over V2: `HE.handleFace h b` is THE catalogue index of the residual face.** -/
theorem LabelledCornerCompatibilityV2.eq_handleFace_of_meet
    (L : LabelledCornerCompatibilityV2 Pr H circ K) (vlink : VertexModelLink Pr.rows V)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (HE : HandleEndLayer W V H F)
    (h : Fin H.handleCount) (b : Bool) {f : Fin F.faceCount}
    (hown : vlink.index (F.faceOwner f) = L.handleEndOwner h b)
    (hmeet : (F.face f ∩ Pr.rows.slim.residualSet
      (Pr.rows.junctions.horizontal (L.edgeLink.endOfHandle h b))).Nonempty) :
    f = HE.handleFace h b := by
  refine sf.eq_of_faceOwner_eq_of_meet ?_ ?_
  · rw [HE.handleFace_owner]
    exact vlink.index.injective (hown.trans (L.handleEnd_index_eq vlink HE h b).symm)
  · rw [L.face_handleFace_eq_residualSet vlink sf HE h b]
    exact hmeet

/-- **The catalogue index of the residual face, unique (V2).** -/
theorem LabelledCornerCompatibilityV2.existsUnique_face_residualSet
    (L : LabelledCornerCompatibilityV2 Pr H circ K) (vlink : VertexModelLink Pr.rows V)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (HE : HandleEndLayer W V H F)
    (h : Fin H.handleCount) (b : Bool) :
    ∃! f : Fin F.faceCount, vlink.index (F.faceOwner f) = L.handleEndOwner h b ∧
      F.face f = Pr.rows.slim.residualSet
        (Pr.rows.junctions.horizontal (L.edgeLink.endOfHandle h b)) := by
  refine ⟨HE.handleFace h b, ⟨?_, L.face_handleFace_eq_residualSet vlink sf HE h b⟩, ?_⟩
  · rw [HE.handleFace_owner]
    exact L.handleEnd_index_eq vlink HE h b
  · rintro f ⟨hown, hface⟩
    refine L.eq_handleFace_of_meet vlink sf HE h b hown ?_
    rw [hface, inter_self]
    obtain ⟨x, hx⟩ : ((H.handle h).endDisk b).Nonempty := ⟨_, ⟨⟨0, by simp⟩, rfl⟩⟩
    exact ⟨x, L.endDisk_subset_residualSet h b hx⟩

/-- **The catalogue entry of the handle face (V2).** -/
theorem LabelledCornerCompatibilityV2.faceEquiv_handleFace
    (L : LabelledCornerCompatibilityV2 Pr H circ K) (vlink : VertexModelLink Pr.rows V)
    (sf : SeamFacesLink Pr.rows V vlink O S F N) (HE : HandleEndLayer W V H F)
    (h : Fin H.handleCount) (b : Bool) :
    (sf.faceEquiv (HE.handleFace h b)).1 = HE.handleEnd h b ∧
      vlink.index (sf.faceEquiv (HE.handleFace h b)).1 = L.handleEndOwner h b ∧
      (V.vertex (sf.faceEquiv (HE.handleFace h b)).1).piece.map ''
          (sf.faceEquiv (HE.handleFace h b)).2.1 =
        Pr.rows.slim.residualSet (Pr.rows.junctions.horizontal (L.edgeLink.endOfHandle h b)) := by
  have h1 : (sf.faceEquiv (HE.handleFace h b)).1 = HE.handleEnd h b :=
    (sf.faceEquiv_owner _).trans (HE.handleFace_owner h b)
  refine ⟨h1, ?_, ?_⟩
  · rw [h1]
    exact L.handleEnd_index_eq vlink HE h b
  · rw [← sf.face_image]
    exact L.face_handleFace_eq_residualSet vlink sf HE h b

end Labelled

/-! ## The forms on the adapted data V2 (GROUP G arc lane) -/

section Adapted

variable {Pr : FC39PreparedV2 W E} {safe : ProducerSafeNeighbourhoods Pr.rows}
  {V : VertexLayer W} {circ' : CircleRegion W} {S : SeamLayer W V circ'}
  {O : PortLayer W E V} {F : FaceLayer W E V S O}
  {N : Pr.rows.SharedFace → TopologicalSpace.Opens W.Carrier}

/-- The handle face of `HE` is the residual face (adapted form, V2). -/
theorem AdaptedEdgeRimDataV2.face_handleFace_eq_residualSet (A : AdaptedEdgeRimDataV2 Pr safe)
    (vlink : VertexModelLink Pr.rows V) (sf : SeamFacesLink Pr.rows V vlink O S F N)
    (HE : HandleEndLayer W V A.edges F) (h : Fin A.edges.handleCount) (b : Bool) :
    F.face (HE.handleFace h b) = Pr.rows.slim.residualSet
      (Pr.rows.junctions.horizontal (A.labelled.edgeLink.endOfHandle h b)) :=
  A.labelled.face_handleFace_eq_residualSet vlink sf HE h b

/-- `HE.handleFace h b` is the unique catalogue index of the residual face (adapted form, V2). -/
theorem AdaptedEdgeRimDataV2.existsUnique_face_residualSet (A : AdaptedEdgeRimDataV2 Pr safe)
    (vlink : VertexModelLink Pr.rows V) (sf : SeamFacesLink Pr.rows V vlink O S F N)
    (HE : HandleEndLayer W V A.edges F) (h : Fin A.edges.handleCount) (b : Bool) :
    ∃! f : Fin F.faceCount, vlink.index (F.faceOwner f) = A.labelled.handleEndOwner h b ∧
      F.face f = Pr.rows.slim.residualSet
        (Pr.rows.junctions.horizontal (A.labelled.edgeLink.endOfHandle h b)) :=
  A.labelled.existsUnique_face_residualSet vlink sf HE h b

/-- A face index with the actual horizontal owner meeting the residual face is the handle face
(adapted form, V2). -/
theorem AdaptedEdgeRimDataV2.eq_handleFace_of_meet (A : AdaptedEdgeRimDataV2 Pr safe)
    (vlink : VertexModelLink Pr.rows V) (sf : SeamFacesLink Pr.rows V vlink O S F N)
    (HE : HandleEndLayer W V A.edges F) (h : Fin A.edges.handleCount) (b : Bool)
    {f : Fin F.faceCount} (hown : vlink.index (F.faceOwner f) = A.labelled.handleEndOwner h b)
    (hmeet : (F.face f ∩ Pr.rows.slim.residualSet
      (Pr.rows.junctions.horizontal (A.labelled.edgeLink.endOfHandle h b))).Nonempty) :
    f = HE.handleFace h b :=
  A.labelled.eq_handleFace_of_meet vlink sf HE h b hown hmeet

end Adapted

end GC.GraphManifold.Assembly.FC39P0
