import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0FixOwner

/-!
# FC39 producer, GROUP G interface (review 56, D56-3): the handle face IS the residual face

External review 56 (§3.2, disposition D56-3) asks, besides the owner identification of every
handle-end layer (already DERIVED: `LabelledCornerCompatibility.handleEnd_index_eq`,
`FC39P0FixOwner.lean`), that the face `HE.handleFace h b` be identified as the catalogue index of the
ACTUAL residual face of the end `(h, b)` — the horizontal label
`Pr.rows.junctions.horizontal (endOfHandle h b)` — from the face catalogue `sf.faceEquiv`, the
face-image identification `sf.face_image` and the non-empty end disk; not merely "some face of the
right owner". Here, for every labelled corner compatibility `L` (in particular `A.labelled` of the
adapted data), every vertex link, every seam–face link `sf` and every handle-end layer `HE`:

* `LabelledCornerCompatibility.endDisk_subset_residualSet` — the end disk lies in the residual face
  (`EdgeComponentsLink.endDisk_eq`: the end disk is the whole disk over the registered endpoint;
  `JunctionsV2.horizontal_disk`);
* `LabelledCornerCompatibility.face_handleFace_eq_residualSet` — **the face of `HE` at `(h, b)` is the
  residual face**: both are images of model boundary components of the same piece (the catalogue
  component `(sf.faceEquiv f).2` of the owner, `FC39RowsV2.exists_residualSet_eq_image` for the
  residual face; the pieces agree by `vertex_piece` and the owner identification), and two
  components whose images meet are equal (`ModelBoundaryFace.eq_of_image_meet`); they meet in the
  non-empty end disk;
* `LabelledCornerCompatibility.eq_handleFace_of_meet` and `existsUnique_face_residualSet` — **the
  catalogue index**: a face index whose owner is the actual horizontal owner and whose face meets the
  residual face IS `HE.handleFace h b` (the catalogue is injective on owners and meeting faces,
  `SeamFacesLink.eq_of_faceOwner_eq_of_meet`); `faceEquiv_handleFace` reads the catalogue entry;
* the forms on the adapted data `AdaptedEdgeRimData.*` used by the GROUP G arc lane.
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

/-! ## Model boundary faces of one piece -/

/-- Two model boundary faces of one embedded piece whose images meet are equal. -/
theorem ModelBoundaryFace.eq_of_image_meet {P : PieceEmbedding W} {m m' : ModelBoundaryFace P}
    (h : (P.map '' m.1 ∩ P.map '' m'.1).Nonempty) : m = m' := by
  obtain ⟨_, ⟨q, hq, rfl⟩, ⟨q', hq', hqq⟩⟩ := h
  obtain rfl : q' = q := P.injective hqq
  exact ActualComponent.eq_of_mem hq hq'

/-- Images of model boundary faces of two equal pieces that meet are equal. -/
theorem ModelBoundaryFace.image_eq_of_meet {P P' : PieceEmbedding W} (hP : P = P')
    {m : ModelBoundaryFace P} {m' : ModelBoundaryFace P'}
    (h : (P.map '' m.1 ∩ P'.map '' m'.1).Nonempty) : P.map '' m.1 = P'.map '' m'.1 := by
  subst hP
  rw [ModelBoundaryFace.eq_of_image_meet h]

/-- **The residual face is the image of a model boundary face of its owner's row piece**: a zero /
cusp-internal model face, or the model face of a new slim end. -/
theorem FC39RowsV2.exists_residualSet_eq_image (Rw : FC39RowsV2 W E)
    (F : Rw.slim.ResidualFace) :
    ∃ m : ModelBoundaryFace (Rw.rowPiece (Rw.slim.residualOwner F)),
      Rw.slim.residualSet F = (Rw.rowPiece (Rw.slim.residualOwner F)).map '' m.1 := by
  rcases F with ⟨⟨i, m⟩ | ⟨b, m, hm⟩, hF⟩ | e
  · exact ⟨m, rfl⟩
  · exact ⟨m, rfl⟩
  · refine ⟨Rw.slim.endFace e.1, ?_⟩
    change Rw.slim.endSet e.1 = (Rw.slim.piece e.1.1.1).map '' (Rw.slim.endFace e.1).1
    rw [Rw.slim.endFace_eq]
    rfl

/-! ## The face catalogue of a seam–face link -/

section Catalogue

variable {Rw : FC39RowsV2 W E} {V : VertexLayer W} {VL : VertexModelLink Rw V}
  {O : PortLayer W E V} {circ : CircleRegion W} {S : SeamLayer W V circ}
  {F : FaceLayer W E V S O} {N : Rw.SharedFace → TopologicalSpace.Opens W.Carrier}

/-- Every face of the catalogue is the image of a model boundary face of its owner's piece. -/
theorem SeamFacesLink.exists_face_eq_image (sf : SeamFacesLink Rw V VL O S F N)
    (f : Fin F.faceCount) :
    ∃ m : ModelBoundaryFace (V.vertex (F.faceOwner f)).piece,
      F.face f = (V.vertex (F.faceOwner f)).piece.map '' m.1 := by
  have h := sf.face_image f
  have ho := sf.faceEquiv_owner f
  generalize sf.faceEquiv f = s at h ho
  obtain ⟨v, m⟩ := s
  dsimp only at h ho
  subst ho
  exact ⟨m, h⟩

/-- **The catalogue is injective on owners and meeting faces**: two face indices with the same
owner whose faces meet are equal. -/
theorem SeamFacesLink.eq_of_faceOwner_eq_of_meet (sf : SeamFacesLink Rw V VL O S F N)
    {f f' : Fin F.faceCount} (hown : F.faceOwner f = F.faceOwner f')
    (hmeet : (F.face f ∩ F.face f').Nonempty) : f = f' := by
  apply sf.faceEquiv.injective
  rw [sf.face_image f, sf.face_image f'] at hmeet
  have hv : (sf.faceEquiv f).1 = (sf.faceEquiv f').1 :=
    (sf.faceEquiv_owner f).trans (hown.trans (sf.faceEquiv_owner f').symm)
  generalize sf.faceEquiv f = s at hmeet hv ⊢
  generalize sf.faceEquiv f' = s' at hmeet hv ⊢
  obtain ⟨v, m⟩ := s
  obtain ⟨v', m'⟩ := s'
  dsimp only at hv hmeet
  subst hv
  rw [ModelBoundaryFace.eq_of_image_meet hmeet]

end Catalogue

/-! ## The handle face of every handle-end layer -/

section Labelled

variable {Pr : FC39Prepared W E} {H : EdgeLayer W} {circ : CircleRegion W}
  {K : RimChartLayer W H circ}

/-- The end disk of `(h, b)` lies in the actual residual face of its horizontal label. -/
theorem LabelledCornerCompatibility.endDisk_subset_residualSet
    (L : LabelledCornerCompatibility Pr H circ K) (h : Fin H.handleCount) (b : Bool) :
    (H.handle h).endDisk b ⊆
      Pr.rows.slim.residualSet (Pr.rows.junctions.horizontal (L.edgeLink.endOfHandle h b)) := by
  rw [L.edgeLink.endDisk_eq]
  exact Pr.rows.junctions.horizontal_disk _

variable {V : VertexLayer W} {circ' : CircleRegion W} {S : SeamLayer W V circ'}
  {O : PortLayer W E V} {F : FaceLayer W E V S O}
  {N : Pr.rows.SharedFace → TopologicalSpace.Opens W.Carrier}

/-- **D56-3: the face of `HE` at `(h, b)` IS the actual residual face** of the horizontal label of
that end (catalogue component + face image + non-empty end disk). -/
theorem LabelledCornerCompatibility.face_handleFace_eq_residualSet
    (L : LabelledCornerCompatibility Pr H circ K) (vlink : VertexModelLink Pr.rows V)
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

/-- **D56-3: `HE.handleFace h b` is THE catalogue index of the residual face**: a face index whose
owner is the actual horizontal owner and whose face meets the residual face is `HE.handleFace h b`
(no other face of that vertex can be chosen). -/
theorem LabelledCornerCompatibility.eq_handleFace_of_meet
    (L : LabelledCornerCompatibility Pr H circ K) (vlink : VertexModelLink Pr.rows V)
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

/-- **The catalogue index of the residual face, unique**: exactly one face index has the actual
horizontal owner and the residual face as its face, and it is `HE.handleFace h b`. -/
theorem LabelledCornerCompatibility.existsUnique_face_residualSet
    (L : LabelledCornerCompatibility Pr H circ K) (vlink : VertexModelLink Pr.rows V)
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

/-- **The catalogue entry of the handle face**: the owner vertex of the end, whose row index is the
actual horizontal owner, with a model boundary face whose image is the residual face. -/
theorem LabelledCornerCompatibility.faceEquiv_handleFace
    (L : LabelledCornerCompatibility Pr H circ K) (vlink : VertexModelLink Pr.rows V)
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

/-! ## The forms on the adapted data (GROUP G arc lane) -/

section Adapted

variable {Pr : FC39Prepared W E} {safe : ProducerSafeNeighbourhoods Pr.rows}
  {V : VertexLayer W} {circ' : CircleRegion W} {S : SeamLayer W V circ'}
  {O : PortLayer W E V} {F : FaceLayer W E V S O}
  {N : Pr.rows.SharedFace → TopologicalSpace.Opens W.Carrier}

/-- The handle face of `HE` is the residual face (adapted form). -/
theorem AdaptedEdgeRimData.face_handleFace_eq_residualSet (A : AdaptedEdgeRimData Pr safe)
    (vlink : VertexModelLink Pr.rows V) (sf : SeamFacesLink Pr.rows V vlink O S F N)
    (HE : HandleEndLayer W V A.edges F) (h : Fin A.edges.handleCount) (b : Bool) :
    F.face (HE.handleFace h b) = Pr.rows.slim.residualSet
      (Pr.rows.junctions.horizontal (A.labelled.edgeLink.endOfHandle h b)) :=
  A.labelled.face_handleFace_eq_residualSet vlink sf HE h b

/-- `HE.handleFace h b` is the unique catalogue index of the residual face (adapted form). -/
theorem AdaptedEdgeRimData.existsUnique_face_residualSet (A : AdaptedEdgeRimData Pr safe)
    (vlink : VertexModelLink Pr.rows V) (sf : SeamFacesLink Pr.rows V vlink O S F N)
    (HE : HandleEndLayer W V A.edges F) (h : Fin A.edges.handleCount) (b : Bool) :
    ∃! f : Fin F.faceCount, vlink.index (F.faceOwner f) = A.labelled.handleEndOwner h b ∧
      F.face f = Pr.rows.slim.residualSet
        (Pr.rows.junctions.horizontal (A.labelled.edgeLink.endOfHandle h b)) :=
  A.labelled.existsUnique_face_residualSet vlink sf HE h b

/-- A face index with the actual horizontal owner meeting the residual face is the handle face
(adapted form). -/
theorem AdaptedEdgeRimData.eq_handleFace_of_meet (A : AdaptedEdgeRimData Pr safe)
    (vlink : VertexModelLink Pr.rows V) (sf : SeamFacesLink Pr.rows V vlink O S F N)
    (HE : HandleEndLayer W V A.edges F) (h : Fin A.edges.handleCount) (b : Bool)
    {f : Fin F.faceCount} (hown : vlink.index (F.faceOwner f) = A.labelled.handleEndOwner h b)
    (hmeet : (F.face f ∩ Pr.rows.slim.residualSet
      (Pr.rows.junctions.horizontal (A.labelled.edgeLink.endOfHandle h b))).Nonempty) :
    f = HE.handleFace h b :=
  A.labelled.eq_handleFace_of_meet vlink sf HE h b hown hmeet

end Adapted

end GC.GraphManifold.Assembly.FC39P0
