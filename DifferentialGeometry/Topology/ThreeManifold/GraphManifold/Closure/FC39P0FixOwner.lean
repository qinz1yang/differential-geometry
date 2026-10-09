import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Adapted
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0FixSeamRemoval
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.AssemblyRimQuadrantProducer

/-!
# FC39 producer, gate 1 (review 49, level-3 interface): owner agreement of every handle-end layer

External review 49 (F.8): `stub_exists_arcLayer` must first export that ANY usable handle-end layer
`HE` agrees with the actual horizontal labels (or take the owner equation explicitly). The
agreement FOLLOWS from the existing fields — no owner equation has to be taken:

`LabelledCornerCompatibility.handleEnd_index_eq`: for every `HE : HandleEndLayer W V H F` (any
seam / face layers) and every vertex link `vlink`, the vertex of the end `b` of the handle `h` is
the owner `residualOwner (horizontal (endOfHandle h b))` of the actual horizontal face.

Proof. The rim point `y = rimChart h b (1, (0, 0))` lies in the end disk (`rim_label`), hence in
the face `handleFace h b` (`handleEnd_face`), hence in the model boundary image of the vertex
`handleEnd h b` (`face_exhausted`, `handleFace_owner`); it lies in the raw tube `U_e`
(`target_in_raw_tube`), which is open. A boundary point of a piece in an open set gives an interior
point of the piece image in that set (`exists_mem_inter_interior_range`). On the tube, the three
labelled side equalities (`vertex_side`, `edge_side`, `region_side`) cover `U_e` by the closed row
set of the horizontal owner, the closed edge piece and the region; if the owner of `HE` were a
different row, its interior would meet none of their interiors (`interiors_disjoint`), so the open
set `U_e ∩ int(row)` would be empty (`eq_empty_of_subset_union_three_FIX2`) — contradiction.

Corollaries: `AdaptedEdgeRimData.handleEnd_index_eq` (the form the assembly stubs use) and
`LabelledCornerCompatibility.handleEnd_eq_of_handleEndLayers` (two handle-end layers have the same
end vertices).
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

/-- A saturated tube over an open set of the circle base is open. -/
theorem CircleBundle.isOpen_tube (R : CircleBundle W) {B : Set R.Base} (hB : IsOpen B) :
    IsOpen (R.tube B) :=
  R.domain.isOpen.isOpenMap_subtype_val _ (hB.preimage R.proj.continuous)

/-- The edge piece is closed (`EdgeBundle.proper` over the compact base `C₂`). -/
theorem EdgeBundle.isClosed_edgePiece (P : EdgeBundle W) : IsClosed P.edgePiece :=
  (P.proper P.cbase P.cbase_compact).isClosed

/-- The whole inverse image of a base component lies in the edge piece. -/
theorem EdgeBundle.wholeComponent_subset_edgePiece (P : EdgeBundle W) (C : P.EdgeBaseComponent) :
    P.wholeComponent C ⊆ P.edgePiece := by
  rintro _ ⟨x, ⟨hx, hx'⟩, rfl⟩
  exact ⟨x, ⟨ActualComponent.subset _ hx, hx'⟩, rfl⟩

/-- Every row set is closed. -/
theorem SlimPiecesV2.isClosed_rowSet {Z : ZeroDomains W} {C : CuspCores W E}
    (S : SlimPiecesV2 W Z C) (a : S.RowIndex) : IsClosed (S.rowSet a) := by
  rcases a with i | b | j
  · exact (Z.piece i).isClosed_range
  · exact (C.piece b).isClosed_range
  · exact (S.piece j).isClosed_range

/-- **Owner agreement (review 49, derived).** For every handle-end layer `HE` over any face layer
and every vertex link, the vertex of the end `b` of the handle `h` is the owner of the actual
horizontal face of that end. -/
theorem LabelledCornerCompatibility.handleEnd_index_eq {Pr : FC39Prepared W E} {H : EdgeLayer W}
    {circ : CircleRegion W} {K : RimChartLayer W H circ}
    (L : LabelledCornerCompatibility Pr H circ K) {V : VertexLayer W}
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

/-- **Owner agreement for the adapted data** (the form of the assembly stubs
`stub_handleEndLayer_of_labelled`, `stub_rimRegionLayer_of_labelled`, `stub_exists_arcLayer`). -/
theorem AdaptedEdgeRimData.handleEnd_index_eq {Pr : FC39Prepared W E}
    {safe : ProducerSafeNeighbourhoods Pr.rows} (A : AdaptedEdgeRimData Pr safe)
    {V : VertexLayer W} (vlink : VertexModelLink Pr.rows V) {circ' : CircleRegion W}
    {S : SeamLayer W V circ'} {O : PortLayer W E V} {F : FaceLayer W E V S O}
    (HE : HandleEndLayer W V A.edges F) (h : Fin A.edges.handleCount) (b : Bool) :
    vlink.index (HE.handleEnd h b) = A.labelled.handleEndOwner h b :=
  A.labelled.handleEnd_index_eq vlink HE h b

/-- **Consumer**: two handle-end layers (over any face layers) have the same end vertices. -/
theorem LabelledCornerCompatibility.handleEnd_eq_of_handleEndLayers {Pr : FC39Prepared W E}
    {H : EdgeLayer W} {circ : CircleRegion W} {K : RimChartLayer W H circ}
    (L : LabelledCornerCompatibility Pr H circ K) {V : VertexLayer W}
    (vlink : VertexModelLink Pr.rows V) {circ₁ circ₂ : CircleRegion W} {S₁ : SeamLayer W V circ₁}
    {S₂ : SeamLayer W V circ₂} {O₁ O₂ : PortLayer W E V} {F₁ : FaceLayer W E V S₁ O₁}
    {F₂ : FaceLayer W E V S₂ O₂} (HE₁ : HandleEndLayer W V H F₁) (HE₂ : HandleEndLayer W V H F₂)
    (h : Fin H.handleCount) (b : Bool) : HE₁.handleEnd h b = HE₂.handleEnd h b :=
  vlink.index.injective
    ((L.handleEnd_index_eq vlink HE₁ h b).trans (L.handleEnd_index_eq vlink HE₂ h b).symm)

end GC.GraphManifold.Assembly.FC39P0
