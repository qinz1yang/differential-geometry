import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GHandleEndRim
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0FixOwnerV2

/-!
# FC39 GROUP G over the prepared rows V2: handle ends and the rim region (D58-1, G1b)

Lane FC39-G-GFF(b). The Pr-indexed theorems of `FC39GHandleEndRim.lean` (lane FC39-G-HE-RIM,
frozen targets `T:329–336`, `T:339–346`) restated for `AdaptedEdgeRimDataV2` over
`Pr : FC39PreparedV2 W E` — the V2 forms of `stub_handleEndLayer_of_labelled` and
`stub_rimRegionLayer_of_labelled` (scratch `build-logs/scratch/FC39-G-GFF/TargetsV2.lean`). The
proofs are the accepted ones (they read `Pr.rows`, the labelled links and the rim charts, never
`Pr.globalFaces`); the row-level lemmas of that file (`exists_face_eq_residualSet_GHR`,
`faceKind_eq_partitioned_GHR`, `rimPoint_mem_*_GHR`, `component_endOfHandle_GHR`) are reused.

* dotted, same short names: `AdaptedEdgeRimDataV2.exists_handleFace_GHR`, `.handleEndLayer_GHR`
  (+ `_handleEnd`, `_index`, `_face`), `LabelledCornerCompatibilityV2.exists_tube_point_GHR`;
* top level: `handleEndLayer_of_labelled_GGFF`, `rimRegionLayer_of_labelled_GGFF`,
  `exists_handleEndLayer_rimRegionLayer_GGFF`;
* `AdaptedEdgeRimData.toV2_handleEndLayer_GHR` — on the forgetful image of an old adapted package the
  V2 handle-end layer IS the old one (definitional).
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

/-! ## The handle-end layer of the adapted data V2 -/

section HandleEnd

variable {Pr : FC39PreparedV2 W E} {safe : ProducerSafeNeighbourhoods Pr.rows}
  {V : VertexLayer W} {O : PortLayer W E V} {circ' : CircleRegion W} {S : SeamLayer W V circ'}
  {F : FaceLayer W E V S O}

/-- The end face of `(h, b)` (V2): a face of the vertex of the actual horizontal owner which IS the
residual face of the horizontal label and is partitioned. -/
theorem AdaptedEdgeRimDataV2.exists_handleFace_GHR (A : AdaptedEdgeRimDataV2 Pr safe)
    (vlink : VertexModelLink Pr.rows V) (sf : SeamFacesLink Pr.rows V vlink O S F safe.shared)
    (h : Fin A.edges.handleCount) (b : Bool) :
    ∃ f : Fin F.faceCount, F.faceOwner f = vlink.index.symm (A.labelled.handleEndOwner h b) ∧
      F.face f = Pr.rows.slim.residualSet
        (Pr.rows.junctions.horizontal (A.labelled.edgeLink.endOfHandle h b)) ∧
      F.faceKind f = .partitioned := by
  have hy := A.labelled.endDisk_subset_residualSet h b (A.rims.rimPoint_mem_endDisk_GHR h b)
  obtain ⟨f, hfo, hff⟩ := sf.exists_face_eq_residualSet_GHR
    (vlink.index.apply_symm_apply (A.labelled.handleEndOwner h b)) ⟨_, hy⟩
  refine ⟨f, hfo, hff, sf.faceKind_eq_partitioned_GHR (e := A.labelled.edgeLink.endOfHandle h b)
    ⟨_, hff ▸ hy, A.rim_in_safe h b (A.rims.rimPoint_mem_target_GHR h b)⟩⟩

/-- **The handle-end layer of the labelled compatibility V2.** -/
def AdaptedEdgeRimDataV2.handleEndLayer_GHR (A : AdaptedEdgeRimDataV2 Pr safe)
    (vlink : VertexModelLink Pr.rows V) (sf : SeamFacesLink Pr.rows V vlink O S F safe.shared) :
    HandleEndLayer W V A.edges F where
  handleEnd h b := vlink.index.symm (A.labelled.handleEndOwner h b)
  handleFace h b := (A.exists_handleFace_GHR vlink sf h b).choose
  handleFace_owner h b := (A.exists_handleFace_GHR vlink sf h b).choose_spec.1
  handleFace_kind h b := (A.exists_handleFace_GHR vlink sf h b).choose_spec.2.2
  handleEnd_face h b := by
    rw [(A.exists_handleFace_GHR vlink sf h b).choose_spec.2.1]
    exact A.labelled.endDisk_subset_residualSet h b
  endDisk_disjoint _ _ _ _ hne := A.labelled.edgeLink.endDisks_disjoint_of_components hne

theorem AdaptedEdgeRimDataV2.handleEndLayer_GHR_handleEnd (A : AdaptedEdgeRimDataV2 Pr safe)
    (vlink : VertexModelLink Pr.rows V) (sf : SeamFacesLink Pr.rows V vlink O S F safe.shared)
    (h : Fin A.edges.handleCount) (b : Bool) :
    (A.handleEndLayer_GHR vlink sf).handleEnd h b =
      vlink.index.symm (A.labelled.handleEndOwner h b) :=
  rfl

/-- **The owner equation (output), V2.** -/
theorem AdaptedEdgeRimDataV2.handleEndLayer_GHR_index (A : AdaptedEdgeRimDataV2 Pr safe)
    (vlink : VertexModelLink Pr.rows V) (sf : SeamFacesLink Pr.rows V vlink O S F safe.shared)
    (h : Fin A.edges.handleCount) (b : Bool) :
    vlink.index ((A.handleEndLayer_GHR vlink sf).handleEnd h b) = A.labelled.handleEndOwner h b :=
  vlink.index.apply_symm_apply _

/-- The end face of the constructed layer is the actual residual face of the horizontal label (V2). -/
theorem AdaptedEdgeRimDataV2.handleEndLayer_GHR_face (A : AdaptedEdgeRimDataV2 Pr safe)
    (vlink : VertexModelLink Pr.rows V) (sf : SeamFacesLink Pr.rows V vlink O S F safe.shared)
    (h : Fin A.edges.handleCount) (b : Bool) :
    F.face ((A.handleEndLayer_GHR vlink sf).handleFace h b) = Pr.rows.slim.residualSet
      (Pr.rows.junctions.horizontal (A.labelled.edgeLink.endOfHandle h b)) :=
  (A.exists_handleFace_GHR vlink sf h b).choose_spec.2.1

end HandleEnd

/-- On the forgetful image of an old adapted package, the V2 handle-end layer IS the old one. -/
theorem AdaptedEdgeRimData.toV2_handleEndLayer_GHR {Pr : FC39Prepared W E}
    {safe : ProducerSafeNeighbourhoods Pr.rows} (A : AdaptedEdgeRimData Pr safe)
    {V : VertexLayer W} {O : PortLayer W E V} {circ' : CircleRegion W} {S : SeamLayer W V circ'}
    {F : FaceLayer W E V S O} (vlink : VertexModelLink Pr.rows V)
    (sf : SeamFacesLink Pr.rows V vlink O S F safe.shared) :
    A.toV2.handleEndLayer_GHR vlink sf = A.handleEndLayer_GHR vlink sf :=
  rfl

/-- **GROUP G, `stub_handleEndLayer_of_labelled` over V2** (frozen `T:329–336`, D58-1 edit). -/
theorem handleEndLayer_of_labelled_GGFF (Pr : FC39PreparedV2 W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) (A : AdaptedEdgeRimDataV2 Pr safe)
    (V : VertexLayer W) (vlink : VertexModelLink Pr.rows V)
    (O : PortLayer W E V) (S : SeamLayer W V A.circ) (F : FaceLayer W E V S O)
    (sf : SeamFacesLink Pr.rows V vlink O S F safe.shared) :
    ∃ HE : HandleEndLayer W V A.edges F,
      ∀ h b, vlink.index (HE.handleEnd h b) = A.labelled.handleEndOwner h b :=
  ⟨A.handleEndLayer_GHR vlink sf, A.handleEndLayer_GHR_index vlink sf⟩

/-! ## The rim region over V2 -/

section Rim

variable {Pr : FC39PreparedV2 W E} {H : EdgeLayer W} {circ : CircleRegion W}
  {K : RimChartLayer W H circ}

/-- **A rim chart point in the raw labelled tube (V2)**, where the tube chart is `(λ x, λ y)`. -/
theorem LabelledCornerCompatibilityV2.exists_tube_point_GHR
    (L : LabelledCornerCompatibilityV2 Pr H circ K) (h : Fin H.handleCount) (b : Bool)
    {p : Circle × (ℝ × ℝ)} (hp : p ∈ (K.rimChart h b).source) :
    ∃ x : Pr.rows.circle.domain, (x : W.Carrier) = K.rimChart h b p ∧
      Pr.rows.circle.proj x ∈ Pr.rows.labelledTubes.base (L.edgeLink.endOfHandle h b) ∧
      (Pr.rows.labelledTubes.chart (L.edgeLink.endOfHandle h b) (Pr.rows.circle.proj x)).1 =
        circ.cornerScale (K.handleCorner h b) * p.2.1 ∧
      (Pr.rows.labelledTubes.chart (L.edgeLink.endOfHandle h b) (Pr.rows.circle.proj x)).2 =
        circ.cornerScale (K.handleCorner h b) * p.2.2 := by
  obtain ⟨x, hxB, hx⟩ := L.target_in_raw_tube h b ((K.rimChart h b).map_source hp)
  refine ⟨x, hx, hxB, ?_, ?_⟩
  · obtain ⟨hs, hheight⟩ := L.height_eq h b p hp
    obtain ⟨hs', hT⟩ := Pr.rows.labelledTubes.height_eq _ x hxB
    have hsub : (⟨(x : W.Carrier), hs'⟩ : Pr.rows.edge.source) = ⟨K.rimChart h b p, hs⟩ :=
      Subtype.ext hx
    rw [hT, hsub, hheight]
  · rw [Pr.rows.labelledTubes.face_eq _ x hxB, hx]
    exact L.horizontal_eq h b p hp

end Rim

/-- **GROUP G, `stub_rimRegionLayer_of_labelled` over V2** (frozen `T:339–346`, D58-1 edit). -/
theorem rimRegionLayer_of_labelled_GGFF (Pr : FC39PreparedV2 W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) (A : AdaptedEdgeRimDataV2 Pr safe)
    (V : VertexLayer W) (vlink : VertexModelLink Pr.rows V)
    {O : PortLayer W E V} {S : SeamLayer W V A.circ} {F : FaceLayer W E V S O}
    (HE : HandleEndLayer W V A.edges F)
    (hHE : ∀ h b, vlink.index (HE.handleEnd h b) = A.labelled.handleEndOwner h b) :
    RimRegionLayer W V A.edges A.circ HE A.rims where
  rim_vertex h b p hp := by
    obtain ⟨x, hx, hxB, -, hY⟩ := A.labelled.exists_tube_point_GHR h b hp
    have hsc := A.circ.cornerScale_pos (A.rims.handleCorner h b)
    rw [vlink.vertex_eq, Pr.rows.rowVertex_image, hHE, ← hx]
    refine (Pr.rows.labelledTubes.vertex_side hxB).trans ?_
    rw [hY]
    constructor
    · intro h1
      nlinarith
    · intro h1
      nlinarith
  rim_handle h b p hp := by
    obtain ⟨x, hx, hxB, hX, hY⟩ := A.labelled.exists_tube_point_GHR h b hp
    have hsc := A.circ.cornerScale_pos (A.rims.handleCorner h b)
    rw [A.labelled.edgeLink.handle_whole h, ← hx]
    change (x : W.Carrier) ∈
      Pr.rows.edge.wholeComponent (A.labelled.edgeLink.componentOfHandle h) ↔ _
    rw [← A.labelled.edgeLink.component_endOfHandle_GHR h b]
    refine (Pr.rows.labelledTubes.edge_side hxB).trans ?_
    rw [hX, hY]
    constructor
    · rintro ⟨h1, h2⟩
      constructor <;> nlinarith
    · rintro ⟨h1, h2⟩
      constructor <;> nlinarith
  rim_region h b p hp := by
    obtain ⟨x, hx, hxB, hX, hY⟩ := A.labelled.exists_tube_point_GHR h b hp
    have hsc := A.circ.cornerScale_pos (A.rims.handleCorner h b)
    rw [A.labelled.circleLink.region_eq, ← hx]
    refine (Pr.rows.labelledTubes.region_side hxB).trans ?_
    rw [hX, hY]
    constructor
    · rintro ⟨h1, h2⟩
      constructor <;> nlinarith
    · rintro ⟨h1, h2⟩
      constructor <;> nlinarith

/-- **The chain of the GROUP G order over V2**: the handle-end layer with its owner equation, and
the rim region layer of the SAME `A` and the SAME `HE`. -/
theorem exists_handleEndLayer_rimRegionLayer_GGFF (Pr : FC39PreparedV2 W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) (A : AdaptedEdgeRimDataV2 Pr safe)
    (V : VertexLayer W) (vlink : VertexModelLink Pr.rows V)
    (O : PortLayer W E V) (S : SeamLayer W V A.circ) (F : FaceLayer W E V S O)
    (sf : SeamFacesLink Pr.rows V vlink O S F safe.shared) :
    ∃ HE : HandleEndLayer W V A.edges F,
      (∀ h b, vlink.index (HE.handleEnd h b) = A.labelled.handleEndOwner h b) ∧
        RimRegionLayer W V A.edges A.circ HE A.rims := by
  obtain ⟨HE, hHE⟩ := handleEndLayer_of_labelled_GGFF Pr safe A V vlink O S F sf
  exact ⟨HE, hHE, rimRegionLayer_of_labelled_GGFF Pr safe A V vlink HE hHE⟩

end GC.GraphManifold.Assembly.FC39P0
