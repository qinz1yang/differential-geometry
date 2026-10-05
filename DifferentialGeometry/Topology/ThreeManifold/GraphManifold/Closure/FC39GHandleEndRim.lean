import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0HandleFaceResidual

/-!
# FC39 GROUP G, targets `stub_handleEndLayer_of_labelled` and `stub_rimRegionLayer_of_labelled`

Lane FC39-G-HE-RIM. The frozen targets `T:329–336` and `T:339–346`
(`docs/geometrization/chapter14/evidence/fc39-p0/Targets.lean.txt`), proved as general theorems on
the contract (external review 56, D56-1), on ONE adapted data `A`:

* `handleEndLayer_of_labelled` — the handle-end layer of the labelled compatibility, with the owner
  equation as OUTPUT: the end vertex of `(h, b)` is the vertex of the actual horizontal owner
  `A.labelled.handleEndOwner h b` (through the given vertex link), the end face is the catalogue
  index of the ACTUAL residual face of the horizontal label (`exists_face_eq_residualSet_GHR`: the
  residual face is a model boundary component of the owner's piece, it meets a face of that vertex
  by `face_exhausted`, and two meeting components are equal); the face is partitioned because it
  meets the safe corner tube at the rim point of the end disk (`faceKind_eq_partitioned_GHR`: an
  external face lies in a collar, a seam face is a shared face inside its safe neighbourhood, both
  avoid the closure of every safe corner tube); the end disks are disjoint by the component
  registration (`endDisks_disjoint_of_components`);
* `rimRegionLayer_of_labelled` — the rim region from the SAME `A` and the SAME `HE`, consuming the
  owner equation `hHE`: every rim chart point lies in the raw labelled tube, where the tube chart is
  `(λ x, λ y)` (`height_eq`, `horizontal_eq` against the tube's `height_eq`, `face_eq`) and the
  three labelled side equalities of the tube give vertex ⇔ `y ≤ 0`, handle ⇔ `y ≥ 0 ∧ x ≤ 0`,
  circle region ⇔ `x, y ≥ 0` (`λ > 0`).
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

/-! ## Generic facts -/

/-- The component of an endpoint is the component of its handle (any universe). -/
theorem EdgeComponentsLink.component_endOfHandle_GHR {P : EdgeBundle W}
    {M : EdgeComponentModels P} {H : EdgeLayer W} (L : EdgeComponentsLink P M H)
    (h : Fin H.handleCount) (b : Bool) :
    (L.endOfHandle h b).component = L.componentOfHandle h := by
  refine ActualComponent.eq_of_mem (z := (L.endOfHandle h b).1)
    (mem_connectedComponentIn (P.frontier_cbase_subset (L.endOfHandle h b).2)) ?_
  change (M.endpointEquiv (L.handleEquiv h, b)).1 ∈ (M.componentEquiv (.inl (L.handleEquiv h))).1
  rw [M.endpointEquiv_apply, ← M.intervalBase_range]
  exact ⟨_, rfl⟩

/-- A model boundary face of an equal piece lies in the model boundary image. -/
theorem ModelBoundaryFace.image_subset_boundaryImage_GHR {P P' : PieceEmbedding W} (hP : P = P')
    (m : ModelBoundaryFace P') : P'.map '' m.1 ⊆ P.map '' (𝓡∂ 3).boundary P.Piece := by
  subst hP
  exact image_mono (ActualComponent.subset m)

/-- The rim point of the end `b` of the handle `h` lies in the end disk. -/
theorem RimChartLayer.rimPoint_mem_endDisk_GHR {H : EdgeLayer W} {circ : CircleRegion W}
    (K : RimChartLayer W H circ) (h : Fin H.handleCount) (b : Bool) :
    K.rimChart h b ((1 : Circle), ((0 : ℝ), (0 : ℝ))) ∈ (H.handle h).endDisk b := by
  have hmem : K.rimChart h b ((1 : Circle), ((0 : ℝ), (0 : ℝ))) ∈
      K.rimChart h b '' {p | p.2 = (0, 0)} := ⟨_, rfl, rfl⟩
  rw [K.rim_label h b] at hmem
  obtain ⟨w, -, hw⟩ := hmem
  exact ⟨w, hw⟩

/-- The rim point of the end `b` of the handle `h` lies in the rim chart target. -/
theorem RimChartLayer.rimPoint_mem_target_GHR {H : EdgeLayer W} {circ : CircleRegion W}
    (K : RimChartLayer W H circ) (h : Fin H.handleCount) (b : Bool) :
    K.rimChart h b ((1 : Circle), ((0 : ℝ), (0 : ℝ))) ∈ (K.rimChart h b).target :=
  (K.rimChart h b).map_source ((K.rim_source h b).2 (by simp [rimBox]))

/-! ## The face catalogue: residual faces and kinds -/

section Catalogue

variable {Rw : FC39RowsV2 W E} {V : VertexLayer W} {vlink : VertexModelLink Rw V}
  {O : PortLayer W E V} {circ : CircleRegion W} {S : SeamLayer W V circ}
  {F : FaceLayer W E V S O}

/-- The residual face lies in the model boundary image of the vertex of its owner. -/
theorem VertexModelLink.residualSet_subset_boundaryImage_GHR (vlink : VertexModelLink Rw V)
    {R : Rw.slim.ResidualFace} {k : Fin V.vertexCount}
    (hk : vlink.index k = Rw.slim.residualOwner R) :
    Rw.slim.residualSet R ⊆ (V.vertex k).boundaryImage := by
  obtain ⟨m, hm⟩ := Rw.exists_residualSet_eq_image R
  rw [hm]
  exact ModelBoundaryFace.image_subset_boundaryImage_GHR (by rw [vlink.vertex_piece, hk]) m

/-- **The catalogue face of a residual face**: for the vertex `k` of the owner of a non-empty
residual face, some face of `k` IS the residual face. -/
theorem SeamFacesLink.exists_face_eq_residualSet_GHR
    {N : Rw.SharedFace → TopologicalSpace.Opens W.Carrier}
    (sf : SeamFacesLink Rw V vlink O S F N) {R : Rw.slim.ResidualFace} {k : Fin V.vertexCount}
    (hk : vlink.index k = Rw.slim.residualOwner R) (hne : (Rw.slim.residualSet R).Nonempty) :
    ∃ f, F.faceOwner f = k ∧ F.face f = Rw.slim.residualSet R := by
  obtain ⟨x, hx⟩ := hne
  have hxB := vlink.residualSet_subset_boundaryImage_GHR hk hx
  rw [← F.face_exhausted] at hxB
  obtain ⟨f, hfk, hxf⟩ := mem_iUnion₂.1 hxB
  refine ⟨f, hfk, ?_⟩
  obtain ⟨m₁, hm₁⟩ := sf.exists_face_eq_image f
  obtain ⟨m₂, hm₂⟩ := Rw.exists_residualSet_eq_image R
  rw [hm₁, hm₂]
  refine ModelBoundaryFace.image_eq_of_meet (by rw [vlink.vertex_piece, hfk, hk]) ⟨x, ?_, ?_⟩
  · rw [← hm₁]
    exact hxf
  · rw [← hm₂]
    exact hx

/-- **A face meeting a safe corner tube is partitioned**: an external face is a boundary torus
inside its collar, a seam face is a shared face inside its safe neighbourhood, and the closure of
every safe corner tube avoids both. -/
theorem SeamFacesLink.faceKind_eq_partitioned_GHR {safe : ProducerSafeNeighbourhoods Rw}
    (sf : SeamFacesLink Rw V vlink O S F safe.shared) {f : Fin F.faceCount}
    {e : Rw.edge.EdgeEnd} (hmeet : (F.face f ∩ safe.corner e).Nonempty) :
    F.faceKind f = .partitioned := by
  obtain ⟨y, hyF, hyC⟩ := hmeet
  have hyC' : y ∈ closure (Rw.circle.tube (safe.cornerBase e)) := subset_closure hyC
  generalize hk : F.faceKind f = k
  cases k with
  | external i =>
    exfalso
    rw [(F.face_external f i hk).1] at hyF
    obtain ⟨t, rfl⟩ := hyF
    exact disjoint_left.1 (safe.corner_off_external e i) hyC'
      ((E.collar i).map_source ((E.source_eq i).symm ▸ zero_mem_halfCollarSource t))
  | torusSeam c b =>
    exfalso
    rw [(F.face_torusSeam f c b hk).1, sf.torus_slim c] at hyF
    exact disjoint_left.1 (safe.corner_off_shared e (sf.torusEquiv c).1) hyC'
      (subset_closure (safe.shared_safe.face_subset _ hyF))
  | sphereSeam c b =>
    exfalso
    rw [(F.face_sphereSeam f c b hk).1, sf.sphere_slim c] at hyF
    exact disjoint_left.1 (safe.corner_off_shared e (sf.sphereEquiv c).1) hyC'
      (subset_closure (safe.shared_safe.face_subset _ hyF))
  | partitioned => rfl

end Catalogue

/-! ## The handle-end layer of the adapted data -/

section HandleEnd

variable {Pr : FC39Prepared W E} {safe : ProducerSafeNeighbourhoods Pr.rows}
  {V : VertexLayer W} {O : PortLayer W E V} {circ' : CircleRegion W} {S : SeamLayer W V circ'}
  {F : FaceLayer W E V S O}

/-- The end face of `(h, b)`: a face of the vertex of the actual horizontal owner which IS the
residual face of the horizontal label and is partitioned. -/
theorem AdaptedEdgeRimData.exists_handleFace_GHR (A : AdaptedEdgeRimData Pr safe)
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

/-- **The handle-end layer of the labelled compatibility**: end vertex = the vertex of the actual
horizontal owner, end face = the catalogue face of the actual residual face. -/
def AdaptedEdgeRimData.handleEndLayer_GHR (A : AdaptedEdgeRimData Pr safe)
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

theorem AdaptedEdgeRimData.handleEndLayer_GHR_handleEnd (A : AdaptedEdgeRimData Pr safe)
    (vlink : VertexModelLink Pr.rows V) (sf : SeamFacesLink Pr.rows V vlink O S F safe.shared)
    (h : Fin A.edges.handleCount) (b : Bool) :
    (A.handleEndLayer_GHR vlink sf).handleEnd h b =
      vlink.index.symm (A.labelled.handleEndOwner h b) :=
  rfl

/-- **The owner equation (output)**: the end vertex is the actual horizontal owner. -/
theorem AdaptedEdgeRimData.handleEndLayer_GHR_index (A : AdaptedEdgeRimData Pr safe)
    (vlink : VertexModelLink Pr.rows V) (sf : SeamFacesLink Pr.rows V vlink O S F safe.shared)
    (h : Fin A.edges.handleCount) (b : Bool) :
    vlink.index ((A.handleEndLayer_GHR vlink sf).handleEnd h b) = A.labelled.handleEndOwner h b :=
  vlink.index.apply_symm_apply _

/-- The end face of the constructed layer is the actual residual face of the horizontal label. -/
theorem AdaptedEdgeRimData.handleEndLayer_GHR_face (A : AdaptedEdgeRimData Pr safe)
    (vlink : VertexModelLink Pr.rows V) (sf : SeamFacesLink Pr.rows V vlink O S F safe.shared)
    (h : Fin A.edges.handleCount) (b : Bool) :
    F.face ((A.handleEndLayer_GHR vlink sf).handleFace h b) = Pr.rows.slim.residualSet
      (Pr.rows.junctions.horizontal (A.labelled.edgeLink.endOfHandle h b)) :=
  (A.exists_handleFace_GHR vlink sf h b).choose_spec.2.1

end HandleEnd

/-- **GROUP G, `stub_handleEndLayer_of_labelled` (frozen statement `T:329–336`).** -/
theorem handleEndLayer_of_labelled (Pr : FC39Prepared W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) (A : AdaptedEdgeRimData Pr safe)
    (V : VertexLayer W) (vlink : VertexModelLink Pr.rows V)
    (O : PortLayer W E V) (S : SeamLayer W V A.circ) (F : FaceLayer W E V S O)
    (sf : SeamFacesLink Pr.rows V vlink O S F safe.shared) :
    ∃ HE : HandleEndLayer W V A.edges F,
      ∀ h b, vlink.index (HE.handleEnd h b) = A.labelled.handleEndOwner h b :=
  ⟨A.handleEndLayer_GHR vlink sf, A.handleEndLayer_GHR_index vlink sf⟩

/-! ## The rim region -/

section Rim

variable {Pr : FC39Prepared W E} {H : EdgeLayer W} {circ : CircleRegion W}
  {K : RimChartLayer W H circ}

/-- **A rim chart point in the raw labelled tube**, where the tube chart is `(λ x, λ y)`. -/
theorem LabelledCornerCompatibility.exists_tube_point_GHR
    (L : LabelledCornerCompatibility Pr H circ K) (h : Fin H.handleCount) (b : Bool)
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

/-- **GROUP G, `stub_rimRegionLayer_of_labelled` (frozen statement `T:339–346`).** -/
theorem rimRegionLayer_of_labelled (Pr : FC39Prepared W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) (A : AdaptedEdgeRimData Pr safe)
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

/-! ## The chain `(A, V, S, F, sf) → (HE, hHE) → RimRegionLayer` on one `A` -/

/-- **The chain of the GROUP G order** (D56 lane plan): the handle-end layer of the labelled data
with its owner equation, and the rim region layer of the SAME `A` and the SAME `HE`, the rim region
consuming the owner equation. -/
theorem exists_handleEndLayer_rimRegionLayer_GHR (Pr : FC39Prepared W E)
    (safe : ProducerSafeNeighbourhoods Pr.rows) (A : AdaptedEdgeRimData Pr safe)
    (V : VertexLayer W) (vlink : VertexModelLink Pr.rows V)
    (O : PortLayer W E V) (S : SeamLayer W V A.circ) (F : FaceLayer W E V S O)
    (sf : SeamFacesLink Pr.rows V vlink O S F safe.shared) :
    ∃ HE : HandleEndLayer W V A.edges F,
      (∀ h b, vlink.index (HE.handleEnd h b) = A.labelled.handleEndOwner h b) ∧
        RimRegionLayer W V A.edges A.circ HE A.rims := by
  obtain ⟨HE, hHE⟩ := handleEndLayer_of_labelled Pr safe A V vlink O S F sf
  exact ⟨HE, hHE, rimRegionLayer_of_labelled Pr safe A V vlink HE hHE⟩

end GC.GraphManifold.Assembly.FC39P0
