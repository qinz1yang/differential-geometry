import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereJointLinks
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereCornersAdapted

/-!
# FC39 producer, packet P0 (gate 1): the S³ joint layers on the WIDE rows

The certificate of the one S³ configuration is built on the WIDE prepared rows
`spherePreparedW sphereJunctions` of lane FC39-CIRC-C (the narrow rows cannot carry
`rim_closure_in_safe`), with the adapted edge–rim data `sphereJointAdaptedEdgeRimData`
(edge layer `sphereEdgeLayer`, circle region `sphereCircleRegion`, rim layer `sphereRimLayer`).

* `sphereRows_wide` — the rows of FC39-JOINT G2 at the wide tubes ARE the wide prepared rows
  (`rfl`); the joint links of §2 restated on them (`sphereVertexModelLinkW`, `spherePortModelLinkW`,
  `sphereSeamFacesLinkW` with the safe neighbourhoods `(sphereSafe sphereJunctions).shared`);
* `sphereHandleEndLayer` — the handle ends read from the SAME actual horizontal labels: the end
  vertex of `(h, b)` is the row vertex of `sphereJointLabelledCompatibility.handleEndOwner h b`
  (`sphereHandleEnd_index`), the end face the level sphere of the label (`sphereLabelFace`:
  `false ↦ 2` (`r = 1`), `true ↦ 3` (`r = 4`));
* `sphereRimRegionLayer` — the three side equalities on the whole rim box, from the labelled tubes;
* `sphereCoverLayer`, `sphereVerticalLayer`, `sphereProtectionLayer`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

/-! ## The wide rows and the joint links on them -/

/-- **The rows of FC39-JOINT G2 at the wide tubes are the wide prepared rows.** -/
theorem sphereRows_wide :
    sphereRows (sphereLabelledTubesW sphereJunctions) = (spherePreparedW sphereJunctions).rows :=
  rfl

/-- `VertexModelLink` on the wide prepared rows. -/
def sphereVertexModelLinkW :
    VertexModelLink (spherePreparedW sphereJunctions).rows sphereVertexLayer :=
  sphereVertexModelLink (sphereLabelledTubesW sphereJunctions)

theorem sphereVertexModelLinkW_index (k : Fin 3) : sphereVertexModelLinkW.index k = sphereRowIndex k :=
  rfl

/-- `PortModelLink` on the wide prepared rows (no ports). -/
theorem spherePortModelLinkW :
    PortModelLink (spherePreparedW sphereJunctions).rows sphereVertexModelLinkW spherePortLayer :=
  spherePortModelLink (sphereLabelledTubesW sphereJunctions)

/-- `SeamFacesLink` on the wide prepared rows, with the safe neighbourhoods of `sphereSafe`. -/
def sphereSeamFacesLinkW :
    SeamFacesLink (spherePreparedW sphereJunctions).rows sphereVertexLayer sphereVertexModelLinkW
      spherePortLayer sphereSeamLayer sphereFaceLayer (sphereSafe sphereJunctions).shared :=
  sphereSeamFacesLink (sphereLabelledTubesW sphereJunctions)

theorem sphereVertexLayer_image_W (k : Fin sphereVertexLayer.vertexCount) :
    (sphereVertexLayer.vertex k).image = sphereSlimPieces.rowSet (sphereRowIndex k) :=
  sphereVertexLayer_image (sphereLabelledTubesW sphereJunctions) k

theorem sphereVertexLayer_image_W3 (k : Fin 3) :
    (sphereVertexLayer.vertex k).image = sphereSlimPieces.rowSet (sphereRowIndex k) :=
  sphereVertexLayer_image (sphereLabelledTubesW sphereJunctions) k

/-! ## The face of a label -/

/-- The face of the horizontal label `σ`: `false ↦ 2` (`r = 1`, the new slim end), `true ↦ 3`
(`r = 4`, the face of `Z₊`). -/
def sphereLabelFace (σ : Bool) : Fin 4 :=
  bif σ then 3 else 2

theorem sphereLabelFace_injective : Injective sphereLabelFace := by
  intro σ σ' h
  cases σ <;> cases σ' <;> first | rfl | exact absurd h (by decide)

theorem sphereFaceKind_labelFace (σ : Bool) : sphereFaceKind (sphereLabelFace σ) = .partitioned := by
  cases σ <;> rfl

theorem sphereFaceSet_labelFace (σ : Bool) :
    sphereFaceSet (sphereLabelFace σ) = {x | sphereHeight x = sphereResidualHeight σ} := by
  rw [sphereFaceSet_eq]
  cases σ
  · change {x | sphereHeight x = -3 / 5} = {x | sphereHeight x = -3 / 5}
    rfl
  · change {x | sphereHeight x = 3 / 5} = {x | sphereHeight x = 3 / 5}
    rfl

theorem sphereFaceSet_labelFace_residual (σ : Bool) :
    sphereFaceSet (sphereLabelFace σ) = sphereSlimPieces.residualSet (sphereResidual σ) := by
  rw [sphereFaceSet_labelFace, residualSet_sphereResidual]

/-- A partitioned face of the S³ face layer is the face of a label. -/
theorem exists_labelFace_of_partitioned {f : Fin 4} (hf : sphereFaceKind f = .partitioned) :
    ∃ σ, f = sphereLabelFace σ := by
  fin_cases f
  · change FaceKind.sphereSeam 0 true = _ at hf
    cases hf
  · change FaceKind.sphereSeam 0 false = _ at hf
    cases hf
  · exact ⟨false, rfl⟩
  · exact ⟨true, rfl⟩

/-! ## The handle ends, read from the actual horizontal labels -/

/-- **The end vertex of `(h, b)`**: the row vertex of the owner of the actual horizontal label. -/
def sphereHandleEnd (h : Fin 2) (b : Bool) : Fin 3 :=
  sphereRowIndex.symm (sphereJointLabelledCompatibility.handleEndOwner h b)

/-- **The agreement with the actual horizontal owner** (review 49, the arc-layer note). -/
theorem sphereHandleEnd_index (h : Fin 2) (b : Bool) :
    sphereRowIndex (sphereHandleEnd h b) = sphereJointLabelledCompatibility.handleEndOwner h b :=
  Equiv.apply_symm_apply _ _

theorem sphereHandleEndOwner_eq (h : Fin 2) (b : Bool) :
    sphereJointLabelledCompatibility.handleEndOwner h b =
      sphereSlimPieces.residualOwner (sphereResidual (edgeEndLabel (h, b))) := by
  change sphereSlimPieces.residualOwner (sphereJunctions.horizontal (sphereEdgeEndEquiv (h, b))) = _
  rw [sphereJunctions_horizontal, sphereHorizontal_apply]

theorem sphereHandleEnd_eq (h : Fin 2) (b : Bool) :
    sphereHandleEnd h b = sphereFaceLayer.faceOwner (sphereLabelFace (edgeEndLabel (h, b))) := by
  unfold sphereHandleEnd
  rw [sphereHandleEndOwner_eq]
  generalize edgeEndLabel (h, b) = σ
  cases σ
  · rw [residualOwner_sphereResidual_false]
    rfl
  · rw [residualOwner_sphereResidual_true]
    rfl

/-- The end disk of `(h, b)` is the whole disk over the registered endpoint. -/
theorem sphereEndDisk_eq (h : Fin 2) (b : Bool) :
    (sphereEdgeLayer.handle h).endDisk b = sphereEdgeBundle.disk (sphereEdgeEndEquiv (h, b)).1 :=
  (sphereEdge_disk_eq (h, b)).symm

theorem sphereEndDisk_subset_level (h : Fin 2) (b : Bool) :
    (sphereEdgeLayer.handle h).endDisk b ⊆
      {x | sphereHeight x = sphereResidualHeight (edgeEndLabel (h, b))} := by
  rw [sphereEndDisk_eq, ← residualSet_sphereResidual, ← sphereHorizontal_apply]
  exact sphere_horizontal_disk _

theorem sphereEndDisk_disjoint {h h' : Fin 2} {b b' : Bool} (hne : (h, b) ≠ (h', b')) :
    Disjoint ((cycleS3Handle (finTwoEquiv h)).endDisk b)
      ((cycleS3Handle (finTwoEquiv h')).endDisk b') :=
  sphereEdgeLayer_disjoint.2 (i := (h, b)) (j := (h', b')) hne

/-- **The handle end layer of the S³ configuration.** -/
def sphereHandleEndLayer :
    HandleEndLayer sphereW sphereVertexLayer sphereEdgeLayer sphereFaceLayer where
  handleEnd := sphereHandleEnd
  handleFace h b := sphereLabelFace (edgeEndLabel (h, b))
  handleFace_owner h b := (sphereHandleEnd_eq h b).symm
  handleFace_kind h b := sphereFaceKind_labelFace _
  handleEnd_face h b := by
    change _ ⊆ sphereFaceSet (sphereLabelFace (edgeEndLabel (h, b)))
    rw [sphereFaceSet_labelFace]
    exact sphereEndDisk_subset_level h b
  endDisk_disjoint h b h' b' hne := sphereEndDisk_disjoint hne

theorem sphereHandleEndLayer_handleFace (h : Fin 2) (b : Bool) :
    sphereHandleEndLayer.handleFace h b = sphereLabelFace (edgeEndLabel (h, b)) :=
  rfl

/-! ## The rim region -/

/-- The component of an endpoint is the component of its handle (any component registration). -/
theorem EdgeComponentsLink.component_endOfHandle_JOINT2 {W : CompactCarrier.{0}} {P : EdgeBundle W}
    {M : EdgeComponentModels P} {H : EdgeLayer W} (L : EdgeComponentsLink P M H)
    (h : Fin H.handleCount) (b : Bool) :
    (L.endOfHandle h b).component = L.componentOfHandle h := by
  refine ActualComponent.eq_of_mem (z := (L.endOfHandle h b).1)
    (mem_connectedComponentIn (P.frontier_cbase_subset (L.endOfHandle h b).2)) ?_
  change (M.endpointEquiv (L.handleEquiv h, b)).1 ∈ (M.componentEquiv (.inl (L.handleEquiv h))).1
  rw [M.endpointEquiv_apply, ← M.intervalBase_range]
  exact ⟨_, rfl⟩

theorem range_sphereHandle_eq_wholeComponent (h : Fin 2) (b : Bool) :
    range (sphereEdgeLayer.handle h).map =
      sphereEdgeBundle.wholeComponent (sphereEdgeEndEquiv (h, b)).component := by
  rw [sphereEdgeLink.handle_whole h]
  exact congrArg sphereEdgeBundle.wholeComponent
    (EdgeComponentsLink.component_endOfHandle_JOINT2 sphereEdgeLink h b).symm

/-- On the rim chart of the end `b` of the handle `h`: the handle ⇔ `y ≥ 0 ∧ x ≤ 0`. -/
theorem circRim_handle_iff (h : Fin 2) (b : Bool) {p : Circle × (ℝ × ℝ)} (hp : p.2 ∈ rimBox 2) :
    circRim (finTwoEquiv h) b p ∈ range (cycleS3Handle (finTwoEquiv h)).map ↔
      (0 ≤ p.2.2 ∧ p.2.1 ≤ 0) := by
  obtain ⟨hx, hbase, hchart⟩ := circRim_tube_point (finTwoEquiv h) b hp
  have hs := circTube_edge_side (x := ⟨circRim (finTwoEquiv h) b p, hx⟩) hbase
  rw [hchart] at hs
  simp only [Equiv.symm_apply_apply] at hs
  have hr := range_sphereHandle_eq_wholeComponent h b
  change range (cycleS3Handle (finTwoEquiv h)).map = _ at hr
  rw [hr]
  refine hs.trans ?_
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-- On the rim chart of the end `b` of the handle `h`: the circle region ⇔ `x, y ≥ 0`. -/
theorem circRim_region_iff (h : Fin 2) (b : Bool) {p : Circle × (ℝ × ℝ)} (hp : p.2 ∈ rimBox 2) :
    circRim (finTwoEquiv h) b p ∈ sphereCircleBundle.region ↔ (0 ≤ p.2.1 ∧ 0 ≤ p.2.2) := by
  obtain ⟨hx, hbase, hchart⟩ := circRim_tube_point (finTwoEquiv h) b hp
  have hs := circTube_region_side (x := ⟨circRim (finTwoEquiv h) b p, hx⟩) hbase
  rw [hchart] at hs
  refine hs.trans ?_
  change 0 ≤ 1 / 16 * p.2.1 ∧ 0 ≤ 1 / 16 * p.2.2 ↔ _
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

/-- On the rim chart of the end `b` of the handle `h`: the end vertex ⇔ `y ≤ 0`. -/
theorem circRim_vertex_iff (h : Fin 2) (b : Bool) {p : Circle × (ℝ × ℝ)}
    (hp : p ∈ (sphereRimLayer.rimChart h b).source) :
    sphereRimLayer.rimChart h b p ∈ (sphereVertexLayer.vertex (sphereHandleEnd h b)).image ↔
      p.2.2 ≤ 0 := by
  rw [sphereVertexLayer_image_W3, sphereHandleEnd_index]
  exact circRim_vertex_side sphereJunctions h b hp

/-- **The rim region layer of the S³ configuration** (vertex ⇔ `y ≤ 0`, handle ⇔ `y ≥ 0 ∧ x ≤ 0`,
circle region ⇔ `x, y ≥ 0` on the whole rim box), from the labelled corner tubes. -/
theorem sphereRimRegionLayer :
    RimRegionLayer sphereW sphereVertexLayer sphereEdgeLayer sphereCircleRegion sphereHandleEndLayer
      sphereRimLayer where
  rim_vertex h b _ hp := circRim_vertex_iff h b hp
  rim_handle h b _ hp := circRim_handle_iff h b ((mem_circRim_source _ _).1 hp)
  rim_region h b _ hp := circRim_region_iff h b ((mem_circRim_source _ _).1 hp)

/-! ## Cover, vertical faces, protection -/

theorem range_sphereHandle_subset_edgePiece (h : Fin 2) :
    range (sphereEdgeLayer.handle h).map ⊆ sphereEdgeBundle.edgePiece := by
  rw [sphere_edgePiece_eq]
  exact subset_iUnion (fun b => range (cycleS3Handle b).map) (finTwoEquiv h)

/-- **The cover layer of the S³ configuration.** -/
theorem sphereCoverLayer :
    CoverLayer sphereW sphereVertexLayer sphereEdgeLayer sphereCircleRegion where
  cover := by
    refine eq_univ_of_forall fun x => ?_
    have hx : x ∈ ⋃ a, allPieces sphereSlimPieces sphereEdgeBundle sphereCircleBundle a := by
      rw [sphere_cover]
      exact mem_univ x
    obtain ⟨a, ha⟩ := mem_iUnion.1 hx
    rcases a with i | (_ | _)
    · refine Or.inl (Or.inl (Or.inl (mem_iUnion.2 ⟨sphereRowIndex.symm i, ?_⟩)))
      rw [sphereVertexLayer_image_W3, Equiv.apply_symm_apply]
      exact ha
    · exact Or.inr ha
    · have he := sphereEdgeLink.iUnion_ranges_eq_edgePiece
      change x ∈ sphereEdgeBundle.edgePiece at ha
      rw [← he] at ha
      rcases ha with h1 | h2
      · exact Or.inl (Or.inl (Or.inr h1))
      · exact Or.inl (Or.inr h2)
  vertex_disjoint k k' hne := by
    change Disjoint (interior (sphereVertexLayer.vertex k).image)
      (interior (sphereVertexLayer.vertex k').image)
    rw [sphereVertexLayer_image_W, sphereVertexLayer_image_W]
    exact sphere_interiors_disjoint (i := .inl (sphereRowIndex k)) (j := .inl (sphereRowIndex k'))
      fun h => hne (sphereRowIndex.injective (Sum.inl_injective h))
  handle_disjoint h h' hne := (sphereEdgeLayer_disjoint.1 hne).mono interior_subset interior_subset
  edgeCircle_disjoint e := e.elim0
  vertex_handle_disjoint k h := by
    rw [sphereVertexLayer_image_W]
    exact (sphere_interiors_disjoint (i := .inl (sphereRowIndex k)) (j := .inr true)
      Sum.inl_ne_inr).mono_right (interior_mono (range_sphereHandle_subset_edgePiece h))
  edgeCircle_vertex_disjoint e := e.elim0
  edgeCircle_handle_disjoint e := e.elim0
  circ_vertex_disjoint k := by
    rw [sphereVertexLayer_image_W]
    exact sphere_interiors_disjoint (i := .inr false) (j := .inl (sphereRowIndex k)) Sum.inr_ne_inl
  circ_handle_disjoint h :=
    (sphere_interiors_disjoint (i := .inr false) (j := .inr true) (by simp)).mono_right
      (interior_mono (range_sphereHandle_subset_edgePiece h))
  circ_edgeCircle_disjoint e := e.elim0

/-- **The vertical layer of the S³ configuration**: every handle rim slice is a whole circle
fibre. -/
theorem sphereVerticalLayer : VerticalLayer sphereW sphereEdgeLayer sphereCircleRegion where
  vertical_fibre h t :=
    ⟨sphereRimBase (edgeInterval (finTwoEquiv h) t), sphereHandle_rim_eq_fibre (finTwoEquiv h) t⟩
  edgeCircle_vertical e := e.elim0

theorem sphereSharedSeam_target_subset_closure_near :
    sphereSharedSeam.collar.target ⊆ closure (sphereSharedNear : Set sphereW.Carrier) :=
  subset_closure.trans (closure_sphereSharedSeam_target.trans subset_closure)

/-- **The protection layer of the S³ configuration**: no port; the sphere seam collar avoids the
rim targets (they lie in the safe corner tubes), the circle region and the handles. -/
theorem sphereProtectionLayer :
    ProtectionLayer sphereW (BoundaryTori.empty sphereW) sphereEdgeLayer sphereCircleRegion
      sphereSeamLayer sphereRimLayer where
  external_region_disjoint i := i.elim0
  external_handle_disjoint i := i.elim0
  external_edgeCircle_disjoint i := i.elim0
  external_torusSeam_disjoint i := i.elim0
  external_sphereSeam_disjoint i := i.elim0
  rim_external_disjoint _ _ i := i.elim0
  rim_torusSeam_disjoint _ _ c := c.elim0
  rim_sphereSeam_disjoint h b _ :=
    (circSafe_off_shared (sphereEdgeEndEquiv (h, b))).mono
      (subset_closure.trans ((closure_circRim_target_subset h b).trans subset_closure))
      sphereSharedSeam_target_subset_closure_near
  sphereSeam_region_disjoint _ :=
    (sphereSharedNear_off_region.mono_left sphereSharedSeam_target_subset_closure_near)
  sphereSeam_handle_disjoint _ h :=
    (sphereSharedNear_off_edge.mono sphereSharedSeam_target_subset_closure_near
      (range_sphereHandle_subset_edgePiece h))

end GC.GraphManifold.Assembly.FC39P0
