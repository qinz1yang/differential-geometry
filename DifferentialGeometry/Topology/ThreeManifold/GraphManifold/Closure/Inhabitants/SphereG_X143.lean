import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.FibreG_X143
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GFinalClosed
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereJointJunctions
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereCornersAdapted

/-!
# X143: S³ through the general FC39 chain

Review 73 D73-6a: select prepared rows, safe neighbourhoods and adapted data from the
general producers. The pointwise assembly consumes these very data. The independent
rows-only existence entry is exercised too; no equality between opaque choices is claimed.
-/
set_option autoImplicit false
noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly.FC39P0.General_X143

/-- The raw S³ rows admit global face functions by the general producer. -/
theorem sphereGlobalFaces_exists_X143 :
    Nonempty (GlobalFaceFunctionsV2 (sphereRowsW sphereJunctions)) :=
  exists_globalFaceFunctions_GGFF (sphereRowsW sphereJunctions)

/-- The general prepared theorem uses GGFF, with no sphere-specific face-function input. -/
def spherePrepared_X143 : FC39PreparedV2 sphereW (BoundaryTori.empty sphereW) :=
  (exists_preparedV2_GGFF (sphereRowsW sphereJunctions)).choose

theorem spherePrepared_rows_X143 : spherePrepared_X143.rows = sphereRowsW sphereJunctions :=
  (exists_preparedV2_GGFF (sphereRowsW sphereJunctions)).choose_spec

def sphereSafe_X143 : ProducerSafeNeighbourhoods spherePrepared_X143.rows :=
  (exists_safeNeighbourhoods_GSAFE spherePrepared_X143.rows).some

def sphereAdapted_X143 : AdaptedEdgeRimDataV2 spherePrepared_X143 sphereSafe_X143 :=
  (exists_adaptedEdgeRimDataV2_GRIM spherePrepared_X143 sphereSafe_X143).some

def sphereVertices_X143 : VertexLayer sphereW :=
  (exists_vertexLayer_portLayer_G1 spherePrepared_X143.rows).choose

def sphereVertexLink_X143 : VertexModelLink spherePrepared_X143.rows sphereVertices_X143 :=
  (exists_vertexLayer_portLayer_G1 spherePrepared_X143.rows).choose_spec.choose

def spherePorts_X143 : PortLayer sphereW (BoundaryTori.empty sphereW) sphereVertices_X143 :=
  (exists_vertexLayer_portLayer_G1 spherePrepared_X143.rows).choose_spec.choose_spec.choose

theorem spherePortLink_X143 : PortModelLink spherePrepared_X143.rows sphereVertexLink_X143
  spherePorts_X143 :=
  (exists_vertexLayer_portLayer_G1 spherePrepared_X143.rows).choose_spec.choose_spec.choose_spec

def sphereSeams_X143 : SeamLayer sphereW sphereVertices_X143 sphereAdapted_X143.circ :=
  (exists_seams_faces_GSF spherePrepared_X143.rows sphereVertices_X143 sphereVertexLink_X143
    sphereAdapted_X143.circ spherePorts_X143 spherePortLink_X143
    sphereSafe_X143.shared sphereSafe_X143.shared_safe).choose

def sphereFaces_X143 : FaceLayer sphereW (BoundaryTori.empty sphereW) sphereVertices_X143
  sphereSeams_X143 spherePorts_X143 :=
  (exists_seams_faces_GSF spherePrepared_X143.rows sphereVertices_X143 sphereVertexLink_X143
    sphereAdapted_X143.circ spherePorts_X143 spherePortLink_X143
    sphereSafe_X143.shared sphereSafe_X143.shared_safe).choose_spec.choose

def sphereSeamFacesLink_X143 : SeamFacesLink spherePrepared_X143.rows sphereVertices_X143
  sphereVertexLink_X143 spherePorts_X143 sphereSeams_X143 sphereFaces_X143 sphereSafe_X143.shared :=
  (exists_seams_faces_GSF spherePrepared_X143.rows sphereVertices_X143 sphereVertexLink_X143
    sphereAdapted_X143.circ spherePorts_X143 spherePortLink_X143
    sphereSafe_X143.shared sphereSafe_X143.shared_safe).choose_spec.choose_spec.some

def sphereArcs_X143 : ArcLayer sphereW sphereAdapted_X143.edges sphereAdapted_X143.circ
  sphereFaces_X143
    (sphereAdapted_X143.handleEndLayer_GHR sphereVertexLink_X143 sphereSeamFacesLink_X143)
      sphereAdapted_X143.rims :=
  (stub_exists_arcLayer_GARC spherePrepared_X143 sphereSafe_X143 sphereAdapted_X143
    sphereVertices_X143 sphereVertexLink_X143 spherePorts_X143 sphereSeams_X143 sphereFaces_X143
    sphereSeamFacesLink_X143 (sphereAdapted_X143.handleEndLayer_GHR sphereVertexLink_X143
    sphereSeamFacesLink_X143)).some

def sphereCertificate_X143 : StrongCertificate sphereW (BoundaryTori.empty sphereW) :=
  strongCertificateOfAdapted_GFIN spherePrepared_X143 sphereSafe_X143 sphereAdapted_X143

/-- Exactly these general seams, faces and arcs are consumed by the pointwise final landing. -/
theorem sphereCertificate_assembly_X143 : sphereCertificate_X143 =
    strongCertificateOfRemainingLabelled_GFIN spherePrepared_X143.rows
      spherePrepared_X143.globalFaces sphereSafe_X143 sphereVertices_X143 sphereVertexLink_X143
      spherePorts_X143 sphereAdapted_X143 sphereSeams_X143 sphereFaces_X143 sphereSeamFacesLink_X143
      sphereArcs_X143 := rfl

/-- Exercise the public rows-only final entry, without a supplied adapted-data premise. -/
theorem sphereFinalRows_X143 : Nonempty (StrongCertificate sphereW (BoundaryTori.empty sphereW)) :=
  exists_strongCertificate_of_rows_GFIN (sphereRowsW sphereJunctions)

theorem sphereCertificate_circ_X143 : sphereCertificate_X143.1.circ = sphereAdapted_X143.circ := rfl

theorem sphereCertificate_region_X143 :
    sphereCertificate_X143.1.circ.region = (sphereRowsW sphereJunctions).circle.region := by
  change sphereAdapted_X143.circ.region = _
  rw [sphereAdapted_X143.circle.region_eq, spherePrepared_rows_X143]

theorem sphereCertificate_handleCount_X143 : sphereCertificate_X143.1.handleCount =
  sphereAdapted_X143.edges.handleCount := rfl

theorem sphereCertificate_edgeCircleCount_X143 :
    sphereCertificate_X143.1.edgeCircleCount = sphereAdapted_X143.edges.edgeCircleCount := rfl

theorem sphereCertificate_handle_X143 (h : Fin sphereAdapted_X143.edges.handleCount) :
    sphereCertificate_X143.1.handle h = sphereAdapted_X143.edges.handle h := rfl

theorem sphereCertificate_edgeCircle_X143 (j : Fin sphereAdapted_X143.edges.edgeCircleCount) :
    sphereCertificate_X143.1.edgeCircle j = sphereAdapted_X143.edges.edgeCircle j := rfl

theorem sphereCertificate_rimChart_X143 (h : Fin sphereAdapted_X143.edges.handleCount) (b : Bool) :
    sphereCertificate_X143.1.rimChart h b = sphereAdapted_X143.rims.rimChart h b := rfl

theorem sphereCertificate_handleCorner_X143 (h : Fin sphereAdapted_X143.edges.handleCount) (b :
  Bool) :
    sphereCertificate_X143.1.handleCorner h b = sphereAdapted_X143.rims.handleCorner h b := rfl

theorem sphereCertificate_handle_whole_X143 (h : Fin sphereAdapted_X143.edges.handleCount) :
    range (sphereCertificate_X143.1.handle h).map = spherePrepared_X143.rows.edge.wholeComponent
      (spherePrepared_X143.rows.edgeModels.componentEquiv (.inl
        (sphereAdapted_X143.components.handleEquiv h))) :=
  sphereAdapted_X143.components.handle_whole h

theorem sphereCertificate_circle_whole_X143 (j : Fin sphereAdapted_X143.edges.edgeCircleCount) :
    range (sphereCertificate_X143.1.edgeCircle j).piece.map =
      spherePrepared_X143.rows.edge.wholeComponent
      (spherePrepared_X143.rows.edgeModels.componentEquiv (.inr
        (sphereAdapted_X143.components.circleEquiv j))) :=
  sphereAdapted_X143.components.circle_whole j

theorem sphereCertificate_disk_X143 (h : Fin sphereAdapted_X143.edges.handleCount) (t : Icc (0 : ℝ)
  1) :
    range (fun w => (sphereCertificate_X143.1.handle h).map (w, t)) =
      spherePrepared_X143.rows.edge.disk (spherePrepared_X143.rows.edgeModels.intervalBase
        (sphereAdapted_X143.components.handleEquiv h) t) :=
  sphereAdapted_X143.components.handle_disk h t

theorem sphereCertificate_rim_X143 (h : Fin sphereAdapted_X143.edges.handleCount) (t : Icc (0 : ℝ)
  1) :
    (fun w => (sphereCertificate_X143.1.handle h).map (w, t)) '' diskRim =
      spherePrepared_X143.rows.edge.rim (spherePrepared_X143.rows.edgeModels.intervalBase
        (sphereAdapted_X143.components.handleEquiv h) t) :=
  sphereAdapted_X143.components.handle_rim h t

theorem sphereCertificate_endDisk_X143 (h : Fin sphereAdapted_X143.edges.handleCount) (b : Bool) :
    (sphereCertificate_X143.1.handle h).endDisk b = spherePrepared_X143.rows.edge.disk
      (sphereAdapted_X143.components.endOfHandle h b).1 :=
  sphereAdapted_X143.components.endDisk_eq h b

/-- Endpoints remain the labelled corners of this certificate's own rim charts. -/
theorem sphereCertificate_endpoint_label_X143 (h : Fin sphereAdapted_X143.edges.handleCount) (b :
  Bool) :
    sphereAdapted_X143.components.endOfHandle h b = sphereAdapted_X143.labelled.endOfCorner
      (sphereCertificate_X143.1.handleCorner h b) := by
  rw [← sphereAdapted_X143.components_eq]
  exact sphereAdapted_X143.labelled.endpoint_label h b

/-- The final vertex owner is the owner of the same horizontal registration. -/
theorem sphereCertificate_owner_X143 (h : Fin sphereAdapted_X143.edges.handleCount) (b : Bool) :
    sphereVertexLink_X143.index (sphereCertificate_X143.1.handleEnd h b) =
      sphereAdapted_X143.labelled.handleEndOwner h b :=
  sphereVertexLink_X143.index.apply_symm_apply _

theorem sphereCertificate_rimProduct_X143 : sphereCertificate_X143.1.RimProduct :=
  sphereCertificate_X143.2

theorem sphereCertificate_fibre_X143 : sphereCertificate_X143.1.EdgeCircleFibreCompatible :=
  strongCertificateOfAdapted_GFIN_edgeCircleFibreCompatible _ _ _

/-- The general producer retains two genuine interval handles. -/
theorem sphereCertificate_twoHandles_X143 : sphereCertificate_X143.1.handleCount = 2 := by
  have h := Fintype.card_congr sphereAdapted_X143.components.handleEquiv
  simp only [Fintype.card_fin] at h
  change sphereAdapted_X143.edges.handleCount = 2
  rw [h, spherePrepared_rows_X143]
  rfl

theorem sphereCertificate_zeroEdgeCircles_X143 : sphereCertificate_X143.1.edgeCircleCount = 0 := by
  have h := Fintype.card_congr sphereAdapted_X143.components.circleEquiv
  simp only [Fintype.card_fin] at h
  change sphereAdapted_X143.edges.edgeCircleCount = 0
  rw [h, spherePrepared_rows_X143]
  rfl

end GC.GraphManifold.Assembly.FC39P0.General_X143
