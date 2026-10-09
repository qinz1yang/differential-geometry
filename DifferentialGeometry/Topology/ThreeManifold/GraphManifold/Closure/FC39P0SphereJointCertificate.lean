import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereJointArcs
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0Strong

/-!
# FC39 producer, packet P0 (gate 1): the NON-VACUOUS strong certificate of the one S³ configuration

The one S³ configuration of review 49 (T49-1): two zero pieces (`Z₋`, `Z₊`), one slim piece, two
handles, one sphere seam, on the WIDE prepared rows `spherePreparedW sphereJunctions` with the
adapted edge–rim data `sphereJointAdaptedEdgeRimData` (lane FC39-CIRC-C).

* `sphereJointCertificate` — `ofLayers` of the vertex, edge (`sphereEdgeLayer` = the adapted edge
  layer, two handles), circle (`sphereCircleRegion`), port, seam, face, handle-end, rim-chart
  (`sphereRimLayer`), arc, cover, vertical, rim-region and protection layers;
* **`sphereStrongCertificate : StrongCertificate sphereW (BoundaryTori.empty sphereW)`** — the rim
  product holds at every rim (`ofLayers_rimProduct_iff` + `sphereRimLayer_rimProduct`, lane FC39-CIRC-B);
  it has two actual handles (`sphereStrongCertificate_handleCount`, regression test A of review 49:
  the zero-handle strong certificate does not count);
* the stub-shaped instances of the assembly targets (`Targets.lean`) on the adapted data: handle ends
  by the SAME horizontal labels (`sphere_handleEndLayer_of_labelled`), the rim region
  (`sphere_rimRegionLayer_of_labelled`), the arc layer, cover / vertical / protection, and the
  certificate's layers ARE the adapted data's (`sphereStrongCertificate_circ` …);
* consumers: the closed wrapper and the interior hint of the strong certificate.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

/-! ## The certificate -/

/-- **The decomposition certificate of the one S³ configuration**, reassembled from its layers. -/
def sphereJointCertificate : DecompositionCertificate sphereW (BoundaryTori.empty sphereW) :=
  ofLayers sphereVertexLayer sphereEdgeLayer sphereCircleRegion spherePortLayer sphereSeamLayer
    sphereFaceLayer sphereHandleEndLayer sphereRimLayer sphereArcLayer sphereCoverLayer
    sphereVerticalLayer sphereRimRegionLayer sphereProtectionLayer

/-- The rim-product clause of the S³ certificate (every rim of both handles). -/
theorem sphereJointCertificate_rimProduct : sphereJointCertificate.RimProduct :=
  ofLayers_rimProduct_iff.2 sphereRimLayer_rimProduct

/-- **The strong certificate of the one S³ configuration.** -/
def sphereStrongCertificate : StrongCertificate sphereW (BoundaryTori.empty sphereW) :=
  ⟨sphereJointCertificate, sphereJointCertificate_rimProduct⟩

/-! ## Non-vacuity (regression test A of review 49) -/

/-- The S³ strong certificate has TWO handles. -/
theorem sphereStrongCertificate_handleCount : sphereStrongCertificate.1.handleCount = 2 :=
  rfl

/-- An actual handle of the S³ strong certificate (the south polar handle). -/
def sphereStrongCertificate_southHandle : Fin sphereStrongCertificate.1.handleCount :=
  (0 : Fin 2)

theorem sphereStrongCertificate_southHandle_eq :
    sphereStrongCertificate.1.handle sphereStrongCertificate_southHandle = cycleS3Handle false :=
  rfl

/-- The rim product at both ends of the actual south handle. -/
theorem sphereStrongCertificate_rimProductAt (b : Bool) :
    RimProductAt (sphereStrongCertificate.1.rimChart sphereStrongCertificate_southHandle b)
      (sphereStrongCertificate.1.handle sphereStrongCertificate_southHandle) b :=
  sphereStrongCertificate.2 sphereStrongCertificate_southHandle b

/-- The S³ strong certificate has four corners and two arcs, no loop, three vertices, four faces
and one sphere seam. -/
theorem sphereStrongCertificate_counts :
    sphereStrongCertificate.1.circ.cornerCount = 4 ∧ sphereStrongCertificate.1.arcFaceCount = 2 ∧
      sphereStrongCertificate.1.loopFaceCount = 0 ∧ sphereStrongCertificate.1.vertexCount = 3 ∧
      sphereStrongCertificate.1.faceCount = 4 ∧ sphereStrongCertificate.1.sphereSeamCount = 1 :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The certificate is built on the wide rows and the adapted edge–rim data -/

theorem sphereStrongCertificate_circ :
    sphereStrongCertificate.1.circ = sphereJointAdaptedEdgeRimData.circ :=
  rfl

theorem sphereStrongCertificate_handle (h : Fin 2) :
    sphereStrongCertificate.1.handle h = sphereJointAdaptedEdgeRimData.edges.handle h :=
  rfl

theorem sphereStrongCertificate_rimChart (h : Fin 2) (b : Bool) :
    sphereStrongCertificate.1.rimChart h b = sphereJointAdaptedEdgeRimData.rims.rimChart h b :=
  rfl

theorem sphereStrongCertificate_handleCorner (h : Fin 2) (b : Bool) :
    sphereStrongCertificate.1.handleCorner h b = sphereJointAdaptedEdgeRimData.rims.handleCorner h b :=
  rfl

theorem sphereStrongCertificate_vertex (k : Fin 3) :
    sphereStrongCertificate.1.vertex k =
      (spherePreparedW sphereJunctions).rows.rowVertex (sphereVertexModelLinkW.index k) :=
  sphereVertexModelLinkW.vertex_eq k

/-- **The handle ends of the certificate are read from the SAME actual horizontal labels.** -/
theorem sphereStrongCertificate_handleEnd (h : Fin 2) (b : Bool) :
    sphereVertexModelLinkW.index (sphereStrongCertificate.1.handleEnd h b) =
      sphereJointAdaptedEdgeRimData.labelled.handleEndOwner h b :=
  sphereHandleEnd_index h b

/-! ## The stub-shaped instances on the adapted data -/

/-- Instance of `stub_handleEndLayer_of_labelled` (new S9) on the S³ data. -/
theorem sphere_handleEndLayer_of_labelled :
    ∃ HE : HandleEndLayer sphereW sphereVertexLayer sphereJointAdaptedEdgeRimData.edges
        sphereFaceLayer,
      ∀ h b, sphereVertexModelLinkW.index (HE.handleEnd h b) =
        sphereJointAdaptedEdgeRimData.labelled.handleEndOwner h b :=
  ⟨sphereHandleEndLayer, sphereHandleEnd_index⟩

/-- Instance of `stub_rimRegionLayer_of_labelled` (new S11b) on the S³ data. -/
theorem sphere_rimRegionLayer_of_labelled :
    RimRegionLayer sphereW sphereVertexLayer sphereJointAdaptedEdgeRimData.edges
      sphereJointAdaptedEdgeRimData.circ sphereHandleEndLayer sphereJointAdaptedEdgeRimData.rims :=
  sphereRimRegionLayer

/-- Instance of `stub_exists_arcLayer` (P9) on the S³ data. -/
theorem sphere_exists_arcLayer :
    Nonempty (ArcLayer sphereW sphereJointAdaptedEdgeRimData.edges sphereJointAdaptedEdgeRimData.circ
      sphereFaceLayer sphereHandleEndLayer sphereJointAdaptedEdgeRimData.rims) :=
  ⟨sphereArcLayer⟩

/-- Instance of `stub_cover_vertical_protection` (P10) on the S³ data. -/
theorem sphere_cover_vertical_protection :
    CoverLayer sphereW sphereVertexLayer sphereJointAdaptedEdgeRimData.edges
        sphereJointAdaptedEdgeRimData.circ ∧
      VerticalLayer sphereW sphereJointAdaptedEdgeRimData.edges sphereJointAdaptedEdgeRimData.circ ∧
      ProtectionLayer sphereW (BoundaryTori.empty sphereW) sphereJointAdaptedEdgeRimData.edges
        sphereJointAdaptedEdgeRimData.circ sphereSeamLayer sphereJointAdaptedEdgeRimData.rims :=
  ⟨sphereCoverLayer, sphereVerticalLayer, sphereProtectionLayer⟩

/-- Instance of `stub_exists_strongCertificate` (P11) on the wide S³ prepared rows. -/
theorem sphere_exists_strongCertificate :
    Nonempty (StrongCertificate sphereW (BoundaryTori.empty sphereW)) :=
  ⟨sphereStrongCertificate⟩

/-! ## Consumers -/

/-- The closed strong certificate of the S³ configuration (the proof of the rim product is kept). -/
def sphereStrongClosedCertificate : StrongClosedCertificate sphereW :=
  sphereStrongCertificate.toClosed

theorem sphereStrongClosedCertificate_rimProduct :
    sphereStrongClosedCertificate.toClosedCertificate.cert.RimProduct :=
  sphereStrongClosedCertificate.rimProduct

/-- The interior hint of the S³ strong certificate (derived, no new field). -/
theorem sphereStrongCertificate_hint :
    ∀ k, (sphereStrongCertificate.1.vertex k).IsBall →
      (sphereStrongCertificate.1.vertex k).image ⊆ (sphereW.interior : Set sphereW.Carrier) :=
  sphereStrongCertificate.hint

end GC.GraphManifold.Assembly.FC39P0
