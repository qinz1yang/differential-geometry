import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GStrongAssembly
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereJointCertificate

/-!
# FC39 GROUP G, lane FC39-G-CVP: the S³ regression consumer

The general cover / vertical / protection lemmas and the general assembler applied to the one S³
configuration of review 49 on the WIDE prepared rows `spherePreparedW sphereJunctions`, with the safe
neighbourhoods `sphereSafe sphereJunctions`, the adapted package `sphereJointAdaptedEdgeRimData`, the
seam–face link `sphereSeamFacesLinkW` and the S³ handle-end, rim-region and arc layers:

* `sphere_cover_vertical_protection_GCVP` — the frozen target at the S³ data, by the general proof;
* `sphere_strongCertificateOfLayers_GCVP_eq` — the general assembler returns EXACTLY the S³ strong
  certificate `sphereStrongCertificate` of lane FC39-JOINT2 (same `ofLayers` output);
* non-vacuity: two actual handles, the rim product at both ends of the south handle, and the handle
  ends read from the actual horizontal labels, all through the general identity theorems.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

/-- The frozen target `stub_cover_vertical_protection` at the S³ data, by the general proof. -/
theorem sphere_cover_vertical_protection_GCVP :
    CoverLayer sphereW sphereVertexLayer sphereJointAdaptedEdgeRimData.edges
        sphereJointAdaptedEdgeRimData.circ ∧
      VerticalLayer sphereW sphereJointAdaptedEdgeRimData.edges sphereJointAdaptedEdgeRimData.circ ∧
      ProtectionLayer sphereW (BoundaryTori.empty sphereW) sphereJointAdaptedEdgeRimData.edges
        sphereJointAdaptedEdgeRimData.circ sphereSeamLayer sphereJointAdaptedEdgeRimData.rims :=
  cover_vertical_protection_GCVP (spherePreparedW sphereJunctions) (sphereSafe sphereJunctions)
    sphereJointAdaptedEdgeRimData sphereVertexLayer sphereVertexModelLinkW spherePortLayer
    sphereSeamLayer sphereFaceLayer sphereSeamFacesLinkW

/-- The general assembler at the S³ data. -/
def sphereStrongCertificate_GCVP : StrongCertificate sphereW (BoundaryTori.empty sphereW) :=
  strongCertificateOfLayers_GCVP (spherePreparedW sphereJunctions) (sphereSafe sphereJunctions)
    sphereJointAdaptedEdgeRimData sphereVertexLayer sphereVertexModelLinkW spherePortLayer
    sphereSeamLayer sphereFaceLayer sphereSeamFacesLinkW sphereHandleEndLayer sphereRimRegionLayer
    sphereArcLayer

/-- **Regression**: the general assembler returns exactly the S³ strong certificate of lane
FC39-JOINT2. -/
theorem sphere_strongCertificateOfLayers_GCVP_eq :
    sphereStrongCertificate_GCVP = sphereStrongCertificate :=
  rfl

/-- Non-vacuity: the assembled S³ certificate has two handles. -/
theorem sphereStrongCertificate_GCVP_handleCount : sphereStrongCertificate_GCVP.1.handleCount = 2 :=
  rfl

/-- The rim product at both ends of the south handle of the assembled S³ certificate. -/
theorem sphereStrongCertificate_GCVP_rimProductAt (b : Bool) :
    RimProductAt (sphereStrongCertificate_GCVP.1.rimChart (0 : Fin 2) b)
      (sphereStrongCertificate_GCVP.1.handle (0 : Fin 2)) b :=
  strongCertificateOfLayers_GCVP_rimProduct (spherePreparedW sphereJunctions)
    (sphereSafe sphereJunctions) sphereJointAdaptedEdgeRimData sphereVertexLayer
    sphereVertexModelLinkW spherePortLayer sphereSeamLayer sphereFaceLayer sphereSeamFacesLinkW
    sphereHandleEndLayer sphereRimRegionLayer sphereArcLayer (0 : Fin 2) b

/-- The handle ends of the assembled S³ certificate are read from the actual horizontal labels
(general owner identification). -/
theorem sphereStrongCertificate_GCVP_handleEnd (h : Fin 2) (b : Bool) :
    sphereVertexModelLinkW.index (sphereStrongCertificate_GCVP.1.handleEnd h b) =
      sphereJointAdaptedEdgeRimData.labelled.handleEndOwner h b :=
  strongCertificateOfLayers_GCVP_handleEnd_index (spherePreparedW sphereJunctions)
    (sphereSafe sphereJunctions) sphereJointAdaptedEdgeRimData sphereVertexLayer
    sphereVertexModelLinkW spherePortLayer sphereSeamLayer sphereFaceLayer sphereSeamFacesLinkW
    sphereHandleEndLayer sphereRimRegionLayer sphereArcLayer h b

/-- The handles of the assembled S³ certificate are whole inverse images of their components. -/
theorem sphereStrongCertificate_GCVP_handle_whole (h : Fin 2) :
    range (sphereStrongCertificate_GCVP.1.handle h).map =
      (spherePreparedW sphereJunctions).rows.edge.wholeComponent
        ((spherePreparedW sphereJunctions).rows.edgeModels.componentEquiv
          (.inl (sphereJointAdaptedEdgeRimData.labelled.edgeLink.handleEquiv h))) :=
  strongCertificateOfLayers_GCVP_handle_whole (spherePreparedW sphereJunctions)
    (sphereSafe sphereJunctions) sphereJointAdaptedEdgeRimData sphereVertexLayer
    sphereVertexModelLinkW spherePortLayer sphereSeamLayer sphereFaceLayer sphereSeamFacesLinkW
    sphereHandleEndLayer sphereRimRegionLayer sphereArcLayer h

/-- The existence form of the assembler at the S³ data. -/
theorem sphere_exists_strongCertificate_GCVP :
    Nonempty (StrongCertificate sphereW (BoundaryTori.empty sphereW)) :=
  exists_strongCertificate_of_layers_GCVP (spherePreparedW sphereJunctions)
    (sphereSafe sphereJunctions) sphereJointAdaptedEdgeRimData sphereVertexLayer
    sphereVertexModelLinkW spherePortLayer sphereSeamLayer sphereFaceLayer sphereSeamFacesLinkW
    sphereHandleEndLayer sphereRimRegionLayer sphereArcLayer

end GC.GraphManifold.Assembly.FC39P0
