import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GCVPSphereRegression
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GSphereHandleEndRim
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereGlobalFacesV2
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GHandleEndRimV2
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GStrongAssemblyV2
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0RegressionV2

/-!
# FC39 GROUP G over V2: the S³ consumers (D58-1, G1b regression)

Lane FC39-G-GFF(b). The V2 consumer theorems applied to the S³ V2 data of G1
(`spherePreparedV2_GGFF sphereJunctions`, `sphereJointAdaptedEdgeRimDataV2_GGFF` — the forgetful
images of the accepted S³ objects): every V2 output on S³ is the accepted V1 output (definitional
equalities through the forgetful maps — nothing re-proved on S³):

* `sphereHandleEndLayerV2_GGFF = sphereHandleEndLayer_GHR`, its owner equation, and the frozen V2
  handle-end target at S³;
* the V2 rim region on the hand-made layer `sphereHandleEndLayer` (owner equation
  `sphereHandleEnd_index`);
* `sphere_cover_vertical_protection_V2_GGFF`;
* `sphereStrongCertificateV2_GGFF = sphereStrongCertificate` (lane FC39-JOINT2's certificate) and its
  existence form;
* regression test C over V2 at S³ (`sphereRegressionCV2_GGFF`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

/-- **The V2 handle-end layer on the S³ data.** -/
def sphereHandleEndLayerV2_GGFF :
    HandleEndLayer sphereW sphereVertexLayer sphereJointAdaptedEdgeRimDataV2_GGFF.edges
      sphereFaceLayer :=
  sphereJointAdaptedEdgeRimDataV2_GGFF.handleEndLayer_GHR sphereVertexModelLinkW
    sphereSeamFacesLinkW

/-- **Regression**: the V2 handle-end layer on S³ IS the accepted general layer. -/
theorem sphereHandleEndLayerV2_GGFF_eq : sphereHandleEndLayerV2_GGFF = sphereHandleEndLayer_GHR :=
  rfl

/-- The owner equation of the V2 layer on S³ (the V2 theorem). -/
theorem sphereHandleEndLayerV2_GGFF_index (h : Fin 2) (b : Bool) :
    sphereVertexModelLinkW.index (sphereHandleEndLayerV2_GGFF.handleEnd h b) =
      sphereJointAdaptedEdgeRimDataV2_GGFF.labelled.handleEndOwner h b :=
  sphereJointAdaptedEdgeRimDataV2_GGFF.handleEndLayer_GHR_index sphereVertexModelLinkW
    sphereSeamFacesLinkW h b

/-- The end vertices of the V2 layer on S³ are the hand-made ones. -/
theorem sphereHandleEndLayerV2_GGFF_handleEnd (h : Fin 2) (b : Bool) :
    sphereHandleEndLayerV2_GGFF.handleEnd h b = sphereHandleEnd h b :=
  sphereHandleEndLayer_GHR_handleEnd h b

/-- The frozen V2 handle-end target at the S³ data. -/
theorem sphere_handleEndLayer_of_labelled_V2_GGFF :
    ∃ HE : HandleEndLayer sphereW sphereVertexLayer sphereJointAdaptedEdgeRimDataV2_GGFF.edges
        sphereFaceLayer,
      ∀ h b, sphereVertexModelLinkW.index (HE.handleEnd h b) =
        sphereJointAdaptedEdgeRimDataV2_GGFF.labelled.handleEndOwner h b :=
  handleEndLayer_of_labelled_GGFF (spherePreparedV2_GGFF sphereJunctions)
    (sphereSafe sphereJunctions) sphereJointAdaptedEdgeRimDataV2_GGFF sphereVertexLayer
    sphereVertexModelLinkW spherePortLayer sphereSeamLayer sphereFaceLayer sphereSeamFacesLinkW

/-- **The V2 rim region theorem on the hand-made S³ handle-end layer** (owner equation
`sphereHandleEnd_index`). -/
theorem sphereRimRegionLayerV2_GGFF :
    RimRegionLayer sphereW sphereVertexLayer sphereJointAdaptedEdgeRimDataV2_GGFF.edges
      sphereJointAdaptedEdgeRimDataV2_GGFF.circ sphereHandleEndLayer
      sphereJointAdaptedEdgeRimDataV2_GGFF.rims :=
  rimRegionLayer_of_labelled_GGFF (spherePreparedV2_GGFF sphereJunctions)
    (sphereSafe sphereJunctions) sphereJointAdaptedEdgeRimDataV2_GGFF sphereVertexLayer
    sphereVertexModelLinkW sphereHandleEndLayer sphereHandleEnd_index

/-- The V2 form of `stub_cover_vertical_protection` at the S³ data. -/
theorem sphere_cover_vertical_protection_V2_GGFF :
    CoverLayer sphereW sphereVertexLayer sphereJointAdaptedEdgeRimDataV2_GGFF.edges
        sphereJointAdaptedEdgeRimDataV2_GGFF.circ ∧
      VerticalLayer sphereW sphereJointAdaptedEdgeRimDataV2_GGFF.edges
        sphereJointAdaptedEdgeRimDataV2_GGFF.circ ∧
      ProtectionLayer sphereW (BoundaryTori.empty sphereW)
        sphereJointAdaptedEdgeRimDataV2_GGFF.edges sphereJointAdaptedEdgeRimDataV2_GGFF.circ
        sphereSeamLayer sphereJointAdaptedEdgeRimDataV2_GGFF.rims :=
  cover_vertical_protection_GGFF (spherePreparedV2_GGFF sphereJunctions)
    (sphereSafe sphereJunctions) sphereJointAdaptedEdgeRimDataV2_GGFF sphereVertexLayer
    sphereVertexModelLinkW spherePortLayer sphereSeamLayer sphereFaceLayer sphereSeamFacesLinkW

/-- **The V2 assembler at the S³ data.** -/
def sphereStrongCertificateV2_GGFF : StrongCertificate sphereW (BoundaryTori.empty sphereW) :=
  strongCertificateOfLayers_GGFF (spherePreparedV2_GGFF sphereJunctions)
    (sphereSafe sphereJunctions) sphereJointAdaptedEdgeRimDataV2_GGFF sphereVertexLayer
    sphereVertexModelLinkW spherePortLayer sphereSeamLayer sphereFaceLayer sphereSeamFacesLinkW
    sphereHandleEndLayer sphereRimRegionLayer sphereArcLayer

/-- **Regression**: the V2 assembler returns exactly the S³ strong certificate of FC39-JOINT2. -/
theorem sphereStrongCertificateV2_GGFF_eq : sphereStrongCertificateV2_GGFF = sphereStrongCertificate :=
  rfl

/-- Non-vacuity: the V2-assembled S³ certificate has two handles. -/
theorem sphereStrongCertificateV2_GGFF_handleCount :
    sphereStrongCertificateV2_GGFF.1.handleCount = 2 :=
  rfl

/-- The handle ends of the V2-assembled S³ certificate are read from the actual horizontal labels. -/
theorem sphereStrongCertificateV2_GGFF_handleEnd (h : Fin 2) (b : Bool) :
    sphereVertexModelLinkW.index (sphereStrongCertificateV2_GGFF.1.handleEnd h b) =
      sphereJointAdaptedEdgeRimDataV2_GGFF.labelled.handleEndOwner h b :=
  strongCertificateOfLayers_GGFF_handleEnd_index (spherePreparedV2_GGFF sphereJunctions)
    (sphereSafe sphereJunctions) sphereJointAdaptedEdgeRimDataV2_GGFF sphereVertexLayer
    sphereVertexModelLinkW spherePortLayer sphereSeamLayer sphereFaceLayer sphereSeamFacesLinkW
    sphereHandleEndLayer sphereRimRegionLayer sphereArcLayer h b

/-- The existence form of the V2 assembler at the S³ data. -/
theorem sphere_exists_strongCertificate_V2_GGFF :
    Nonempty (StrongCertificate sphereW (BoundaryTori.empty sphereW)) :=
  exists_strongCertificate_of_layers_GGFF (spherePreparedV2_GGFF sphereJunctions)
    (sphereSafe sphereJunctions) sphereJointAdaptedEdgeRimDataV2_GGFF sphereVertexLayer
    sphereVertexModelLinkW spherePortLayer sphereSeamLayer sphereFaceLayer sphereSeamFacesLinkW
    sphereHandleEndLayer sphereRimRegionLayer sphereArcLayer

/-- **Regression test C over V2 at S³**: the V2 contract rejects the swapped S³ data and projects to
the dry links. -/
theorem sphereRegressionCV2_GGFF (h : Fin 2) (b : Bool) :
    DryCircleLink sphereEdgeBundle sphereCircleBundle sphereCircleRegion ∧
      DryCircleLink sphereEdgeBundle sphereCircleBundle (swapAxesRegion sphereCircleRegion) ∧
      Nonempty (RimChartLayer sphereW sphereEdgeLayer (swapAxesRegion sphereCircleRegion)) ∧
      (¬ ∀ {p}, p ∈ (sphereRimLayer.swap.rimChart h b).source →
        (sphereRimLayer.swap.rimChart h b p ∈ sphereSlimPieces.rowSet
            ((sphereLabelledCompatibilityV2_GGFF sphereJunctions).handleEndOwner h b) ↔
          p.2.2 ≤ 0)) ∧
      IsEmpty (LabelledCornerCompatibilityV2 (spherePreparedV2_GGFF sphereJunctions)
        sphereEdgeLayer (swapAxesRegion sphereCircleRegion) sphereRimLayer.swap) :=
  regressionC_projected_GGFF sphereRimLayer (sphereLabelledCompatibilityV2_GGFF sphereJunctions)
    h b _ 1 (circRim_vertex_side sphereJunctions h b)

end GC.GraphManifold.Assembly.FC39P0
