import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GFinalAssembly
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GSphereConsumersV2

/-!
# FC39 GROUP G final assembly: the S³ regression (lane FC39-G-FINAL)

The data form of the final assembly (`FC39GFinalAssembly.lean`) with its four remaining inputs
instantiated by the existing S³ constructions —

* global face functions V2: `sphereGlobalFacesV2_GGFF sphereJunctions`,
* adapted edge–rim data V2: `sphereJointAdaptedEdgeRimDataV2_GGFF`,
* seams / faces: `sphereSeamLayer`, `sphereFaceLayer`, `sphereSeamFacesLinkW`,
* arc layer: `sphereArcLayer` —

on the S³ rows `sphereRowsW sphereJunctions` with the S³ safe neighbourhoods, vertex link and port
layer:

* `sphereStrongCertificateOfRemaining_GFIN_eq` — with the hand-made handle-end layer
  `sphereHandleEndLayer` the result IS `sphereStrongCertificate` (**definitional**, `rfl`);
* `sphereHandleEndLayer_eq_GFIN` — the hand-made layer equals the layer computed from the labels
  (`handleEndLayer_GHR`; **propositional**, from the end vertices and the uniqueness of the
  residual-face catalogue index);
* `sphereStrongCertificateOfRemainingLabelled_GFIN_eq` — with the handle-end layer COMPUTED from the
  labels and `sphereArcLayer` transported along that equality, the result equals
  `sphereStrongCertificate` (**propositional**);
* non-vacuity: two handles; the existence form.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

/-- Two handle-end layers with the same end vertices and the same end faces are equal (the other
fields are propositions). -/
theorem HandleEndLayer.ext_GFIN {W : CompactCarrier.{u}} {n : ℕ} {E : BoundaryTori W n}
    {V : VertexLayer W} {H : EdgeLayer W} {circ : CircleRegion W} {S : SeamLayer W V circ}
    {O : PortLayer W E V} {F : FaceLayer W E V S O} {HE HE' : HandleEndLayer W V H F}
    (hEnd : HE.handleEnd = HE'.handleEnd) (hFace : HE.handleFace = HE'.handleFace) : HE = HE' := by
  cases HE
  cases HE'
  cases hEnd
  cases hFace
  rfl

/-- **The data form of the final assembly on the S³ constructions** (hand-made handle-end layer,
owner equation `sphereHandleEnd_index`). -/
def sphereStrongCertificateOfRemaining_GFIN :
    StrongCertificate sphereW (BoundaryTori.empty sphereW) :=
  strongCertificateOfRemaining_GFIN (sphereRowsW sphereJunctions)
    (sphereGlobalFacesV2_GGFF sphereJunctions) (sphereSafe sphereJunctions) sphereVertexLayer
    sphereVertexModelLinkW spherePortLayer sphereJointAdaptedEdgeRimDataV2_GGFF sphereSeamLayer
    sphereFaceLayer sphereSeamFacesLinkW sphereHandleEndLayer sphereHandleEnd_index sphereArcLayer

/-- **Regression (definitional)**: the final assembly on the S³ constructions returns exactly the
S³ strong certificate of FC39-JOINT2. -/
theorem sphereStrongCertificateOfRemaining_GFIN_eq :
    sphereStrongCertificateOfRemaining_GFIN = sphereStrongCertificate :=
  rfl

/-- The S³ handle-end layer computed from the labels by the general construction (V2). -/
theorem sphereHandleEndLayerV2_GFIN_eq :
    sphereJointAdaptedEdgeRimDataV2_GGFF.handleEndLayer_GHR sphereVertexModelLinkW
      sphereSeamFacesLinkW = sphereHandleEndLayer_GHR :=
  rfl

/-- **The hand-made S³ handle-end layer IS the layer computed from the labels** (propositional:
same end vertices, `sphereHandleEndLayer_GHR_handleEnd`; same end faces by the uniqueness of the
residual-face catalogue index, `sphereHandleEndLayer_GHR_handleFace`). -/
theorem sphereHandleEndLayer_eq_GFIN :
    sphereHandleEndLayer =
      sphereJointAdaptedEdgeRimDataV2_GGFF.handleEndLayer_GHR sphereVertexModelLinkW
        sphereSeamFacesLinkW :=
  HandleEndLayer.ext_GFIN
    (funext fun h => funext fun b => (sphereHandleEndLayer_GHR_handleEnd h b).symm)
    (funext fun h => funext fun b => (sphereHandleEndLayer_GHR_handleFace h b).symm)

/-- **The final assembly on S³ with the handle-end layer computed from the labels**; the S³ arc
layer is transported along `sphereHandleEndLayer_eq_GFIN`. -/
def sphereStrongCertificateOfRemainingLabelled_GFIN :
    StrongCertificate sphereW (BoundaryTori.empty sphereW) :=
  strongCertificateOfRemainingLabelled_GFIN (sphereRowsW sphereJunctions)
    (sphereGlobalFacesV2_GGFF sphereJunctions) (sphereSafe sphereJunctions) sphereVertexLayer
    sphereVertexModelLinkW spherePortLayer sphereJointAdaptedEdgeRimDataV2_GGFF sphereSeamLayer
    sphereFaceLayer sphereSeamFacesLinkW (sphereHandleEndLayer_eq_GFIN ▸ sphereArcLayer)

/-- **Regression (propositional)**: with the handle-end layer computed from the labels, the final
assembly on S³ still returns the S³ strong certificate of FC39-JOINT2. -/
theorem sphereStrongCertificateOfRemainingLabelled_GFIN_eq :
    sphereStrongCertificateOfRemainingLabelled_GFIN = sphereStrongCertificate :=
  (strongCertificateOfRemaining_GFIN_congr (sphereRowsW sphereJunctions)
    (sphereGlobalFacesV2_GGFF sphereJunctions) (sphereSafe sphereJunctions) sphereVertexLayer
    sphereVertexModelLinkW spherePortLayer sphereJointAdaptedEdgeRimDataV2_GGFF sphereSeamLayer
    sphereFaceLayer sphereSeamFacesLinkW sphereHandleEndLayer_eq_GFIN sphereHandleEnd_index
    (sphereJointAdaptedEdgeRimDataV2_GGFF.handleEndLayer_GHR_index sphereVertexModelLinkW
      sphereSeamFacesLinkW) sphereArcLayer).trans sphereStrongCertificateOfRemaining_GFIN_eq

/-- Non-vacuity: the S³ final assembly has two handles. -/
theorem sphereStrongCertificateOfRemaining_GFIN_handleCount :
    sphereStrongCertificateOfRemaining_GFIN.1.handleCount = 2 :=
  rfl

/-- The handle ends of the S³ final assembly are read from the actual horizontal labels. -/
theorem sphereStrongCertificateOfRemaining_GFIN_handleEnd (h : Fin 2) (b : Bool) :
    sphereVertexModelLinkW.index (sphereStrongCertificateOfRemaining_GFIN.1.handleEnd h b) =
      sphereJointAdaptedEdgeRimDataV2_GGFF.labelled.handleEndOwner h b :=
  strongCertificateOfRemaining_GFIN_handleEnd_index (sphereRowsW sphereJunctions)
    (sphereGlobalFacesV2_GGFF sphereJunctions) (sphereSafe sphereJunctions) sphereVertexLayer
    sphereVertexModelLinkW spherePortLayer sphereJointAdaptedEdgeRimDataV2_GGFF sphereSeamLayer
    sphereFaceLayer sphereSeamFacesLinkW sphereHandleEndLayer sphereHandleEnd_index sphereArcLayer
    h b

/-- The existence form of the final assembly on S³. -/
theorem sphere_exists_strongCertificate_GFIN :
    Nonempty (StrongCertificate sphereW (BoundaryTori.empty sphereW)) :=
  ⟨sphereStrongCertificateOfRemainingLabelled_GFIN⟩

end GC.GraphManifold.Assembly.FC39P0
