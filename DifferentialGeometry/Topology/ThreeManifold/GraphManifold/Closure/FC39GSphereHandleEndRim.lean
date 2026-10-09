import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GHandleEndRim
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0HandleFaceResidualSphere

/-!
# FC39 GROUP G, handle ends and rim region: consumer on the S³ configuration (lane FC39-G-HE-RIM)

The general theorems of `FC39GHandleEndRim.lean` applied to the one S³ configuration (wide prepared
rows `spherePreparedW sphereJunctions`, safe neighbourhoods `sphereSafe sphereJunctions`, adapted
data `sphereJointAdaptedEdgeRimData` with two handles, vertex link `sphereVertexModelLinkW`, port
layer `spherePortLayer`, seam layer `sphereSeamLayer`, face layer `sphereFaceLayer`, seam–face link
`sphereSeamFacesLinkW`):

* `sphereHandleEndLayer_GHR` — the GENERAL handle-end layer on the S³ data; its end vertices and end
  faces are those of the hand-made `sphereHandleEndLayer` of `FC39P0SphereJointWide.lean`
  (`sphereHandleEndLayer_GHR_handleEnd`, `sphereHandleEndLayer_GHR_handleFace`: the face from the
  uniqueness of the residual-face catalogue index, not by unfolding);
* `sphere_handleEndLayer_rimRegionLayer_GHR` — the chain `HE → RimRegionLayer` on the SAME adapted
  data and the SAME `HE`, from the general theorems;
* `sphereRimRegionLayer_GHR` — the general rim region theorem on the hand-made
  `sphereHandleEndLayer` with its owner equation `sphereHandleEnd_index`;
* non-vacuity: two handles, four handle ends, every end face partitioned with the residual face as
  its face (`sphereHandleEndLayer_GHR_kind`, `sphereHandleEndLayer_GHR_face`).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

/-- **The general handle-end layer on the S³ data.** -/
def sphereHandleEndLayer_GHR :
    HandleEndLayer sphereW sphereVertexLayer sphereJointAdaptedEdgeRimData.edges sphereFaceLayer :=
  sphereJointAdaptedEdgeRimData.handleEndLayer_GHR sphereVertexModelLinkW sphereSeamFacesLinkW

/-- The frozen handle-end target, applied to the S³ data. -/
theorem sphere_handleEndLayer_of_labelled_GHR :
    ∃ HE : HandleEndLayer sphereW sphereVertexLayer sphereJointAdaptedEdgeRimData.edges
        sphereFaceLayer,
      ∀ h b, sphereVertexModelLinkW.index (HE.handleEnd h b) =
        sphereJointAdaptedEdgeRimData.labelled.handleEndOwner h b :=
  handleEndLayer_of_labelled (spherePreparedW sphereJunctions) (sphereSafe sphereJunctions)
    sphereJointAdaptedEdgeRimData sphereVertexLayer sphereVertexModelLinkW spherePortLayer
    sphereSeamLayer sphereFaceLayer sphereSeamFacesLinkW

/-- The owner equation of the general layer on S³. -/
theorem sphereHandleEndLayer_GHR_index (h : Fin 2) (b : Bool) :
    sphereVertexModelLinkW.index (sphereHandleEndLayer_GHR.handleEnd h b) =
      sphereJointAdaptedEdgeRimData.labelled.handleEndOwner h b :=
  sphereJointAdaptedEdgeRimData.handleEndLayer_GHR_index sphereVertexModelLinkW
    sphereSeamFacesLinkW h b

/-- **Regression: the general end vertices are the hand-made ones.** -/
theorem sphereHandleEndLayer_GHR_handleEnd (h : Fin 2) (b : Bool) :
    sphereHandleEndLayer_GHR.handleEnd h b = sphereHandleEnd h b :=
  sphereVertexModelLinkW.index.injective
    ((sphereHandleEndLayer_GHR_index h b).trans (sphereHandleEnd_index h b).symm)

/-- The end face of the general layer on S³ is the actual residual face of the label. -/
theorem sphereHandleEndLayer_GHR_face (h : Fin 2) (b : Bool) :
    sphereFaceLayer.face (sphereHandleEndLayer_GHR.handleFace h b) =
      (spherePreparedW sphereJunctions).rows.slim.residualSet
        ((spherePreparedW sphereJunctions).rows.junctions.horizontal
          (sphereJointAdaptedEdgeRimData.labelled.edgeLink.endOfHandle h b)) :=
  sphereJointAdaptedEdgeRimData.handleEndLayer_GHR_face sphereVertexModelLinkW
    sphereSeamFacesLinkW h b

/-- The end face of the general layer on S³ is partitioned. -/
theorem sphereHandleEndLayer_GHR_kind (h : Fin 2) (b : Bool) :
    sphereFaceLayer.faceKind (sphereHandleEndLayer_GHR.handleFace h b) = .partitioned :=
  sphereHandleEndLayer_GHR.handleFace_kind h b

/-- **Regression: the general end faces are the hand-made ones** (uniqueness of the catalogue index
of the residual face). -/
theorem sphereHandleEndLayer_GHR_handleFace (h : Fin 2) (b : Bool) :
    sphereHandleEndLayer_GHR.handleFace h b = sphereLabelFace (edgeEndLabel (h, b)) := by
  refine (sphereLabelFace_existsUnique_residualSet h b).unique ?_ ?_
  · exact ⟨(congrArg sphereVertexModelLinkW.index
      (sphereHandleEndLayer_GHR.handleFace_owner h b)).trans (sphereHandleEndLayer_GHR_index h b),
      sphereHandleEndLayer_GHR_face h b⟩
  · refine ⟨?_, sphereLabelFace_face_eq_residualSet h b⟩
    rw [← sphereHandleEnd_eq]
    exact sphereHandleEnd_index h b

/-- **The chain `HE → RimRegionLayer` on the S³ data**, on the SAME adapted data and the SAME `HE`
(from the general theorems). -/
theorem sphere_handleEndLayer_rimRegionLayer_GHR :
    ∃ HE : HandleEndLayer sphereW sphereVertexLayer sphereJointAdaptedEdgeRimData.edges
        sphereFaceLayer,
      (∀ h b, sphereVertexModelLinkW.index (HE.handleEnd h b) =
        sphereJointAdaptedEdgeRimData.labelled.handleEndOwner h b) ∧
        RimRegionLayer sphereW sphereVertexLayer sphereJointAdaptedEdgeRimData.edges
          sphereJointAdaptedEdgeRimData.circ HE sphereJointAdaptedEdgeRimData.rims :=
  exists_handleEndLayer_rimRegionLayer_GHR (spherePreparedW sphereJunctions)
    (sphereSafe sphereJunctions) sphereJointAdaptedEdgeRimData sphereVertexLayer
    sphereVertexModelLinkW spherePortLayer sphereSeamLayer sphereFaceLayer sphereSeamFacesLinkW

/-- The rim region of the general layer on S³ (frozen rim target, owner equation of the output). -/
theorem sphereRimRegionLayer_of_GHR :
    RimRegionLayer sphereW sphereVertexLayer sphereJointAdaptedEdgeRimData.edges
      sphereJointAdaptedEdgeRimData.circ sphereHandleEndLayer_GHR
      sphereJointAdaptedEdgeRimData.rims :=
  rimRegionLayer_of_labelled (spherePreparedW sphereJunctions) (sphereSafe sphereJunctions)
    sphereJointAdaptedEdgeRimData sphereVertexLayer sphereVertexModelLinkW sphereHandleEndLayer_GHR
    sphereHandleEndLayer_GHR_index

/-- **The general rim region theorem on the hand-made handle-end layer** (owner equation
`sphereHandleEnd_index`): it reproduces `sphereRimRegionLayer`. -/
theorem sphereRimRegionLayer_GHR :
    RimRegionLayer sphereW sphereVertexLayer sphereJointAdaptedEdgeRimData.edges
      sphereJointAdaptedEdgeRimData.circ sphereHandleEndLayer sphereJointAdaptedEdgeRimData.rims :=
  rimRegionLayer_of_labelled (spherePreparedW sphereJunctions) (sphereSafe sphereJunctions)
    sphereJointAdaptedEdgeRimData sphereVertexLayer sphereVertexModelLinkW sphereHandleEndLayer
    sphereHandleEnd_index

/-- Non-vacuity: the S³ adapted data has two handles, hence four handle ends. -/
theorem sphereHandleEndLayer_GHR_handleCount :
    sphereJointAdaptedEdgeRimData.edges.handleCount = 2 :=
  rfl

end GC.GraphManifold.Assembly.FC39P0
