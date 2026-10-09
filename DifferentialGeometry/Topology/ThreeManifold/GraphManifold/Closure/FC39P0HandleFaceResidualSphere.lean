import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0HandleFaceResidual
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereJointWide

/-!
# FC39 producer, GROUP G interface (review 56, D56-3): consumer on the S³ configuration

The general identification of `FC39P0HandleFaceResidual.lean` applied to the one S³ configuration
(wide prepared rows `spherePreparedW sphereJunctions`, adapted data
`sphereJointAdaptedEdgeRimData`, vertex link `sphereVertexModelLinkW`, seam–face link
`sphereSeamFacesLinkW`, handle-end layer `sphereHandleEndLayer` with two handles): for each of the
four handle ends, the hand-chosen end face `sphereLabelFace (edgeEndLabel (h, b))` of
`FC39P0SphereJointWide.lean` IS the actual residual face of the horizontal label, and it is the
unique catalogue index with the actual horizontal owner and that face — now DERIVED from the
general theorem, not read off the construction.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

/-- On S³: the end face of `(h, b)` is the actual residual face of the horizontal label. -/
theorem sphereLabelFace_face_eq_residualSet (h : Fin 2) (b : Bool) :
    sphereFaceLayer.face (sphereLabelFace (edgeEndLabel (h, b))) =
      (spherePreparedW sphereJunctions).rows.slim.residualSet
        ((spherePreparedW sphereJunctions).rows.junctions.horizontal
          (sphereJointAdaptedEdgeRimData.labelled.edgeLink.endOfHandle h b)) :=
  sphereJointAdaptedEdgeRimData.face_handleFace_eq_residualSet sphereVertexModelLinkW
    sphereSeamFacesLinkW sphereHandleEndLayer h b

/-- On S³: the end face of `(h, b)` is the UNIQUE catalogue index with the actual horizontal
owner and the residual face as its face. -/
theorem sphereLabelFace_existsUnique_residualSet (h : Fin 2) (b : Bool) :
    ∃! f : Fin sphereFaceLayer.faceCount,
      sphereVertexModelLinkW.index (sphereFaceLayer.faceOwner f) =
          sphereJointAdaptedEdgeRimData.labelled.handleEndOwner h b ∧
        sphereFaceLayer.face f = (spherePreparedW sphereJunctions).rows.slim.residualSet
          ((spherePreparedW sphereJunctions).rows.junctions.horizontal
            (sphereJointAdaptedEdgeRimData.labelled.edgeLink.endOfHandle h b)) :=
  sphereJointAdaptedEdgeRimData.existsUnique_face_residualSet sphereVertexModelLinkW
    sphereSeamFacesLinkW sphereHandleEndLayer h b

/-- On S³: any face index with the actual horizontal owner meeting the residual face is the
hand-chosen end face. -/
theorem eq_sphereLabelFace_of_meet (h : Fin 2) (b : Bool) {f : Fin sphereFaceLayer.faceCount}
    (hown : sphereVertexModelLinkW.index (sphereFaceLayer.faceOwner f) =
      sphereJointAdaptedEdgeRimData.labelled.handleEndOwner h b)
    (hmeet : (sphereFaceLayer.face f ∩ (spherePreparedW sphereJunctions).rows.slim.residualSet
      ((spherePreparedW sphereJunctions).rows.junctions.horizontal
        (sphereJointAdaptedEdgeRimData.labelled.edgeLink.endOfHandle h b))).Nonempty) :
    f = sphereLabelFace (edgeEndLabel (h, b)) :=
  sphereJointAdaptedEdgeRimData.eq_handleFace_of_meet sphereVertexModelLinkW sphereSeamFacesLinkW
    sphereHandleEndLayer h b hown hmeet

end GC.GraphManifold.Assembly.FC39P0
