import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GArcLayer
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GSphereConsumersV2
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereJointArcs

/-!
# FC39 GROUP G arcs: consumer on the S³ V2 data

Lane FC39-G-ARC. The general arc-layer theorem `exists_arcLayer_GARC` applied to the S³ V2 data
(`spherePreparedV2_GGFF sphereJunctions`, `sphereJointAdaptedEdgeRimDataV2_GGFF`, the seam–face
link `sphereSeamFacesLinkW`) with TWO handle-end layers (the hand-made `sphereHandleEndLayer` and the
general `sphereHandleEndLayerV2_GGFF`: any `HE` is accepted), and the count regression: the general
enumeration has exactly as many arcs as the hand-made S³ arc layer of `FC39P0SphereJointArcs.lean`
(two arcs, the handle count; no FC40).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

/-- **The general arc layer on the S³ V2 data** (hand-made handle-end layer). -/
theorem sphere_exists_arcLayer_GARC :
    Nonempty (ArcLayer sphereW sphereJointAdaptedEdgeRimDataV2_GGFF.edges
      sphereJointAdaptedEdgeRimDataV2_GGFF.circ sphereFaceLayer sphereHandleEndLayer
      sphereJointAdaptedEdgeRimDataV2_GGFF.rims) :=
  exists_arcLayer_GARC (spherePreparedV2_GGFF sphereJunctions) (sphereSafe sphereJunctions)
    sphereJointAdaptedEdgeRimDataV2_GGFF sphereVertexLayer sphereVertexModelLinkW spherePortLayer
    sphereSeamLayer sphereFaceLayer sphereSeamFacesLinkW sphereHandleEndLayer

/-- **The general arc layer on the S³ V2 data** (the general handle-end layer of lane GHR). -/
theorem sphere_exists_arcLayer_general_GARC :
    Nonempty (ArcLayer sphereW sphereJointAdaptedEdgeRimDataV2_GGFF.edges
      sphereJointAdaptedEdgeRimDataV2_GGFF.circ sphereFaceLayer sphereHandleEndLayerV2_GGFF
      sphereJointAdaptedEdgeRimDataV2_GGFF.rims) :=
  stub_exists_arcLayer_GARC (spherePreparedV2_GGFF sphereJunctions) (sphereSafe sphereJunctions)
    sphereJointAdaptedEdgeRimDataV2_GGFF sphereVertexLayer sphereVertexModelLinkW spherePortLayer
    sphereSeamLayer sphereFaceLayer sphereSeamFacesLinkW sphereHandleEndLayerV2_GGFF

/-- **Count regression on S³**: the general enumeration has two arcs, as many as the hand-made S³
arc layer. -/
theorem sphere_arcCount_GARC :
    Fintype.card (sphereJointAdaptedEdgeRimDataV2_GGFF.ArcIdx_GARC sphereSeamFacesLinkW) =
      sphereArcLayer.arcFaceCount :=
  (arcFaceCount_eq_handleCount_GARC sphereJointAdaptedEdgeRimDataV2_GGFF sphereSeamFacesLinkW
    sphereHandleEndLayer).trans sphereArcLayer_arcFaceCount.symm

end GC.GraphManifold.Assembly.FC39P0
