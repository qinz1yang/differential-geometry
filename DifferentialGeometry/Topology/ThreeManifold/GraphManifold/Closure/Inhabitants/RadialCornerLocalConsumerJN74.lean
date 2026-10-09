import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.RadialStageGeomJN74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39StageCornerLocalJN74

/-!
# Draft 74, G7 consumer: the structural corner lemmas on the radial solid torus

Lane S-JUNCTIONS2 (suffix `_JN74`). `CircleBundle.isOpenMap_proj_JN74` on the X135 circle bundle,
`SlimPiecesV2.vertexSide_JN74` on the X135 slim pieces at their (one) new face (the slim band is the
vertex owner of the face `h = -1/2`: `x ∈ band ↔ -(1/2) - h x ≤ 0` near the face), and
`exists_cornerCutFacts_JN74` on the radial rows (no endpoint, so the per-endpoint data are
vacuous). The per-endpoint lemma `exists_cornerRank_descended_of_local_JN74` is exercised by the
endpoint-bearing instances (S-SOLIDTORUS2, the S³ four-corner).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0.X135Radial

local instance radialEdgeEndEmpty_CornerConsumerJN74 : IsEmpty radialRows74.edge.EdgeEnd :=
  radialEdgeEnd_isEmpty74

/-- The X135 circle projection is an open map. -/
theorem radialCircleProj_isOpenMap74 : IsOpenMap radialCircleBundle.proj :=
  radialCircleBundle.isOpenMap_proj_JN74

/-- The vertex side of the sign model at the new slim face of the radial solid torus. -/
theorem radialVertexSide74 {x : carrier.Carrier}
    (hx : x ∈ radialSlims.residualNear radialResidualFace) :
    x ∈ radialSlims.rowSet (radialSlims.residualOwner radialResidualFace) ↔
      radialSlims.residualFn radialResidualFace x ≤ 0 :=
  SlimPiecesV2.vertexSide_JN74 (S := radialSlims) (F := radialResidualFace) hx

/-- The corner facts of the radial rows through the all-endpoint assembly (vacuous). -/
theorem radialCornerFacts74_nonempty : Nonempty (CornerCutFacts74 radialFaces74 radialRims74) :=
  exists_cornerCutFacts_JN74 (fun e => isEmptyElim e) (fun e => isEmptyElim e)

end GC.GraphManifold.Assembly.FC39P0.X135Radial
