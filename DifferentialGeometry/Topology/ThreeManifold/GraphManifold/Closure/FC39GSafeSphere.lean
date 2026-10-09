import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GSafeNeighbourhoods
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereCornersAdapted

/-!
# FC39 GROUP G (lane FC39-G-SAFE): the S³ regression of the safe neighbourhoods

The general theorem `exists_safeNeighbourhoods_GSAFE` and its public lemmas applied to the S³
rows `(spherePreparedW sphereJunctions).rows` (the wide rows of the non-vacuous strong
certificate). Non-vacuity: the S³ rows have FOUR endpoints with four distinct rim base points (so
`corner_closure_disjoint` is a real clause), and a shared face, which the general S2 lemma keeps off
the edge piece and the circle region.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

/-- The general safe neighbourhoods of the S³ rows of the strong certificate. -/
theorem sphere_safeNeighbourhoods_GSAFE :
    Nonempty (ProducerSafeNeighbourhoods (spherePreparedW sphereJunctions).rows) :=
  exists_safeNeighbourhoods_GSAFE _

/-- **Non-vacuity of the corner clauses**: the S³ rows have four endpoints. -/
theorem sphere_edgeEnd_card_GSAFE :
    Nat.card (spherePreparedW sphereJunctions).rows.edge.EdgeEnd = 4 := by
  rw [← Nat.card_congr (spherePreparedW sphereJunctions).rows.edgeModels.endpointEquiv]
  change Nat.card (Fin 2 × Bool) = 4
  simp

/-- The four rim base points of the S³ endpoints are pairwise distinct (general S5). -/
theorem sphere_rimBase_injective_GSAFE :
    Injective fun e : (spherePreparedW sphereJunctions).rows.edge.EdgeEnd =>
      (spherePreparedW sphereJunctions).rows.junctions.rimBase e.1 :=
  FC39RowsV2.rimBase_injective_GSAFE _

/-- **Non-vacuity of the shared clauses**: the S³ shared face avoids the edge piece (general S2). -/
theorem sphere_sharedSet_disjoint_edgePiece_GSAFE :
    Disjoint ((spherePreparedW sphereJunctions).rows.sharedSet sphereSharedFace)
      (spherePreparedW sphereJunctions).rows.edge.edgePiece :=
  FC39RowsV2.sharedSet_disjoint_edgePiece_GSAFE (spherePreparedW sphereJunctions).rows
    sphereSharedFace

/-- The S³ shared face avoids the circle region (general S2). -/
theorem sphere_sharedSet_disjoint_region_GSAFE :
    Disjoint ((spherePreparedW sphereJunctions).rows.sharedSet sphereSharedFace)
      (spherePreparedW sphereJunctions).rows.circle.region :=
  FC39RowsV2.sharedSet_disjoint_region_GSAFE (spherePreparedW sphereJunctions).rows
    sphereSharedFace

end GC.GraphManifold.Assembly.FC39P0
