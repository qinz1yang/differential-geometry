import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GComponentEquiv
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39GVertexPortLayers
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39P0SphereJointWide

/-!
# FC39 GROUP G (lane FC39-G1): the S³ regression of the three general theorems

The general theorems `totalComponentEquiv_G1`, `exists_vertexLayer_G1`, `exists_portLayer_G1`
applied to the S³ rows (the wide prepared rows `(spherePreparedW sphereJunctions).rows` of the
non-vacuous strong certificate, and their edge data `sphereEdgeBundle`, `sphereEdgeModels`):

* the edge piece of S³ has exactly TWO actual components (`sphere_edgeActualComponent_card_G1`),
  the component of the label `inl i` being the range of the polar handle `intervalTriv i`;
* every vertex link of the S³ rows has three vertices, the generic vertex layer has the same
  vertex `0` (the inner ball `Z₋`) as the hand-built `sphereVertexLayer`;
* the generic port layer over the hand-built vertex layer and link IS `spherePortLayer`.
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.Seifert GC.GraphManifold
open Manifold
open scoped Manifold ContDiff Topology

namespace GC.GraphManifold.Assembly.FC39P0

/-! ## Actual components of the S³ edge piece -/

/-- `totalComponentEquiv_G1` on the S³ edge data. -/
theorem sphereTotalComponentEquiv_G1 :
    ∃ e : (Fin sphereEdgeModels.intervalCount ⊕ Fin sphereEdgeModels.circleCount) ≃
        sphereEdgeBundle.EdgeActualComponent,
      ∀ s, (e s).1 = sphereEdgeBundle.wholeComponent (sphereEdgeModels.componentEquiv s) :=
  totalComponentEquiv_G1 sphereEdgeBundle sphereEdgeModels

/-- `totalComponentEquiv_G1` on the edge data of the S³ rows. -/
theorem sphereRowsTotalComponentEquiv_G1 :
    ∃ e : (Fin (spherePreparedW sphereJunctions).rows.edgeModels.intervalCount ⊕
          Fin (spherePreparedW sphereJunctions).rows.edgeModels.circleCount) ≃
        (spherePreparedW sphereJunctions).rows.edge.EdgeActualComponent,
      ∀ s, (e s).1 = (spherePreparedW sphereJunctions).rows.edge.wholeComponent
        ((spherePreparedW sphereJunctions).rows.edgeModels.componentEquiv s) :=
  totalComponentEquiv_G1 _ _

/-- **Non-vacuity**: the S³ edge piece has exactly two actual components. -/
theorem sphere_edgeActualComponent_card_G1 :
    Nat.card sphereEdgeBundle.EdgeActualComponent = 2 := by
  rw [← Nat.card_congr sphereEdgeModels.totalComponentEquivOf_G1]
  change Nat.card (Fin 2 ⊕ Fin 0) = 2
  simp

/-- The actual component of the label `inl i` is the range of the polar handle `i`. -/
theorem sphere_actualComponent_handle_G1 (i : Fin 2) :
    (sphereEdgeModels.totalComponentEquivOf_G1 (.inl i)).1 =
      range (sphereEdgeModels.intervalTriv i).map :=
  (sphereEdgeModels.intervalTriv_range i).symm

/-! ## Vertices and ports of the S³ rows -/

/-- `exists_vertexLayer_G1` on the S³ rows. -/
theorem sphereExistsVertexLayer_G1 :
    ∃ V : VertexLayer sphereW,
      Nonempty (VertexModelLink (spherePreparedW sphereJunctions).rows V) :=
  exists_vertexLayer_G1 _

/-- Every vertex link of the S³ rows has three vertices (`Z₋`, `S`, `Z₊`). -/
theorem sphere_vertexCount_G1 {V : VertexLayer sphereW}
    (vlink : VertexModelLink (spherePreparedW sphereJunctions).rows V) : V.vertexCount = 3 :=
  vlink.vertexCount_eq_G1

/-- The generic vertex layer of the S³ rows has the hand-built vertex `0` (the inner ball). -/
theorem sphere_vertexLayer_G1_vertex_zero :
    (vertexLayer_G1 (spherePreparedW sphereJunctions).rows).vertex (0 : Fin 3) =
      sphereVertexLayer.vertex (0 : Fin 3) :=
  rfl

/-- `exists_portLayer_G1` on the S³ rows over the hand-built vertex layer and link. -/
theorem sphereExistsPortLayer_G1 :
    ∃ O : PortLayer sphereW (BoundaryTori.empty sphereW) sphereVertexLayer,
      PortModelLink (spherePreparedW sphereJunctions).rows sphereVertexModelLinkW O :=
  exists_portLayer_G1 _ _ _

/-- The generic port layer over the hand-built vertex layer and link IS `spherePortLayer`. -/
theorem sphere_portLayer_G1_eq :
    portLayer_G1 (spherePreparedW sphereJunctions).rows sphereVertexLayer sphereVertexModelLinkW =
      spherePortLayer := by
  unfold portLayer_G1 spherePortLayer
  congr 1

/-- The vertex → port chain of GROUP G on the S³ rows. -/
theorem sphereVertexLayerPortLayer_G1 :
    ∃ V : VertexLayer sphereW,
      ∃ vlink : VertexModelLink (spherePreparedW sphereJunctions).rows V,
        ∃ O : PortLayer sphereW (BoundaryTori.empty sphereW) V,
          PortModelLink (spherePreparedW sphereJunctions).rows vlink O :=
  exists_vertexLayer_portLayer_G1 _

end GC.GraphManifold.Assembly.FC39P0
