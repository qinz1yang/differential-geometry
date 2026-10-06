import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39CarrierTransportRows74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39CarrierTransportJunctionsCross74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39CarrierTransportEdgeModelsCross74

/-!
# Draft 74, D74-6: `FC39RowsV2.transportCross74` — the whole record along ONE carrier
diffeomorphism between carriers of ANY kinds

Lane O-CROSS, G3 (REG-CHAIN G25). Same assembly as `FC39RowsV2.transport74` (lane C14-REG-CHAIN
by S-REG-CHAIN, G24) WITHOUT `hk : W₀.kind = W₁.kind`: the edge bundle, its component models,
the junctions and the tubes use the cross-kind transports of O-CROSS G3 (whole disks by
`isSmoothEmbedding_comp_carrier_cross_disk_R74`).

* **`FC39RowsV2.transportCross74 e Rw : FC39RowsV2 W₁ (E.transport74 e)`**;
* projections `FC39RowsV2.transportCross74_zero` … `_junctions` (all `rfl`);
* `FC39RowsV2.transportCross74_sets` (zero union, slim union, edge piece, circle region,
  `M₁`, `M₂`, `M₃`, `∂M₂` are the `e`-images).
-/

set_option autoImplicit false

noncomputable section

open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open Manifold TopologicalSpace
open scoped Manifold ContDiff Topology

universe u

namespace GC.GraphManifold.Assembly.FC39P0

attribute [local instance] diskChartsBase_FC39P0 diskChartsEdges_FC39P0

variable {W₀ W₁ : CompactCarrier.{u}} {n : ℕ}

/-- **`FC39RowsV2.transportCross74`** (D74-6): the whole row record carried along `e`, onto the
transported boundary tori. -/
def FC39RowsV2.transportCross74 (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)
    {E : BoundaryTori W₀ n} (Rw : FC39RowsV2 W₀ E) :
    FC39RowsV2 W₁ (E.transport74 e) where
  zero := Rw.zero.mapCarrier74 e
  cusp := Rw.cusp.mapCarrier74 e
  slim := Rw.slim.mapCarrier74 e
  edge := Rw.edge.mapCarrierCross74 e
  edgeModels := Rw.edgeModels.mapCarrierCross74 e
  circle := Rw.circle.mapCarrier74 e
  junctions := Rw.junctions.mapCarrierCross74 e
  labelledTubes := Rw.labelledTubes.mapCarrierCross74 e

section Projections

variable (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier) {E : BoundaryTori W₀ n}
  (Rw : FC39RowsV2 W₀ E)

/-- The transported zero domains are `ZeroDomains.mapCarrier74`. -/
theorem FC39RowsV2.transportCross74_zero :
    (Rw.transportCross74 e).zero = Rw.zero.mapCarrier74 e :=
  rfl

/-- The transported cusp cores are `CuspCores.mapCarrier74`. -/
theorem FC39RowsV2.transportCross74_cusp :
    (Rw.transportCross74 e).cusp = Rw.cusp.mapCarrier74 e :=
  rfl

/-- The transported slim pieces are `SlimPiecesV2.mapCarrier74`. -/
theorem FC39RowsV2.transportCross74_slim :
    (Rw.transportCross74 e).slim = Rw.slim.mapCarrier74 e :=
  rfl

/-- The transported edge bundle is `EdgeBundle.mapCarrierCross74`. -/
theorem FC39RowsV2.transportCross74_edge :
    (Rw.transportCross74 e).edge = Rw.edge.mapCarrierCross74 e :=
  rfl

/-- The transported circle bundle is `CircleBundle.mapCarrier74`. -/
theorem FC39RowsV2.transportCross74_circle :
    (Rw.transportCross74 e).circle = Rw.circle.mapCarrier74 e :=
  rfl

/-- The transported junctions are `JunctionsV2.mapCarrierCross74`. -/
theorem FC39RowsV2.transportCross74_junctions :
    (Rw.transportCross74 e).junctions = Rw.junctions.mapCarrierCross74 e :=
  rfl

/-- **The set-level statement of D74-6 for the whole record**: the zero union, the slim union,
the edge piece, the circle region, `M₁`, `M₂`, `M₃` and `∂M₂` of the transported record are the
`e`-images of those of `Rw`. -/
theorem FC39RowsV2.transportCross74_sets :
    (⋃ i, range ((Rw.transportCross74 e).zero.piece i).map) =
        e '' ⋃ i, range (Rw.zero.piece i).map ∧
      (Rw.transportCross74 e).slim.union = e '' Rw.slim.union ∧
      (Rw.transportCross74 e).edge.edgePiece = e '' Rw.edge.edgePiece ∧
      (Rw.transportCross74 e).circle.region = e '' Rw.circle.region ∧
      regionM1 (Rw.transportCross74 e).zero (Rw.transportCross74 e).cusp =
        e '' regionM1 Rw.zero Rw.cusp ∧
      regionM2 (Rw.transportCross74 e).slim = e '' regionM2 Rw.slim ∧
      regionM3 (Rw.transportCross74 e).slim (Rw.transportCross74 e).edge =
        e '' regionM3 Rw.slim Rw.edge ∧
      (Rw.transportCross74 e).slim.boundaryM2 = e '' Rw.slim.boundaryM2 :=
  ⟨Rw.zero.mapCarrier74_union e, Rw.slim.mapCarrier74_union e,
    EdgeBundle.mapCarrierCross74_edgePiece e Rw.edge, Rw.circle.mapCarrier74_region e,
    regionM1_mapCarrier74 e Rw.zero Rw.cusp, regionM2_mapCarrier74 e Rw.slim,
    regionM3_mapCarrierCross74 e Rw.slim Rw.edge, boundaryM2_mapCarrier74 e Rw.slim⟩

end Projections

end GC.GraphManifold.Assembly.FC39P0
