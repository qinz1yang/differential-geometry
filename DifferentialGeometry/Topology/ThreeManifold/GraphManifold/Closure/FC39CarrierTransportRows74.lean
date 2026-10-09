import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39CarrierTransportTubes74
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.FC39CarrierTransportEdgeModels74

/-!
# Draft 74, D74-6: `FC39RowsV2.transport74` — the whole record along ONE carrier diffeomorphism

Lane C14-REG-CHAIN (by S-REG-CHAIN), G24. For a carrier diffeomorphism
`e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier` between carriers of the same kind and a row
record `Rw : FC39RowsV2 W₀ E`:

* **`FC39RowsV2.transport74 e hk Rw : FC39RowsV2 W₁ (E.transport74 e)`** assembles the two halves
  of D74-6: pieces / bundles (`ZeroDomains`, `CuspCores`, `SlimPiecesV2`, `EdgeBundle`,
  `EdgeComponentModels`, `CircleBundle`, G13–G22) and faces / junctions / tubes
  (`JunctionsV2`, `LabelledCornerTubes`, G23). The target boundary tori are the transported
  ports `E.transport74 e`, never an arbitrary `E₁`.
* the field projections are the transported fields (`transport74_zero` …
  `transport74_labelledTubes`, all `rfl`);
* the set-level statement of D74-6 for the whole record: zero union, slim union, edge piece,
  circle region, `M₁`, `M₂`, `M₃`, `∂M₂` of the transported record are the `e`-images
  (`FC39RowsV2.transport74_sets`).
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

/-- **`FC39RowsV2.transport74`** (D74-6): the whole row record carried along `e`, onto the
transported boundary tori. -/
def FC39RowsV2.transport74 (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier)
    (hk : W₀.kind = W₁.kind) {E : BoundaryTori W₀ n} (Rw : FC39RowsV2 W₀ E) :
    FC39RowsV2 W₁ (E.transport74 e) where
  zero := Rw.zero.mapCarrier74 e
  cusp := Rw.cusp.mapCarrier74 e
  slim := Rw.slim.mapCarrier74 e
  edge := Rw.edge.mapCarrier74 e hk
  edgeModels := Rw.edgeModels.mapCarrier74 e hk
  circle := Rw.circle.mapCarrier74 e
  junctions := Rw.junctions.mapCarrier74 e hk
  labelledTubes := Rw.labelledTubes.mapCarrier74 e hk

section Projections

variable (e : W₀.Carrier ≃ₘ⟮W₀.model, W₁.model⟯ W₁.Carrier) (hk : W₀.kind = W₁.kind)
  {E : BoundaryTori W₀ n} (Rw : FC39RowsV2 W₀ E)

/-- The transported zero domains are `ZeroDomains.mapCarrier74`. -/
theorem FC39RowsV2.transport74_zero :
    (Rw.transport74 e hk).zero = Rw.zero.mapCarrier74 e :=
  rfl

/-- The transported cusp cores are `CuspCores.mapCarrier74`. -/
theorem FC39RowsV2.transport74_cusp :
    (Rw.transport74 e hk).cusp = Rw.cusp.mapCarrier74 e :=
  rfl

/-- The transported slim pieces are `SlimPiecesV2.mapCarrier74`. -/
theorem FC39RowsV2.transport74_slim :
    (Rw.transport74 e hk).slim = Rw.slim.mapCarrier74 e :=
  rfl

/-- The transported edge bundle is `EdgeBundle.mapCarrier74`. -/
theorem FC39RowsV2.transport74_edge :
    (Rw.transport74 e hk).edge = Rw.edge.mapCarrier74 e hk :=
  rfl

/-- The transported circle bundle is `CircleBundle.mapCarrier74`. -/
theorem FC39RowsV2.transport74_circle :
    (Rw.transport74 e hk).circle = Rw.circle.mapCarrier74 e :=
  rfl

/-- The transported junctions are `JunctionsV2.mapCarrier74`. -/
theorem FC39RowsV2.transport74_junctions :
    (Rw.transport74 e hk).junctions = Rw.junctions.mapCarrier74 e hk :=
  rfl

/-- **The set-level statement of D74-6 for the whole record**: the zero union, the slim union,
the edge piece, the circle region, `M₁`, `M₂`, `M₃` and `∂M₂` of the transported record are the
`e`-images of those of `Rw`. -/
theorem FC39RowsV2.transport74_sets :
    (⋃ i, range ((Rw.transport74 e hk).zero.piece i).map) =
        e '' ⋃ i, range (Rw.zero.piece i).map ∧
      (Rw.transport74 e hk).slim.union = e '' Rw.slim.union ∧
      (Rw.transport74 e hk).edge.edgePiece = e '' Rw.edge.edgePiece ∧
      (Rw.transport74 e hk).circle.region = e '' Rw.circle.region ∧
      regionM1 (Rw.transport74 e hk).zero (Rw.transport74 e hk).cusp =
        e '' regionM1 Rw.zero Rw.cusp ∧
      regionM2 (Rw.transport74 e hk).slim = e '' regionM2 Rw.slim ∧
      regionM3 (Rw.transport74 e hk).slim (Rw.transport74 e hk).edge =
        e '' regionM3 Rw.slim Rw.edge ∧
      (Rw.transport74 e hk).slim.boundaryM2 = e '' Rw.slim.boundaryM2 :=
  ⟨Rw.zero.mapCarrier74_union e, Rw.slim.mapCarrier74_union e,
    EdgeBundle.mapCarrier74_edgePiece e hk Rw.edge, Rw.circle.mapCarrier74_region e,
    regionM1_mapCarrier74 e Rw.zero Rw.cusp, regionM2_mapCarrier74 e Rw.slim,
    regionM3_mapCarrier74 e hk Rw.slim Rw.edge, boundaryM2_mapCarrier74 e Rw.slim⟩

end Projections

end GC.GraphManifold.Assembly.FC39P0
