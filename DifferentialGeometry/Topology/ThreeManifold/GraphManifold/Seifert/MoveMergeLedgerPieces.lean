import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveMergeLedgerKept

/-!
# Native selected component and port cardinalities

The selected quotient is the actual last native component of contraction. The native port
bijections give the exact numbers of owned sides for this component and every kept component.
-/

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Function DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.Topology (componentCarrier)
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.TorusPresentation

variable {W : CompactCarrier.{u}} (T : TorusPresentation W)
  (S : Finset (Fin T.components.count)) (K : Finset (Fin T.pairing.count))
  (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
  (hext : ∀ i, T.externalPiece i ∉ S) (hk : T.cutCarrier.kind = .withBoundary)
  (hconn : IsConnected ((T.restrictAlongCarrier S K hK hext).interior :
    Set (T.restrictAlongPairing S K hK).QuotientSpace))

local instance restrictedAlongCharts :
    ChartedSpace (T.restrictAlongCarrier S K hK hext).kind.Space
      (T.restrictAlongCarrier S K hK hext).Carrier :=
  (T.restrictAlongCarrier S K hK hext).charts


private def contractAlongLastGeometryDiffeomorph (a : Fin Sᶜ.card ⊕ Unit)
    (ha : a = Sum.inr ()) :
    (T.restrictAlongCarrier S K hK hext).Carrier ≃ₘ⟮
      (T.restrictAlongCarrier S K hK hext).model, CarrierModel.withBoundary.model⟯
      (T.alongPieceGeometry S K hK hext hk
        (T.restrictAlong_hconn_complement S K hK hext hconn) a).Carrier := by
  subst a
  exact Diffeomorph.refl (T.restrictAlongCarrier S K hK hext).model
    (T.restrictAlongCarrier S K hK hext).Carrier ∞

def contractAlongLastDiffeomorph :
    (T.restrictAlongCarrier S K hK hext).Carrier ≃ₘ⟮
      (T.restrictAlongCarrier S K hK hext).model,
      (componentCarrier (T.contractAlong S K hK hext hk hconn).cutCarrier
        (T.contractAlong S K hK hext hk hconn).components (Fin.last Sᶜ.card)).model⟯
      (componentCarrier (T.contractAlong S K hK hext hk hconn).cutCarrier
        (T.contractAlong S K hK hext hk hconn).components (Fin.last Sᶜ.card)).Carrier :=
  (T.contractAlongLastGeometryDiffeomorph S K hK hext hk hconn
    ((T.alongGeometryIndexEquiv S).symm (Fin.last Sᶜ.card))
    ((T.alongGeometryIndexEquiv S).symm_apply_eq.mpr rfl)).trans
    ((T.alongCutSystem S K hK hext hk
      (T.restrictAlong_hconn_complement S K hK hext hconn)).pieceDiffeomorph
      (Fin.last Sᶜ.card))

theorem card_contractAlong_ownedSide_kept {i : Fin T.components.count} (hi : i ∉ S) :
    Fintype.card ((T.contractAlong S K hK hext hk hconn).OwnedSide
      (T.contractAlongKeptIndex S K hK hext hk hconn hi)) = Fintype.card (T.OwnedSide i) := by
  let j := T.subIndexOf Sᶜ (Finset.mem_compl.mpr hi)
  let A := T.alongCutSystem S K hK hext hk
    (T.restrictAlong_hconn_complement S K hK hext hconn)
  have hc := Fintype.card_congr (A.port j.castSucc).symm
  rw [Fintype.card_fin] at hc
  refine hc.trans ?_
  change (T.alongPieceGeometry S K hK hext hk
    (T.restrictAlong_hconn_complement S K hK hext hconn)
    ((T.alongGeometryIndexEquiv S).symm j.castSucc)).torusCount = _
  rw [show (T.alongGeometryIndexEquiv S).symm j.castSucc = Sum.inl j from
    (T.alongGeometryIndexEquiv S).symm_apply_eq.mpr rfl]
  change Fintype.card (T.OwnedSide (T.subIndex Sᶜ j)) = _
  rw [T.subIndex_subIndexOf Sᶜ (Finset.mem_compl.mpr hi)]

theorem card_contractAlong_ownedSide_last :
    Fintype.card ((T.contractAlong S K hK hext hk hconn).OwnedSide (Fin.last Sᶜ.card)) =
      Fintype.card (T.AlongBoundarySide S K) := by
  let A := T.alongCutSystem S K hK hext hk
    (T.restrictAlong_hconn_complement S K hK hext hconn)
  have hc := Fintype.card_congr (A.port (Fin.last Sᶜ.card)).symm
  rw [Fintype.card_fin] at hc
  refine hc.trans ?_
  change (T.alongPieceGeometry S K hK hext hk
    (T.restrictAlong_hconn_complement S K hK hext hconn)
    ((T.alongGeometryIndexEquiv S).symm (Fin.last Sᶜ.card))).torusCount = _
  rw [show (T.alongGeometryIndexEquiv S).symm (Fin.last Sᶜ.card) = Sum.inr () from
    (T.alongGeometryIndexEquiv S).symm_apply_eq.mpr rfl]
  rfl

end GC.Seifert.TorusPresentation
