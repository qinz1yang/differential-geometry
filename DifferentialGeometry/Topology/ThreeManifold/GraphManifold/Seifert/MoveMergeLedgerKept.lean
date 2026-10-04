import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.ContractAlongPresentation
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveTerminal

/-!
# Passive actual components under selected contraction

A component outside the selected set is transported through its native kept geometry into the
new actual cut carrier. Its full compact component diffeomorphism commutes with the two cut
maps and preserves the actual component orientations through the oriented quotient folds.
-/

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Function DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.Topology (componentCarrier)
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

private def keptRecastDiffeomorph (C : CompactCarrier.{u}) (k : CarrierModel) (h : C.kind = k) :
    C.Carrier ≃ₘ⟮C.model, (recastCarrier C k h).model⟯ (recastCarrier C k h).Carrier := by
  subst k
  exact Diffeomorph.refl C.model C.Carrier ∞

private theorem keptRecastDiffeomorph_apply
    (C : CompactCarrier.{u}) (k : CarrierModel) (h : C.kind = k) (x : C.Carrier) :
    keptRecastDiffeomorph C k h x = x := by
  subst k
  rfl

private def keptComponentIndexDiffeomorph (C : CompactCarrier.{u}) (A : C.Components)
    {i j : Fin A.count} (h : i = j) :
    (componentCarrier C A i).Carrier ≃ₘ⟮(componentCarrier C A i).model,
      (componentCarrier C A j).model⟯ (componentCarrier C A j).Carrier := by
  subst j
  exact Diffeomorph.refl (componentCarrier C A i).model (componentCarrier C A i).Carrier ∞

private theorem keptComponentIndexDiffeomorph_apply_val
    (C : CompactCarrier.{u}) (A : C.Components) {i j : Fin A.count} (h : i = j)
    (x : (componentCarrier C A i).Carrier) :
    (keptComponentIndexDiffeomorph C A h x).val = x.val := by
  subst j
  rfl

namespace TorusPresentation

variable {W : CompactCarrier.{u}} (T : TorusPresentation W)
  (S : Finset (Fin T.components.count)) (K : Finset (Fin T.pairing.count))
  (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
  (hext : ∀ i, T.externalPiece i ∉ S) (hk : T.cutCarrier.kind = .withBoundary)
  (hconn : IsConnected ((T.restrictAlongCarrier S K hK hext).interior :
    Set (T.restrictAlongPairing S K hK).QuotientSpace))

private def contractAlongKeptGeometryDiffeomorph (j : Fin Sᶜ.card)
    (a : Fin Sᶜ.card ⊕ Unit) (ha : a = Sum.inl j) :
    (componentCarrier T.cutCarrier T.components (T.subIndex Sᶜ j)).Carrier ≃ₘ⟮
      (componentCarrier T.cutCarrier T.components (T.subIndex Sᶜ j)).model,
      CarrierModel.withBoundary.model⟯
      (T.alongPieceGeometry S K hK hext hk
        (T.restrictAlong_hconn_complement S K hK hext hconn) a).Carrier := by
  subst a
  exact keptRecastDiffeomorph
    (componentCarrier T.cutCarrier T.components (T.subIndex Sᶜ j)) .withBoundary hk

private theorem contractAlongKeptGeometryDiffeomorph_map (j : Fin Sᶜ.card)
    (a : Fin Sᶜ.card ⊕ Unit) (ha : a = Sum.inl j)
    (x : (componentCarrier T.cutCarrier T.components (T.subIndex Sᶜ j)).Carrier) :
    (T.alongPieceGeometry S K hK hext hk
      (T.restrictAlong_hconn_complement S K hK hext hconn) a).map
      (T.contractAlongKeptGeometryDiffeomorph S K hK hext hk hconn j a ha x) =
      T.cutMap x.val := by
  subst a
  change T.cutMap (keptRecastDiffeomorph
    (componentCarrier T.cutCarrier T.components (T.subIndex Sᶜ j)) .withBoundary hk x).val = _
  rw [keptRecastDiffeomorph_apply]

private def contractAlongKeptNativeDiffeomorph (j : Fin Sᶜ.card) :
    (componentCarrier T.cutCarrier T.components (T.subIndex Sᶜ j)).Carrier ≃ₘ⟮
      (componentCarrier T.cutCarrier T.components (T.subIndex Sᶜ j)).model,
      CarrierModel.withBoundary.model⟯
      (T.alongPieceGeometry S K hK hext hk
        (T.restrictAlong_hconn_complement S K hK hext hconn)
        ((T.alongGeometryIndexEquiv S).symm j.castSucc)).Carrier :=
  T.contractAlongKeptGeometryDiffeomorph S K hK hext hk hconn j
    ((T.alongGeometryIndexEquiv S).symm j.castSucc)
    ((T.alongGeometryIndexEquiv S).symm_apply_eq.mpr rfl)

private def contractAlongKeptAtDiffeomorph (j : Fin Sᶜ.card) :
    (componentCarrier T.cutCarrier T.components (T.subIndex Sᶜ j)).Carrier ≃ₘ⟮
      (componentCarrier T.cutCarrier T.components (T.subIndex Sᶜ j)).model,
      (componentCarrier (T.contractAlong S K hK hext hk hconn).cutCarrier
        (T.contractAlong S K hK hext hk hconn).components j.castSucc).model⟯
      (componentCarrier (T.contractAlong S K hK hext hk hconn).cutCarrier
        (T.contractAlong S K hK hext hk hconn).components j.castSucc).Carrier :=
  (T.contractAlongKeptNativeDiffeomorph S K hK hext hk hconn j).trans
    ((T.alongCutSystem S K hK hext hk
      (T.restrictAlong_hconn_complement S K hK hext hconn)).pieceDiffeomorph j.castSucc)

private theorem contractAlongKeptAtDiffeomorph_cutMap (j : Fin Sᶜ.card)
    (x : (componentCarrier T.cutCarrier T.components (T.subIndex Sᶜ j)).Carrier) :
    (T.contractAlong S K hK hext hk hconn).cutMap
      (T.contractAlongKeptAtDiffeomorph S K hK hext hk hconn j x).val = T.cutMap x.val := by
  change (T.alongPieceGeometry S K hK hext hk
      (T.restrictAlong_hconn_complement S K hK hext hconn)
      ((T.alongGeometryIndexEquiv S).symm j.castSucc)).map
    (T.contractAlongKeptNativeDiffeomorph S K hK hext hk hconn j x) = T.cutMap x.val
  exact T.contractAlongKeptGeometryDiffeomorph_map S K hK hext hk hconn j _ _ x


def contractAlongKeptIndex {i : Fin T.components.count} (hi : i ∉ S) :
    Fin (T.contractAlong S K hK hext hk hconn).components.count :=
  (T.subIndexOf Sᶜ (Finset.mem_compl.mpr hi)).castSucc

def contractAlongKeptDiffeomorph {i : Fin T.components.count} (hi : i ∉ S) :
    (componentCarrier T.cutCarrier T.components i).Carrier ≃ₘ⟮
      (componentCarrier T.cutCarrier T.components i).model,
      (componentCarrier (T.contractAlong S K hK hext hk hconn).cutCarrier
        (T.contractAlong S K hK hext hk hconn).components
        (T.contractAlongKeptIndex S K hK hext hk hconn hi)).model⟯
      (componentCarrier (T.contractAlong S K hK hext hk hconn).cutCarrier
        (T.contractAlong S K hK hext hk hconn).components
        (T.contractAlongKeptIndex S K hK hext hk hconn hi)).Carrier := by
  let j := T.subIndexOf Sᶜ (Finset.mem_compl.mpr hi)
  have hj : T.subIndex Sᶜ j = i := T.subIndex_subIndexOf Sᶜ (Finset.mem_compl.mpr hi)
  exact (keptComponentIndexDiffeomorph T.cutCarrier T.components hj.symm).trans
    (T.contractAlongKeptAtDiffeomorph S K hK hext hk hconn j)

theorem contractAlongKeptDiffeomorph_cutMap {i : Fin T.components.count} (hi : i ∉ S)
    (x : (componentCarrier T.cutCarrier T.components i).Carrier) :
    (T.contractAlong S K hK hext hk hconn).cutMap
      (T.contractAlongKeptDiffeomorph S K hK hext hk hconn hi x).val = T.cutMap x.val := by
  let j := T.subIndexOf Sᶜ (Finset.mem_compl.mpr hi)
  have hj : T.subIndex Sᶜ j = i := T.subIndex_subIndexOf Sᶜ (Finset.mem_compl.mpr hi)
  let y := keptComponentIndexDiffeomorph T.cutCarrier T.components hj.symm x
  change (T.contractAlong S K hK hext hk hconn).cutMap
    (T.contractAlongKeptAtDiffeomorph S K hK hext hk hconn j y).val = _
  rw [contractAlongKeptAtDiffeomorph_cutMap, keptComponentIndexDiffeomorph_apply_val]


theorem contractAlongKeptDiffeomorph_oriented {i : Fin T.components.count} (hi : i ∉ S) :
    (T.contractAlongKeptDiffeomorph S K hK hext hk hconn hi).preservesOrientation
      (componentCarrier T.cutCarrier T.components i).orientation
      (componentCarrier (T.contractAlong S K hK hext hk hconn).cutCarrier
        (T.contractAlong S K hK hext hk hconn).components
        (T.contractAlongKeptIndex S K hK hext hk hconn hi)).orientation := by
  let U := T.contractAlong S K hK hext hk hconn
  let j := T.contractAlongKeptIndex S K hK hext hk hconn hi
  let D := T.contractAlongKeptDiffeomorph S K hK hext hk hconn hi
  change D.preservesOrientation
    (componentCarrier T.cutCarrier T.components i).orientation
    (componentCarrier U.cutCarrier U.components j).orientation
  apply preservesOrientation_of_comp D (T.cutMap ∘ Subtype.val) (U.cutMap ∘ Subtype.val)
    (oM := (componentCarrier T.cutCarrier T.components i).orientation)
    (oN := (componentCarrier U.cutCarrier U.components j).orientation)
    (O := W.orientation)
  · intro y
    exact (U.quotient_smooth.comp contMDiff_subtype_val).mdifferentiableAt (by simp)
  · exact T.contractAlongKeptDiffeomorph_cutMap S K hK hext hk hconn hi
  · exact T.isOrientedFold_cutMap.restrict T.quotient_smooth _
  · exact U.isOrientedFold_cutMap.restrict U.quotient_smooth _


end TorusPresentation

end GC.Seifert
