import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveMergeLedgerKept

/-!
# Native kept ports under selected contraction

The native kept port bijection transports each full half collar through the actual compact
component diffeomorphism. Retained seam sides and external sides keep their native labels.
-/

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Function DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.Topology (componentCarrier)
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

private def keptPortsKeptRecastDiffeomorph
    (C : CompactCarrier.{u}) (k : CarrierModel) (h : C.kind = k) :
    C.Carrier ≃ₘ⟮C.model, (recastCarrier C k h).model⟯ (recastCarrier C k h).Carrier := by
  subst k
  exact Diffeomorph.refl C.model C.Carrier ∞

private theorem keptPortsKeptRecastDiffeomorph_apply
    (C : CompactCarrier.{u}) (k : CarrierModel) (h : C.kind = k) (x : C.Carrier) :
    keptPortsKeptRecastDiffeomorph C k h x = x := by
  subst k
  rfl

private def keptPortsKeptComponentIndexDiffeomorph (C : CompactCarrier.{u}) (A : C.Components)
    {i j : Fin A.count} (h : i = j) :
    (componentCarrier C A i).Carrier ≃ₘ⟮(componentCarrier C A i).model,
      (componentCarrier C A j).model⟯ (componentCarrier C A j).Carrier := by
  subst j
  exact Diffeomorph.refl (componentCarrier C A i).model (componentCarrier C A i).Carrier ∞

private theorem keptPortsKeptComponentIndexDiffeomorph_apply_val
    (C : CompactCarrier.{u}) (A : C.Components) {i j : Fin A.count} (h : i = j)
    (x : (componentCarrier C A i).Carrier) :
    (keptPortsKeptComponentIndexDiffeomorph C A h x).val = x.val := by
  subst j
  rfl

namespace TorusPresentation

variable {W : CompactCarrier.{u}} (T : TorusPresentation W)
  (S : Finset (Fin T.components.count)) (K : Finset (Fin T.pairing.count))
  (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
  (hext : ∀ i, T.externalPiece i ∉ S) (hk : T.cutCarrier.kind = .withBoundary)
  (hconn : IsConnected ((T.restrictAlongCarrier S K hK hext).interior :
    Set (T.restrictAlongPairing S K hK).QuotientSpace))

private def keptPortsContractAlongKeptGeometryDiffeomorph (j : Fin Sᶜ.card)
    (a : Fin Sᶜ.card ⊕ Unit) (ha : a = Sum.inl j) :
    (componentCarrier T.cutCarrier T.components (T.subIndex Sᶜ j)).Carrier ≃ₘ⟮
      (componentCarrier T.cutCarrier T.components (T.subIndex Sᶜ j)).model,
      CarrierModel.withBoundary.model⟯
      (T.alongPieceGeometry S K hK hext hk
        (T.restrictAlong_hconn_complement S K hK hext hconn) a).Carrier := by
  subst a
  exact keptPortsKeptRecastDiffeomorph
    (componentCarrier T.cutCarrier T.components (T.subIndex Sᶜ j)) .withBoundary hk

private theorem keptPortsIndex_inverse_castSucc (j : Fin Sᶜ.card) :
    (T.alongGeometryIndexEquiv S).symm j.castSucc = Sum.inl j :=
  (T.alongGeometryIndexEquiv S).symm_apply_eq.mpr rfl

private def keptPortsContractAlongKeptNativeDiffeomorph (j : Fin Sᶜ.card) :
    (componentCarrier T.cutCarrier T.components (T.subIndex Sᶜ j)).Carrier ≃ₘ⟮
      (componentCarrier T.cutCarrier T.components (T.subIndex Sᶜ j)).model,
      CarrierModel.withBoundary.model⟯
      (T.alongPieceGeometry S K hK hext hk
        (T.restrictAlong_hconn_complement S K hK hext hconn)
        ((T.alongGeometryIndexEquiv S).symm j.castSucc)).Carrier :=
  T.keptPortsContractAlongKeptGeometryDiffeomorph S K hK hext hk hconn j
    ((T.alongGeometryIndexEquiv S).symm j.castSucc)
    (T.keptPortsIndex_inverse_castSucc S j)

private def keptPortsContractAlongKeptAtDiffeomorph (j : Fin Sᶜ.card) :
    (componentCarrier T.cutCarrier T.components (T.subIndex Sᶜ j)).Carrier ≃ₘ⟮
      (componentCarrier T.cutCarrier T.components (T.subIndex Sᶜ j)).model,
      (componentCarrier (T.contractAlong S K hK hext hk hconn).cutCarrier
        (T.contractAlong S K hK hext hk hconn).components j.castSucc).model⟯
      (componentCarrier (T.contractAlong S K hK hext hk hconn).cutCarrier
        (T.contractAlong S K hK hext hk hconn).components j.castSucc).Carrier :=
  (T.keptPortsContractAlongKeptNativeDiffeomorph S K hK hext hk hconn j).trans
    ((T.alongCutSystem S K hK hext hk
      (T.restrictAlong_hconn_complement S K hK hext hconn)).pieceDiffeomorph j.castSucc)

private def keptPortsDiffeomorph {i : Fin T.components.count} (hi : i ∉ S) :
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
  exact (keptPortsKeptComponentIndexDiffeomorph T.cutCarrier T.components hj.symm).trans
    (T.keptPortsContractAlongKeptAtDiffeomorph S K hK hext hk hconn j)

private theorem keptPortsDiffeomorph_eq {i : Fin T.components.count} (hi : i ∉ S) :
    T.keptPortsDiffeomorph S K hK hext hk hconn hi =
      T.contractAlongKeptDiffeomorph S K hK hext hk hconn hi := rfl

private def keptPortsOwnedIndexEquiv {i j : Fin T.components.count} (h : i = j) :
    T.OwnedSide i ≃ T.OwnedSide j := by
  subst j
  exact Equiv.refl _

private theorem keptPortsIndexDiffeomorph_collar {i j : Fin T.components.count} (h : i = j)
    (s : T.OwnedSide i) (p : Torus × EuclideanHalfSpace 1) :
    T.pieceCollar j (T.keptPortsOwnedIndexEquiv h s) p =
      keptPortsKeptComponentIndexDiffeomorph T.cutCarrier T.components h
        (T.pieceCollar i s p) := by
  subst j
  rfl

private theorem keptPortsOwnedIndexEquiv_val {i j : Fin T.components.count} (h : i = j)
    (s : T.OwnedSide i) : (T.keptPortsOwnedIndexEquiv h s).val = s.val := by
  subst j
  rfl

private def keptPortsGeometryPortEquiv (j : Fin Sᶜ.card) (a : Fin Sᶜ.card ⊕ Unit)
    (ha : a = Sum.inl j) :
    T.OwnedSide (T.subIndex Sᶜ j) ≃
      Fin ((T.alongPieceGeometry S K hK hext hk
        (T.restrictAlong_hconn_complement S K hK hext hconn) a).torusCount) := by
  subst a
  exact Fintype.equivFin _

private theorem keptPortsGeometryPortEquiv_sigma (j : Fin Sᶜ.card)
    (a : Fin Sᶜ.card ⊕ Unit) (ha : a = Sum.inl j)
    (s : T.OwnedSide (T.subIndex Sᶜ j)) :
    (⟨a, T.keptPortsGeometryPortEquiv S K hK hext hk hconn j a ha s⟩ :
      Σ b, Fin ((T.alongPieceGeometry S K hK hext hk
        (T.restrictAlong_hconn_complement S K hK hext hconn) b).torusCount)) =
      ⟨Sum.inl j, Fintype.equivFin _ s⟩ := by
  subst a
  rfl

private theorem keptPortsGeometryDiffeomorph_collar (j : Fin Sᶜ.card)
    (a : Fin Sᶜ.card ⊕ Unit) (ha : a = Sum.inl j)
    (s : T.OwnedSide (T.subIndex Sᶜ j)) (p : Torus × EuclideanHalfSpace 1) :
    (T.alongPieceGeometry S K hK hext hk
      (T.restrictAlong_hconn_complement S K hK hext hconn) a).collar
      (T.keptPortsGeometryPortEquiv S K hK hext hk hconn j a ha s) p =
      T.keptPortsContractAlongKeptGeometryDiffeomorph S K hK hext hk hconn j a ha
        (T.pieceCollar (T.subIndex Sᶜ j) s p) := by
  subst a
  change recastPD (componentCarrier T.cutCarrier T.components (T.subIndex Sᶜ j))
    .withBoundary hk ((T.pieceBoundaryTori (T.subIndex Sᶜ j)).collar
      (Fintype.equivFin _ s)) p = _
  rw [recastPD_apply]
  change T.pieceCollar (T.subIndex Sᶜ j) ((Fintype.equivFin _).symm
    (Fintype.equivFin _ s)) p = keptPortsKeptRecastDiffeomorph
      (componentCarrier T.cutCarrier T.components (T.subIndex Sᶜ j)) .withBoundary hk
      (T.pieceCollar (T.subIndex Sᶜ j) s p)
  rw [Equiv.symm_apply_apply, keptPortsKeptRecastDiffeomorph_apply]

private def keptPortsAtOwnedSideEquiv (j : Fin Sᶜ.card) :
    T.OwnedSide (T.subIndex Sᶜ j) ≃
      (T.contractAlong S K hK hext hk hconn).OwnedSide j.castSucc :=
  (T.keptPortsGeometryPortEquiv S K hK hext hk hconn j
    ((T.alongGeometryIndexEquiv S).symm j.castSucc)
    (T.keptPortsIndex_inverse_castSucc S j)).trans
    ((T.alongCutSystem S K hK hext hk
      (T.restrictAlong_hconn_complement S K hK hext hconn)).port j.castSucc)

private theorem keptPortsAtOwnedSideEquiv_collar (j : Fin Sᶜ.card)
    (s : T.OwnedSide (T.subIndex Sᶜ j)) {p : Torus × EuclideanHalfSpace 1}
    (hp : p ∈ halfCollarSource) :
    (T.contractAlong S K hK hext hk hconn).pieceCollar j.castSucc
      (T.keptPortsAtOwnedSideEquiv S K hK hext hk hconn j s) p =
      T.keptPortsContractAlongKeptAtDiffeomorph S K hK hext hk hconn j
        (T.pieceCollar (T.subIndex Sᶜ j) s p) := by
  let A := T.alongCutSystem S K hK hext hk
    (T.restrictAlong_hconn_complement S K hK hext hconn)
  apply Subtype.ext
  rw [TorusPresentation.pieceCollar_apply _ _ _ hp]
  change A.toTorusPresentation.sideCollar (A.port j.castSucc
    (T.keptPortsGeometryPortEquiv S K hK hext hk hconn j
      ((T.alongGeometryIndexEquiv S).symm j.castSucc)
      (T.keptPortsIndex_inverse_castSucc S j) s)).val p = _
  rw [A.sideCollar_eq, A.sideOf_port, A.sideCollar_apply]
  exact congrArg (fun q => (⟨j.castSucc, q⟩ : A.Cut))
    (T.keptPortsGeometryDiffeomorph_collar S K hK hext hk hconn j _ _ s p)

private theorem keptPortsAtOwnedSideEquiv_label (j : Fin Sᶜ.card)
    (s : T.OwnedSide (T.subIndex Sᶜ j)) :
    (T.alongCutSystem S K hK hext hk
      (T.restrictAlong_hconn_complement S K hK hext hconn)).sideOf
      (T.keptPortsAtOwnedSideEquiv S K hK hext hk hconn j s).val =
    T.alongGeometryFiniteSideEquiv S K hK hext hk
      (T.restrictAlong_hconn_complement S K hK hext hconn)
      ⟨s.val, T.alongLedgerRetained_of_ownedOutside S K hK j s⟩ := by
  let A := T.alongCutSystem S K hK hext hk
    (T.restrictAlong_hconn_complement S K hK hext hconn)
  change A.sideOf (A.port j.castSucc
    (T.keptPortsGeometryPortEquiv S K hK hext hk hconn j
      ((T.alongGeometryIndexEquiv S).symm j.castSucc)
      (T.keptPortsIndex_inverse_castSucc S j) s)).val = _
  rw [A.sideOf_port]
  change (⟨j.castSucc, T.keptPortsGeometryPortEquiv S K hK hext hk hconn j
    ((T.alongGeometryIndexEquiv S).symm j.castSucc)
    (T.keptPortsIndex_inverse_castSucc S j) s⟩ :
    Σ k : Fin (Sᶜ.card + 1), Fin ((T.alongPieceGeometry S K hK hext hk
      (T.restrictAlong_hconn_complement S K hK hext hconn)
      ((T.alongGeometryIndexEquiv S).symm k)).torusCount)) = _
  have hs : T.alongGeometryOwner S K
      ⟨s.val, T.alongLedgerRetained_of_ownedOutside S K hK j s⟩ = Sum.inl j := by
    change (T.alongGeometryIndexEquiv S).symm (T.alongPieceIndex S (T.sidePiece s.val)) = _
    rw [s.property, (T.alongLedgerPieceIndex_castSucc_iff S _ j).mpr rfl]
    exact (T.alongGeometryIndexEquiv S).symm_apply_eq.mpr rfl
  let r : T.AlongLedgerRetainedSide K :=
    ⟨s.val, T.alongLedgerRetained_of_ownedOutside S K hK j s⟩
  let a : T.AlongGeometryOwned S K (Sum.inl j) := ⟨r, hs⟩
  have hf : (Equiv.sigmaFiberEquiv (T.alongGeometryOwner S K)).symm r =
      ⟨Sum.inl j, a⟩ :=
    (Equiv.sigmaFiberEquiv (T.alongGeometryOwner S K)).symm_apply_eq.mpr rfl
  have hp : T.alongGeometryFiberEquiv S K hK hext hk
      (T.restrictAlong_hconn_complement S K hK hext hconn) (Sum.inl j) a =
      Fintype.equivFin _ s := rfl
  change _ = T.alongGeometryFiniteSideEquiv S K hK hext hk
    (T.restrictAlong_hconn_complement S K hK hext hconn) r
  simp only [alongGeometryFiniteSideEquiv, alongGeometrySideEquiv, Equiv.trans_apply]
  rw [hf]
  simp only [Equiv.sigmaCongrRight_apply, hp]
  apply (Equiv.sigmaCongrLeft'
    (β := fun b => Fin ((T.alongPieceGeometry S K hK hext hk
      (T.restrictAlong_hconn_complement S K hK hext hconn) b).torusCount))
    (T.alongGeometryIndexEquiv S)).symm.injective
  rw [Equiv.symm_apply_apply]
  exact T.keptPortsGeometryPortEquiv_sigma S K hK hext hk hconn j _ _ s



def contractAlongKeptOwnedSideEquiv {i : Fin T.components.count} (hi : i ∉ S) :
    T.OwnedSide i ≃ (T.contractAlong S K hK hext hk hconn).OwnedSide
      (T.contractAlongKeptIndex S K hK hext hk hconn hi) := by
  let j := T.subIndexOf Sᶜ (Finset.mem_compl.mpr hi)
  have hj : T.subIndex Sᶜ j = i := T.subIndex_subIndexOf Sᶜ (Finset.mem_compl.mpr hi)
  exact (T.keptPortsOwnedIndexEquiv hj.symm).trans
    (T.keptPortsAtOwnedSideEquiv S K hK hext hk hconn j)

theorem contractAlongKeptOwnedSideEquiv_collar {i : Fin T.components.count} (hi : i ∉ S)
    (s : T.OwnedSide i) {p : Torus × EuclideanHalfSpace 1} (hp : p ∈ halfCollarSource) :
    (T.contractAlong S K hK hext hk hconn).pieceCollar
      (T.contractAlongKeptIndex S K hK hext hk hconn hi)
      (T.contractAlongKeptOwnedSideEquiv S K hK hext hk hconn hi s) p =
      T.contractAlongKeptDiffeomorph S K hK hext hk hconn hi (T.pieceCollar i s p) := by
  rw [← keptPortsDiffeomorph_eq]
  let j := T.subIndexOf Sᶜ (Finset.mem_compl.mpr hi)
  have hj : T.subIndex Sᶜ j = i := T.subIndex_subIndexOf Sᶜ (Finset.mem_compl.mpr hi)
  change (T.contractAlong S K hK hext hk hconn).pieceCollar j.castSucc
    (T.keptPortsAtOwnedSideEquiv S K hK hext hk hconn j
      (T.keptPortsOwnedIndexEquiv hj.symm s)) p = _
  rw [T.keptPortsAtOwnedSideEquiv_collar S K hK hext hk hconn j _ hp,
    keptPortsIndexDiffeomorph_collar]
  rfl

def contractAlongKeptRetainedSide {i : Fin T.components.count} (hi : i ∉ S)
    (s : T.OwnedSide i) : T.AlongLedgerRetainedSide K := by
  refine ⟨s.val, ?_⟩
  intro k hkK
  have hout : T.sidePiece s.val ∉ S := s.property.symm ▸ hi
  constructor
  · intro he
    apply hout
    rw [he]
    exact (hK k hkK).1
  · intro he
    apply hout
    rw [he]
    exact (hK k hkK).2

theorem contractAlongKeptOwnedSideEquiv_label {i : Fin T.components.count} (hi : i ∉ S)
    (s : T.OwnedSide i) :
    (T.alongCutSystem S K hK hext hk
      (T.restrictAlong_hconn_complement S K hK hext hconn)).sideOf
      (T.contractAlongKeptOwnedSideEquiv S K hK hext hk hconn hi s).val =
    T.alongGeometryFiniteSideEquiv S K hK hext hk
      (T.restrictAlong_hconn_complement S K hK hext hconn)
      (T.contractAlongKeptRetainedSide S K hK hi s) := by
  let j := T.subIndexOf Sᶜ (Finset.mem_compl.mpr hi)
  have hj : T.subIndex Sᶜ j = i := T.subIndex_subIndexOf Sᶜ (Finset.mem_compl.mpr hi)
  change (T.alongCutSystem S K hK hext hk
    (T.restrictAlong_hconn_complement S K hK hext hconn)).sideOf
    (T.keptPortsAtOwnedSideEquiv S K hK hext hk hconn j
      (T.keptPortsOwnedIndexEquiv hj.symm s)).val = _
  rw [keptPortsAtOwnedSideEquiv_label]
  apply congrArg (T.alongGeometryFiniteSideEquiv S K hK hext hk
    (T.restrictAlong_hconn_complement S K hK hext hconn))
  apply Subtype.ext
  exact T.keptPortsOwnedIndexEquiv_val hj.symm s

theorem contractAlongKeptOwnedSideEquiv_left {i : Fin T.components.count} (hi : i ∉ S)
    (s : T.OwnedSide i) (c : Fin T.pairing.count) (hc : c ∉ K) (hs : s.val = .inl c) :
    (T.contractAlongKeptOwnedSideEquiv S K hK hext hk hconn hi s).val =
      .inl (Fintype.equivFin (T.AlongUnpairedSeam K) ⟨c, hc⟩) := by
  let A := T.alongCutSystem S K hK hext hk
    (T.restrictAlong_hconn_complement S K hK hext hconn)
  apply A.bijective_sideOf.injective
  rw [T.contractAlongKeptOwnedSideEquiv_label S K hK hext hk hconn hi s]
  change T.alongGeometryFiniteSideEquiv S K hK hext hk
    (T.restrictAlong_hconn_complement S K hK hext hconn)
    (T.contractAlongKeptRetainedSide S K hK hi s) =
    T.alongGeometryFiniteSideEquiv S K hK hext hk
      (T.restrictAlong_hconn_complement S K hK hext hconn)
      (T.alongLedgerSideSum K (.inl
        ((Fintype.equivFin (T.AlongUnpairedSeam K)).symm
          (Fintype.equivFin (T.AlongUnpairedSeam K) ⟨c, hc⟩), true)))
  rw [Equiv.symm_apply_apply]
  apply congrArg (T.alongGeometryFiniteSideEquiv S K hK hext hk
    (T.restrictAlong_hconn_complement S K hK hext hconn))
  exact Subtype.ext hs

theorem contractAlongKeptOwnedSideEquiv_right {i : Fin T.components.count} (hi : i ∉ S)
    (s : T.OwnedSide i) (c : Fin T.pairing.count) (hc : c ∉ K)
    (hs : s.val = .inr (.inl c)) :
    (T.contractAlongKeptOwnedSideEquiv S K hK hext hk hconn hi s).val =
      .inr (.inl (Fintype.equivFin (T.AlongUnpairedSeam K) ⟨c, hc⟩)) := by
  let A := T.alongCutSystem S K hK hext hk
    (T.restrictAlong_hconn_complement S K hK hext hconn)
  apply A.bijective_sideOf.injective
  rw [T.contractAlongKeptOwnedSideEquiv_label S K hK hext hk hconn hi s]
  change T.alongGeometryFiniteSideEquiv S K hK hext hk
    (T.restrictAlong_hconn_complement S K hK hext hconn)
    (T.contractAlongKeptRetainedSide S K hK hi s) =
    T.alongGeometryFiniteSideEquiv S K hK hext hk
      (T.restrictAlong_hconn_complement S K hK hext hconn)
      (T.alongLedgerSideSum K (.inl
        ((Fintype.equivFin (T.AlongUnpairedSeam K)).symm
          (Fintype.equivFin (T.AlongUnpairedSeam K) ⟨c, hc⟩), false)))
  rw [Equiv.symm_apply_apply]
  apply congrArg (T.alongGeometryFiniteSideEquiv S K hK hext hk
    (T.restrictAlong_hconn_complement S K hK hext hconn))
  exact Subtype.ext hs

theorem contractAlongKeptOwnedSideEquiv_external {i : Fin T.components.count} (hi : i ∉ S)
    (s : T.OwnedSide i) (e : Fin T.externalCount) (hs : s.val = .inr (.inr e)) :
    (T.contractAlongKeptOwnedSideEquiv S K hK hext hk hconn hi s).val = .inr (.inr e) := by
  let A := T.alongCutSystem S K hK hext hk
    (T.restrictAlong_hconn_complement S K hK hext hconn)
  apply A.bijective_sideOf.injective
  rw [T.contractAlongKeptOwnedSideEquiv_label S K hK hext hk hconn hi s]
  change T.alongGeometryFiniteSideEquiv S K hK hext hk
    (T.restrictAlong_hconn_complement S K hK hext hconn)
    (T.contractAlongKeptRetainedSide S K hK hi s) =
    T.alongGeometryFiniteSideEquiv S K hK hext hk
      (T.restrictAlong_hconn_complement S K hK hext hconn)
      (T.alongLedgerSideSum K (.inr e))
  apply congrArg (T.alongGeometryFiniteSideEquiv S K hK hext hk
    (T.restrictAlong_hconn_complement S K hK hext hconn))
  exact Subtype.ext hs


def contractAlongKeptTransfer {i : Fin T.components.count} (hi : i ∉ S) :
    PieceTransfer T i (T.contractAlong S K hK hext hk hconn)
      (T.contractAlongKeptIndex S K hK hext hk hconn hi) where
  map := T.contractAlongKeptDiffeomorph S K hK hext hk hconn hi
  side := T.contractAlongKeptOwnedSideEquiv S K hK hext hk hconn hi
  collar_eq := T.contractAlongKeptOwnedSideEquiv_collar S K hK hext hk hconn hi

theorem contractAlongKeptTransfer_oriented {i : Fin T.components.count} (hi : i ∉ S) :
    (T.contractAlongKeptTransfer S K hK hext hk hconn hi).map.preservesOrientation
      (componentCarrier T.cutCarrier T.components i).orientation
      (componentCarrier (T.contractAlong S K hK hext hk hconn).cutCarrier
        (T.contractAlong S K hK hext hk hconn).components
        (T.contractAlongKeptIndex S K hK hext hk hconn hi)).orientation :=
  T.contractAlongKeptDiffeomorph_oriented S K hK hext hk hconn hi


theorem contractAlongKeptTransfer_cutMap {i : Fin T.components.count} (hi : i ∉ S)
    (x : (componentCarrier T.cutCarrier T.components i).Carrier) :
    (T.contractAlong S K hK hext hk hconn).cutMap
      ((T.contractAlongKeptTransfer S K hK hext hk hconn hi).map x).val = T.cutMap x.val :=
  T.contractAlongKeptDiffeomorph_cutMap S K hK hext hk hconn hi x


end TorusPresentation

end GC.Seifert
