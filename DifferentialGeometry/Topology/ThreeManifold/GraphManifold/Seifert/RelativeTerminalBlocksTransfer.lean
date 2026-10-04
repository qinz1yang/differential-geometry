import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveMergeLedgerKeptPorts
import
  DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeTerminalBlocksSelected

/-!
# Passive selected stars under an actual selected contraction

A selected star disjoint from the contracted pieces retains its actual compact product and
solid pieces, full half collars, directed arm labels and filling slopes. Native kept indices
also identify its selected set exactly, for recursion through finite disjoint groups.
-/

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

noncomputable section

open Set Function DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert

namespace TorusPresentation

variable {W : CompactCarrier.{u}} (T : TorusPresentation W)
  (S : Finset (Fin T.components.count)) (K : Finset (Fin T.pairing.count))
  (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
  (hext : ∀ i, T.externalPiece i ∉ S) (hk : T.cutCarrier.kind = .withBoundary)
  (hconn : IsConnected ((T.restrictAlongCarrier S K hK hext).interior :
    Set (T.restrictAlongPairing S K hK).QuotientSpace))

theorem relativeKeptIndex_injective {i i' : Fin T.components.count}
    (hi : i ∉ S) (hi' : i' ∉ S)
    (he : T.contractAlongKeptIndex S K hK hext hk hconn hi =
      T.contractAlongKeptIndex S K hK hext hk hconn hi') : i = i' :=
  (T.subIndexOf_eq_iff _ _).mp (Fin.castSucc_injective _ he)

private theorem relativeTransfer_leftPiece (c : Fin T.pairing.count) (hc : c ∉ K)
    (hi : T.leftPiece c ∉ S) :
    (T.contractAlong S K hK hext hk hconn).leftPiece
      (Fintype.equivFin (T.AlongUnpairedSeam K) ⟨c, hc⟩) =
      T.contractAlongKeptIndex S K hK hext hk hconn hi := by
  let s : T.OwnedSide (T.leftPiece c) := ⟨.inl c, rfl⟩
  have hp := (T.contractAlongKeptOwnedSideEquiv S K hK hext hk hconn hi s).property
  have he := T.contractAlongKeptOwnedSideEquiv_left S K hK hext hk hconn hi s c hc rfl
  rw [he] at hp
  exact hp

private theorem relativeTransfer_rightPiece (c : Fin T.pairing.count) (hc : c ∉ K)
    (hi : T.rightPiece c ∉ S) :
    (T.contractAlong S K hK hext hk hconn).rightPiece
      (Fintype.equivFin (T.AlongUnpairedSeam K) ⟨c, hc⟩) =
      T.contractAlongKeptIndex S K hK hext hk hconn hi := by
  let s : T.OwnedSide (T.rightPiece c) := ⟨.inr (.inl c), rfl⟩
  have hp := (T.contractAlongKeptOwnedSideEquiv S K hK hext hk hconn hi s).property
  have he := T.contractAlongKeptOwnedSideEquiv_right S K hK hext hk hconn hi s c hc rfl
  rw [he] at hp
  exact hp

end TorusPresentation

namespace SelectedStarGroup

variable {W : CompactCarrier.{u}} {T : TorusPresentation W} {d : SeifertData}
  (G : SelectedStarGroup T d) (S : Finset (Fin T.components.count))
  (K : Finset (Fin T.pairing.count))
  (hK : ∀ k ∈ K, T.leftPiece k ∈ S ∧ T.rightPiece k ∈ S)
  (hext : ∀ i, T.externalPiece i ∉ S) (hk : T.cutCarrier.kind = .withBoundary)
  (hconn : IsConnected ((T.restrictAlongCarrier S K hK hext).interior :
    Set (T.restrictAlongPairing S K hK).QuotientSpace))
  (hG : Disjoint G.set S)

include hG in
theorem relativeTransfer_center_not_mem : G.center ∉ S :=
  Finset.disjoint_left.mp hG G.center_mem

include hG in
theorem relativeTransfer_solid_not_mem (l : Fin d.fillingCount) :
    T.leftPiece (G.arm l) ∉ S := Finset.disjoint_left.mp hG (G.solid_mem l)

include hK hG in
theorem relativeTransfer_arm_not_mem (l : Fin d.fillingCount) : G.arm l ∉ K :=
  fun hl => G.relativeTransfer_solid_not_mem S hG l (hK (G.arm l) hl).1

private theorem relativeTransfer_arm_right (l : Fin d.fillingCount) :
    (T.contractAlong S K hK hext hk hconn).rightPiece
      (Fintype.equivFin (T.AlongUnpairedSeam K)
        ⟨G.arm l, G.relativeTransfer_arm_not_mem S K hK hG l⟩) =
      T.contractAlongKeptIndex S K hK hext hk hconn
        (G.relativeTransfer_center_not_mem S hG) := by
  let s : T.OwnedSide G.center := ⟨.inr (.inl (G.arm l)), G.arm_right l⟩
  have hp := (T.contractAlongKeptOwnedSideEquiv S K hK hext hk hconn
    (G.relativeTransfer_center_not_mem S hG) s).property
  have he := T.contractAlongKeptOwnedSideEquiv_right S K hK hext hk hconn
    (G.relativeTransfer_center_not_mem S hG) s (G.arm l)
    (G.relativeTransfer_arm_not_mem S K hK hG l) rfl
  rw [he] at hp
  exact hp


def relativeSelectedTransfer : SelectedStarGroup (T.contractAlong S K hK hext hk hconn) d where
  center := T.contractAlongKeptIndex S K hK hext hk hconn
    (G.relativeTransfer_center_not_mem S hG)
  product := G.product.transfer (T.contractAlongKeptTransfer S K hK hext hk hconn
    (G.relativeTransfer_center_not_mem S hG))
  arm l := Fintype.equivFin (T.AlongUnpairedSeam K)
    ⟨G.arm l, G.relativeTransfer_arm_not_mem S K hK hG l⟩
  solid l := ((G.solid l).transfer (T.contractAlongKeptTransfer S K hK hext hk hconn
    (G.relativeTransfer_solid_not_mem S hG l))).congrIndex
    (T.relativeTransfer_leftPiece S K hK hext hk hconn _ _
      (G.relativeTransfer_solid_not_mem S hG l)).symm
  arm_right l := G.relativeTransfer_arm_right S K hK hext hk hconn hG l
  arm_injective l l' he := G.arm_injective
    (congrArg Subtype.val ((Fintype.equivFin (T.AlongUnpairedSeam K)).injective he))
  solid_ne_center l := by
    rw [T.relativeTransfer_leftPiece S K hK hext hk hconn _ _
      (G.relativeTransfer_solid_not_mem S hG l)]
    intro he
    exact G.solid_ne_center l (T.relativeKeptIndex_injective S K hK hext hk hconn _ _ he)
  slope l := by
    have hm := T.contractAlong_retained_matching S K hK hext hk hconn
      ⟨G.arm l, G.relativeTransfer_arm_not_mem S K hK hG l⟩
    exact (congrArg (fun f => torusUnit f • meridianSlope) hm).trans (G.slope l)

theorem relativeSelectedTransfer_mem_set
    {j : Fin (T.contractAlong S K hK hext hk hconn).components.count}
    (hj : j ∈ (G.relativeSelectedTransfer S K hK hext hk hconn hG).set) :
    ∃ i, ∃ hi : i ∉ S, i ∈ G.set ∧
      j = T.contractAlongKeptIndex S K hK hext hk hconn hi := by
  rcases (G.relativeSelectedTransfer S K hK hext hk hconn hG).mem_set hj with h | ⟨l, h⟩
  · exact ⟨_, G.relativeTransfer_center_not_mem S hG, G.center_mem, h⟩
  · refine ⟨_, G.relativeTransfer_solid_not_mem S hG l, G.solid_mem l, h.trans ?_⟩
    exact T.relativeTransfer_leftPiece S K hK hext hk hconn _ _
      (G.relativeTransfer_solid_not_mem S hG l)

theorem relativeSelectedTransfer_index_mem_set {i : Fin T.components.count} (hi : i ∉ S)
    (h : i ∈ G.set) :
    T.contractAlongKeptIndex S K hK hext hk hconn hi ∈
      (G.relativeSelectedTransfer S K hK hext hk hconn hG).set := by
  rcases G.mem_set h with rfl | ⟨l, rfl⟩
  · exact (G.relativeSelectedTransfer S K hK hext hk hconn hG).center_mem
  · have hl := (G.relativeSelectedTransfer S K hK hext hk hconn hG).solid_mem l
    change (T.contractAlong S K hK hext hk hconn).leftPiece
      (Fintype.equivFin (T.AlongUnpairedSeam K)
        ⟨G.arm l, G.relativeTransfer_arm_not_mem S K hK hG l⟩) ∈ _ at hl
    rwa [T.relativeTransfer_leftPiece S K hK hext hk hconn _ _ hi] at hl

end SelectedStarGroup

end GC.Seifert
