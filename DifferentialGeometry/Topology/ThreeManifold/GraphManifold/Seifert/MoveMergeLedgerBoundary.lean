import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveMergeLedgerLocal

/-!
# Connected selected carriers and their exact remaining boundary count

The two actual connected cut pieces meet in the quotient at the selected seam, so their selected
carrier has connected interior without a supplied product model. For a solid and host pair the
remaining boundary sides are exactly the host sides other than the selected side. Every side
of an unselected host self seam remains a distinct port.
-/

set_option autoImplicit false
noncomputable section
open Set Function
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
universe u
namespace GC.Seifert.RelativeNormalization.MixedStage
variable {Q : ConnectedClosedOrientedManifold.{u} 3} (σ : MixedStage Q)

private def selectedCarrierPieceMap (j : Fin σ.toTorus.pairing.count)
    (i : Fin σ.toTorus.components.count) (hi : i ∈ σ.toTorus.seamPair j) :
    σ.toTorus.components.piece i →
      (σ.toTorus.restrictAlongPairing (σ.toTorus.seamPair j) {j}
        (σ.selectedInternal j)).QuotientSpace :=
  fun x => (σ.toTorus.restrictAlongPairing (σ.toTorus.seamPair j) {j}
    (σ.selectedInternal j)).quotientMap
      ⟨x.val, σ.toTorus.piece_subset_subPiece (σ.toTorus.seamPair j) hi x.property⟩

private theorem selectedCarrierPieceMap_continuous (j : Fin σ.toTorus.pairing.count)
    (i : Fin σ.toTorus.components.count) (hi : i ∈ σ.toTorus.seamPair j) :
    Continuous (σ.selectedCarrierPieceMap j i hi) :=
  (σ.toTorus.restrictAlongPairing (σ.toTorus.seamPair j) {j}
    (σ.selectedInternal j)).quotientMap.continuous.comp
      (continuous_subtype_val.subtype_mk fun x =>
        σ.toTorus.piece_subset_subPiece (σ.toTorus.seamPair j) hi x.property)

theorem selectedCarrier_connected (j : Fin σ.toTorus.pairing.count) :
    ConnectedSpace (σ.selectedCarrier j).Carrier := by
  classical
  let S := σ.toTorus.seamPair j
  let K : Finset (Fin σ.toTorus.pairing.count) := {j}
  let hK := σ.selectedInternal j
  let P := σ.toTorus.restrictAlongPairing S K hK
  have hlS : σ.toTorus.leftPiece j ∈ S := σ.toTorus.left_mem_seamPair j
  have hrS : σ.toTorus.rightPiece j ∈ S := σ.toTorus.right_mem_seamPair j
  let f := σ.selectedCarrierPieceMap j (σ.toTorus.leftPiece j) hlS
  let g := σ.selectedCarrierPieceMap j (σ.toTorus.rightPiece j) hrS
  have hfc : IsConnected (Set.range f) := by
    let := σ.toTorus.components.connected (σ.toTorus.leftPiece j)
    exact isConnected_range
      (σ.selectedCarrierPieceMap_continuous j (σ.toTorus.leftPiece j) hlS)
  have hgc : IsConnected (Set.range g) := by
    let := σ.toTorus.components.connected (σ.toTorus.rightPiece j)
    exact isConnected_range
      (σ.selectedCarrierPieceMap_continuous j (σ.toTorus.rightPiece j) hrS)
  have hcov : Set.range f ∪ Set.range g = Set.univ := by
    apply Set.eq_univ_of_forall
    intro q
    obtain ⟨x, rfl⟩ := Quotient.exists_rep q
    obtain ⟨i, hi, hxi⟩ := (σ.toTorus.mem_subPiece S).mp x.property
    rcases σ.toTorus.eq_or_eq_of_mem_seamPair hi with rfl | rfl
    · exact Or.inl ⟨⟨x.val, hxi⟩, rfl⟩
    · exact Or.inr ⟨⟨x.val, hxi⟩, rfl⟩
  let a : Fin K.card := ⟨0, by simp [K]⟩
  have ha : (σ.toTorus.alongSeam K a).val = j := by
    exact Finset.mem_singleton.mp (σ.toTorus.alongSeam K a).property
  let x := P.leftParam a 1
  let y := P.rightParam a (P.matching a 1)
  have hx : x.val.val ∈ σ.toTorus.components.piece (σ.toTorus.leftPiece j) := by
    apply σ.toTorus.left_owned j
    have hh := x.property
    change x.val.val ∈ σ.toTorus.pairing.gluing.left
      (σ.toTorus.keptSeam S (σ.toTorus.alongKeptIndex S K hK a)).val at hh
    simpa only [σ.toTorus.keptSeam_alongKeptIndex, ha] using hh
  have hy : y.val.val ∈ σ.toTorus.components.piece (σ.toTorus.rightPiece j) := by
    apply σ.toTorus.right_owned j
    have hh := y.property
    change y.val.val ∈ σ.toTorus.pairing.gluing.right
      (σ.toTorus.keptSeam S (σ.toTorus.alongKeptIndex S K hK a)).val at hh
    simpa only [σ.toTorus.keptSeam_alongKeptIndex, ha] using hh
  have hxy : P.quotientMap x.val = P.quotientMap y.val := by
    apply Quotient.sound
    have hh := P.gluing.rel_of_mem_left x.property
    have he := congrArg Subtype.val (P.matching_eq a 1)
    exact he ▸ hh
  have hinter : (Set.range f ∩ Set.range g).Nonempty :=
    ⟨P.quotientMap x.val, ⟨⟨x.val.val, hx⟩, rfl⟩, ⟨⟨y.val.val, hy⟩, hxy.symm⟩⟩
  exact connectedSpace_iff_univ.mpr (hcov ▸ hfc.union hinter hgc)


theorem selectedCarrier_interior_connected (j : Fin σ.toTorus.pairing.count) :
    IsConnected ((σ.selectedCarrier j).interior :
      Set (σ.toTorus.restrictAlongPairing (σ.toTorus.seamPair j) {j}
        (σ.selectedInternal j)).QuotientSpace) := by
  let C := σ.selectedCarrier j
  let : ConnectedSpace C.Carrier := σ.selectedCarrier_connected j
  exact ⟨Manifold.dense_manifold_interior.nonempty,
    Manifold.isPreconnected_manifold_interior⟩

private theorem selectedBoundary_ne_pairSide (j : Fin σ.toTorus.pairing.count)
    (a : σ.toTorus.AlongBoundarySide (σ.toTorus.seamPair j) {j}) (b : Bool) :
    a.val ≠ σ.toTorus.pairSide j b := by
  intro he
  have hh := a.property.2
  rw [he] at hh
  cases b <;> simp [TorusPresentation.pairSide] at hh

private def selectedHostSide (j : Fin σ.toTorus.pairing.count) (b : Bool) :
    σ.toTorus.OwnedSide (σ.hostPiece j b) :=
  ⟨σ.toTorus.pairSide j (!b), by
    change σ.toTorus.sidePiece (σ.toTorus.pairSide j (!b)) = σ.seamPiece j (!b)
    exact σ.sidePiece_pairSide j (!b)⟩

def selectedBoundaryHostEquiv (j : Fin σ.toTorus.pairing.count) (b : Bool)
    (hj : j ∉ σ.prot) (hsolid : σ.kind (σ.seamPiece j b) = 1)
    (hne : σ.seamPiece j b ≠ σ.hostPiece j b) :
    σ.toTorus.AlongBoundarySide (σ.toTorus.seamPair j) {j} ≃
      {s : σ.toTorus.OwnedSide (σ.hostPiece j b) //
        s ≠ σ.selectedHostSide j b} := by
  classical
  have hc : Fintype.card (σ.toTorus.OwnedSide (σ.seamPiece j b)) = 1 :=
    (σ.card_ownedSide_eq_kind _ (σ.seamPiece_not_mem_frozen hj b)).trans hsolid
  let : Subsingleton (σ.toTorus.OwnedSide (σ.seamPiece j b)) :=
    Fintype.card_le_one_iff_subsingleton.mp hc.le
  have hsole (s : σ.toTorus.Side) (hs : σ.toTorus.sidePiece s = σ.seamPiece j b) :
      s = σ.toTorus.pairSide j b :=
    congrArg Subtype.val (Subsingleton.elim
      (⟨s, hs⟩ : σ.toTorus.OwnedSide (σ.seamPiece j b))
      ⟨σ.toTorus.pairSide j b, σ.sidePiece_pairSide j b⟩)
  have hhost (a : σ.toTorus.AlongBoundarySide (σ.toTorus.seamPair j) {j}) :
      σ.toTorus.sidePiece a.val = σ.hostPiece j b := by
    rcases (σ.mem_seamPair_iff j b _).mp a.property.1 with hs | hs
    · exact False.elim (σ.selectedBoundary_ne_pairSide j a b (hsole a.val hs))
    · exact hs
  refine
    { toFun := fun a => ⟨⟨a.val, hhost a⟩, fun he =>
        σ.selectedBoundary_ne_pairSide j a (!b) (congrArg Subtype.val he)⟩
      invFun := fun s => ⟨s.val.val, ?_, ?_⟩
      left_inv := fun a => Subtype.ext rfl
      right_inv := fun s => Subtype.ext (Subtype.ext rfl) }
  · exact (σ.mem_seamPair_iff j b _).mpr (Or.inr s.val.property)
  · have hsH : s.val.val ≠ σ.toTorus.pairSide j (!b) := by
      intro he
      exact s.property (Subtype.ext he)
    have hsV : s.val.val ≠ σ.toTorus.pairSide j b := by
      intro he
      have hh := s.val.property
      rw [he, σ.sidePiece_pairSide] at hh
      exact hne hh
    have hn (beta : Bool) : s.val.val ≠ σ.toTorus.pairSide j beta := by
      have hb : beta = b ∨ beta = !b := by cases beta <;> cases b <;> simp
      rcases hb with rfl | rfl
      · exact hsV
      · exact hsH
    rcases hs : s.val.val with r | r | r
    · intro hr
      exact hn true (hs.trans (congrArg Sum.inl (Finset.mem_singleton.mp hr)))
    · intro hr
      exact hn false (hs.trans
        (congrArg (fun k => Sum.inr (Sum.inl k)) (Finset.mem_singleton.mp hr)))
    · exact Finset.mem_univ r

theorem card_selected_boundary (j : Fin σ.toTorus.pairing.count) (b : Bool)
    (hj : j ∉ σ.prot) (hsolid : σ.kind (σ.seamPiece j b) = 1)
    (hhost : 2 ≤ σ.kind (σ.hostPiece j b)) :
    Fintype.card (σ.toTorus.AlongBoundarySide (σ.toTorus.seamPair j) {j}) + 1 =
      σ.kind (σ.hostPiece j b) := by
  have hn : σ.seamPiece j b ≠ σ.hostPiece j b := by
    intro he
    rw [← he, hsolid] at hhost
    omega
  rw [Fintype.card_congr (σ.selectedBoundaryHostEquiv j b hj hsolid hn)]
  rw [Fintype.card_subtype_compl]
  have hone : Fintype.card {s : σ.toTorus.OwnedSide (σ.hostPiece j b) //
      s = σ.selectedHostSide j b} = 1 := Fintype.card_unique
  rw [hone, σ.card_ownedSide_eq_kind _ (σ.hostPiece_not_mem_frozen hj b)]
  omega

end GC.Seifert.RelativeNormalization.MixedStage
