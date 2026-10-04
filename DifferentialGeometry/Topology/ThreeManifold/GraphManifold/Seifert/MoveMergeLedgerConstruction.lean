import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveMergeLedgerBoundary
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveMergeLedgerPieces
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveMergeLedgerAssembly
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveAbsorbLedgerCounting
import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.MoveAbsorbLedgerTransport

/-!
# Actual mixed product models after a selected contraction

The selected quotient is the last native component of contraction. Every other compact piece
is transported by its actual kept-component diffeomorphism. Protected seams and frozen pieces
retain their native finite ledgers, and the new product models are assembled with genuine germs.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open Set Function DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.Topology (componentCarrier)
open scoped Manifold ContDiff Topology
universe u
namespace GC.Seifert.RelativeNormalization

structure UncollaredProduct {Q : ConnectedClosedOrientedManifold.{u} 3}
    (T : TorusPresentation (NoCuts.carrier Q)) (i : Fin T.components.count) (k : ℕ) where
  base : PlanarBase.{u} k
  theta : (base.surface.Carrier × Circle)
    ≃ₘ⟮(SurfaceModel.model base.surface.kind).prod (𝓡 1), T.cutCarrier.model⟯ T.components.piece i
  card_owned : Fintype.card (T.OwnedSide i) = k

namespace MixedStage
variable {Q : ConnectedClosedOrientedManifold.{u} 3} (σ : MixedStage Q)

abbrev selectedContraction (j : Fin σ.toTorus.pairing.count) :
    TorusPresentation (NoCuts.carrier Q) :=
  σ.toTorus.contractAlong (σ.toTorus.seamPair j) {j} (σ.selectedInternal j)
    (TorusPresentation.externalPiece_not_mem_of_closed _ _)
    (σ.toTorus.cutCarrier_kind_of_pos j.pos) (σ.selectedCarrier_interior_connected j)

theorem selectedFrozenDisjoint (j : Fin σ.toTorus.pairing.count) (hj : j ∉ σ.prot) :
    Disjoint σ.frozen (σ.toTorus.seamPair j) := by
  classical
  exact Finset.disjoint_left.mpr fun i hi hS =>
    σ.not_mem_frozen_of_mem_seamPair hj hS hi

abbrev selectedFrozen (j : Fin σ.toTorus.pairing.count) (hj : j ∉ σ.prot) :
    Finset (Fin (σ.selectedContraction j).components.count) :=
  σ.toTorus.contractAlongFrozen (σ.toTorus.seamPair j) {j} (σ.selectedInternal j)
    (TorusPresentation.externalPiece_not_mem_of_closed _ _)
    (σ.toTorus.cutCarrier_kind_of_pos j.pos) (σ.selectedCarrier_interior_connected j)
    σ.frozen (σ.selectedFrozenDisjoint j hj)

abbrev selectedProtected (j : Fin σ.toTorus.pairing.count) :
    Finset (Fin (σ.selectedContraction j).pairing.count) :=
  σ.toTorus.contractAlongProtected {j} σ.prot

abbrev selectedKeptIndex (j : Fin σ.toTorus.pairing.count)
    {i : Fin σ.toTorus.components.count} (hi : i ∉ σ.toTorus.seamPair j) :
    Fin (σ.selectedContraction j).components.count :=
  σ.toTorus.contractAlongKeptIndex (σ.toTorus.seamPair j) {j} (σ.selectedInternal j)
    (TorusPresentation.externalPiece_not_mem_of_closed _ _)
    (σ.toTorus.cutCarrier_kind_of_pos j.pos) (σ.selectedCarrier_interior_connected j) hi

abbrev selectedKeptDiffeomorph (j : Fin σ.toTorus.pairing.count)
    {i : Fin σ.toTorus.components.count} (hi : i ∉ σ.toTorus.seamPair j) :=
  σ.toTorus.contractAlongKeptDiffeomorph (σ.toTorus.seamPair j) {j} (σ.selectedInternal j)
    (TorusPresentation.externalPiece_not_mem_of_closed _ _)
    (σ.toTorus.cutCarrier_kind_of_pos j.pos) (σ.selectedCarrier_interior_connected j) hi

abbrev selectedLastDiffeomorph (j : Fin σ.toTorus.pairing.count) :=
  σ.toTorus.contractAlongLastDiffeomorph (σ.toTorus.seamPair j) {j} (σ.selectedInternal j)
    (TorusPresentation.externalPiece_not_mem_of_closed _ _)
    (σ.toTorus.cutCarrier_kind_of_pos j.pos) (σ.selectedCarrier_interior_connected j)

def selectedContractionKind (j : Fin σ.toTorus.pairing.count) (k : ℕ) :
    Fin (σ.selectedContraction j).components.count → ℕ :=
  Fin.lastCases k (fun a => σ.kind (σ.toTorus.subIndex (σ.toTorus.seamPair j)ᶜ a))

theorem selectedFrozen_kept_iff (j : Fin σ.toTorus.pairing.count) (hj : j ∉ σ.prot)
    {i : Fin σ.toTorus.components.count} (hi : i ∉ σ.toTorus.seamPair j) :
    σ.selectedKeptIndex j hi ∈ σ.selectedFrozen j hj ↔ i ∈ σ.frozen := by
  have he : σ.toTorus.alongPieceIndex (σ.toTorus.seamPair j) i =
      σ.selectedKeptIndex j hi := by
        simp [TorusPresentation.alongPieceIndex, hi, selectedKeptIndex,
          TorusPresentation.contractAlongKeptIndex]
  rw [← he]
  exact σ.toTorus.alongPieceIndex_mem_contractAlongFrozen_iff
    (σ.toTorus.seamPair j) {j} (σ.selectedInternal j)
    (TorusPresentation.externalPiece_not_mem_of_closed _ _)
    (σ.toTorus.cutCarrier_kind_of_pos j.pos) (σ.selectedCarrier_interior_connected j)
    σ.frozen (σ.selectedFrozenDisjoint j hj) i

theorem selectedFrozen_not_last (j : Fin σ.toTorus.pairing.count) (hj : j ∉ σ.prot) :
    Fin.last (σ.toTorus.seamPair j)ᶜ.card ∉ σ.selectedFrozen j hj := by
  classical
  intro hi
  obtain ⟨i, _hi, he⟩ := Finset.mem_image.mp hi
  exact Fin.castSucc_ne_last _ he

theorem selectedContractionKind_mem (j : Fin σ.toTorus.pairing.count) (hj : j ∉ σ.prot)
    {k : ℕ} (hk : k ∈ ({1, 2, 3} : Finset ℕ))
    (i : Fin (σ.selectedContraction j).components.count) (hi : i ∉ σ.selectedFrozen j hj) :
    σ.selectedContractionKind j k i ∈ ({1, 2, 3} : Finset ℕ) := by
  revert hi
  refine Fin.lastCases ?_ (fun a => ?_) i
  · intro _hi
    simpa only [selectedContractionKind, Fin.lastCases_last] using hk
  · intro hi
    let z := σ.toTorus.subIndex (σ.toTorus.seamPair j)ᶜ a
    have hz : z ∉ σ.toTorus.seamPair j :=
      Finset.mem_compl.mp (σ.toTorus.subIndex_mem _ a)
    have he : σ.selectedKeptIndex j hz = a.castSucc := by
      change (σ.toTorus.subIndexOf _ _).castSucc = _
      rw [σ.toTorus.subIndexOf_subIndex]
    have hf : z ∉ σ.frozen := fun hf =>
      hi (he ▸ (σ.selectedFrozen_kept_iff j hj hz).mpr hf)
    simpa only [selectedContractionKind, Fin.lastCases_castSucc] using σ.kind_mem z hf

def selectedKeptProduct (j : Fin σ.toTorus.pairing.count) (hj : j ∉ σ.prot)
    {k : ℕ} (a : Fin (σ.toTorus.seamPair j)ᶜ.card)
    (hi : a.castSucc ∉ σ.selectedFrozen j hj) :
    UncollaredProduct (σ.selectedContraction j) a.castSucc
      (σ.selectedContractionKind j k a.castSucc) := by
  let z := σ.toTorus.subIndex (σ.toTorus.seamPair j)ᶜ a
  have hz : z ∉ σ.toTorus.seamPair j :=
    Finset.mem_compl.mp (σ.toTorus.subIndex_mem _ a)
  have he : σ.selectedKeptIndex j hz = a.castSucc := by
    change (σ.toTorus.subIndexOf _ _).castSucc = _
    rw [σ.toTorus.subIndexOf_subIndex]
  have hf : z ∉ σ.frozen := fun hf =>
    hi (he ▸ (σ.selectedFrozen_kept_iff j hj hz).mpr hf)
  let P := σ.piece z hf
  have e : (componentCarrier σ.toTorus.cutCarrier σ.toTorus.components z).Carrier ≃ₘ⟮
      (componentCarrier σ.toTorus.cutCarrier σ.toTorus.components z).model,
      (componentCarrier (σ.selectedContraction j).cutCarrier
        (σ.selectedContraction j).components (σ.selectedKeptIndex j hz)).model⟯
      (componentCarrier (σ.selectedContraction j).cutCarrier
        (σ.selectedContraction j).components (σ.selectedKeptIndex j hz)).Carrier :=
    σ.selectedKeptDiffeomorph j hz
  rw [he] at e
  simp only [selectedContractionKind, Fin.lastCases_castSucc]
  refine ⟨P.base, P.trivialization.trans e, ?_⟩
  have hc := σ.toTorus.card_contractAlong_ownedSide_kept
    (σ.toTorus.seamPair j) {j} (σ.selectedInternal j)
    (TorusPresentation.externalPiece_not_mem_of_closed _ _)
    (σ.toTorus.cutCarrier_kind_of_pos j.pos) (σ.selectedCarrier_interior_connected j) hz
  change Fintype.card ((σ.selectedContraction j).OwnedSide (σ.selectedKeptIndex j hz)) =
    Fintype.card (σ.toTorus.OwnedSide z) at hc
  rw [he] at hc
  exact hc.trans P.card_ownedSide


def selectedLastProduct (j : Fin σ.toTorus.pairing.count) (b : Bool) (hj : j ∉ σ.prot)
    (hsolid : σ.kind (σ.seamPiece j b) = 1) (hhost : 2 ≤ σ.kind (σ.hostPiece j b))
    {k : ℕ} (hkind : σ.kind (σ.hostPiece j b) = k + 1) (B : PlanarBase.{u} k)
    (theta : (B.surface.Carrier × Circle)
      ≃ₘ⟮(SurfaceModel.model B.surface.kind).prod (𝓡 1), (σ.selectedCarrier j).model⟯
        (σ.selectedCarrier j).Carrier) :
    UncollaredProduct (σ.selectedContraction j) (Fin.last (σ.toTorus.seamPair j)ᶜ.card) k := by
  refine ⟨B, theta.trans (σ.selectedLastDiffeomorph j), ?_⟩
  have hc := σ.toTorus.card_contractAlong_ownedSide_last
    (σ.toTorus.seamPair j) {j} (σ.selectedInternal j)
    (TorusPresentation.externalPiece_not_mem_of_closed _ _)
    (σ.toTorus.cutCarrier_kind_of_pos j.pos) (σ.selectedCarrier_interior_connected j)
  have hb := σ.card_selected_boundary j b hj hsolid hhost
  rw [hkind] at hb
  exact hc.trans (by omega)

def selectedUncollaredProduct (j : Fin σ.toTorus.pairing.count) (b : Bool) (hj : j ∉ σ.prot)
    (hsolid : σ.kind (σ.seamPiece j b) = 1) (hhost : 2 ≤ σ.kind (σ.hostPiece j b))
    {k : ℕ} (hkind : σ.kind (σ.hostPiece j b) = k + 1) (B : PlanarBase.{u} k)
    (theta : (B.surface.Carrier × Circle)
      ≃ₘ⟮(SurfaceModel.model B.surface.kind).prod (𝓡 1), (σ.selectedCarrier j).model⟯
        (σ.selectedCarrier j).Carrier)
    (i : Fin (σ.selectedContraction j).components.count) (hi : i ∉ σ.selectedFrozen j hj) :
    UncollaredProduct (σ.selectedContraction j) i (σ.selectedContractionKind j k i) := by
  revert hi
  refine Fin.lastCases ?_ (fun a => ?_) i
  · intro _hi
    simpa only [selectedContractionKind, Fin.lastCases_last] using
      σ.selectedLastProduct j b hj hsolid hhost hkind B theta
  · intro hi
    exact σ.selectedKeptProduct j hj a hi

def selectedProductModels (j : Fin σ.toTorus.pairing.count) (b : Bool) (hj : j ∉ σ.prot)
    (hsolid : σ.kind (σ.seamPiece j b) = 1) (hhost : 2 ≤ σ.kind (σ.hostPiece j b))
    {k : ℕ} (hk : k ∈ ({1, 2, 3} : Finset ℕ))
    (hkind : σ.kind (σ.hostPiece j b) = k + 1) (B : PlanarBase.{u} k)
    (theta : (B.surface.Carrier × Circle)
      ≃ₘ⟮(SurfaceModel.model B.surface.kind).prod (𝓡 1), (σ.selectedCarrier j).model⟯
        (σ.selectedCarrier j).Carrier) : MixedProductModels Q where
  T := σ.selectedContraction j
  prot := σ.selectedProtected j
  frozen := σ.selectedFrozen j hj
  kind := σ.selectedContractionKind j k
  kind_mem := σ.selectedContractionKind_mem j hj hk
  base i := (σ.selectedUncollaredProduct j b hj hsolid hhost hkind B theta i.val i.property).base
  theta i := (σ.selectedUncollaredProduct j b hj hsolid hhost hkind B theta i.val i.property).theta
  card_owned i :=
    (σ.selectedUncollaredProduct j b hj hsolid hhost hkind B theta i.val i.property).card_owned
  hyperbolic i hi := by
    let f := σ.toTorus.contractAlongFrozenEquiv (σ.toTorus.seamPair j) {j}
      (σ.selectedInternal j) (TorusPresentation.externalPiece_not_mem_of_closed _ _)
      (σ.toTorus.cutCarrier_kind_of_pos j.pos) (σ.selectedCarrier_interior_connected j)
      σ.frozen (σ.selectedFrozenDisjoint j hj)
    let z := f.symm ⟨i, hi⟩
    have hz : z.val ∉ σ.toTorus.seamPair j :=
      fun hS => Finset.disjoint_left.mp (σ.selectedFrozenDisjoint j hj) z.property hS
    have he : σ.selectedKeptIndex j hz = i :=
      congrArg Subtype.val (f.apply_symm_apply ⟨i, hi⟩)
    have e : (componentCarrier σ.toTorus.cutCarrier σ.toTorus.components z.val).Carrier ≃ₘ⟮
        (componentCarrier σ.toTorus.cutCarrier σ.toTorus.components z.val).model,
        (componentCarrier (σ.selectedContraction j).cutCarrier
          (σ.selectedContraction j).components (σ.selectedKeptIndex j hz)).model⟯
        (componentCarrier (σ.selectedContraction j).cutCarrier
          (σ.selectedContraction j).components (σ.selectedKeptIndex j hz)).Carrier :=
      σ.selectedKeptDiffeomorph j hz
    rw [he] at e
    obtain ⟨g, hg⟩ := σ.hyperbolic z.val z.property
    exact exists_transportComponentHyperbolicGeometry
      (T := σ.toTorus) (U := σ.selectedContraction j) e g hg
  left_prot c hi := by
    have hf := (σ.toTorus.contractAlong_leftPiece_mem_frozen_iff
      (σ.toTorus.seamPair j) {j} (σ.selectedInternal j)
      (TorusPresentation.externalPiece_not_mem_of_closed _ _)
      (σ.toTorus.cutCarrier_kind_of_pos j.pos) (σ.selectedCarrier_interior_connected j)
      σ.frozen (σ.selectedFrozenDisjoint j hj) c).mp hi
    exact (σ.toTorus.mem_contractAlongProtected {j} σ.prot c).mpr (σ.left_prot _ hf)
  right_prot c hi := by
    have hf := (σ.toTorus.contractAlong_rightPiece_mem_frozen_iff
      (σ.toTorus.seamPair j) {j} (σ.selectedInternal j)
      (TorusPresentation.externalPiece_not_mem_of_closed _ _)
      (σ.toTorus.cutCarrier_kind_of_pos j.pos) (σ.selectedCarrier_interior_connected j)
      σ.frozen (σ.selectedFrozenDisjoint j hj) c).mp hi
    exact (σ.toTorus.mem_contractAlongProtected {j} σ.prot c).mpr (σ.right_prot _ hf)

end MixedStage
end GC.Seifert.RelativeNormalization
