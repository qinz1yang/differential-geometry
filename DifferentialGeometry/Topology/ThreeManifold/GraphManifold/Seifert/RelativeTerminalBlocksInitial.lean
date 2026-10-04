import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeTerminalBlocksAssembly
import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeTerminalBlocksFamily
import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeTerminalBlocksUnfilled

/-!
# The actual initial finite grouping of a terminal mixed stage

The canonical flip preserves the original frozen compact carriers and protected signed
seams. Its actual finite pants stars cover every nonfrozen solid vertex. Thus every remaining
nonfrozen compact piece has a zero-filling good block with its original full ports.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open GC.Topology (componentCarrier)
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.RelativeNormalization.MixedStage

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (σ : MixedStage Q)
  (hInc : ∀ k : σ.ProtSeam, ∀ t,
    Function.Injective (FundamentalGroup.map (σ.toTorus.seamTorus k.val) t))
  (ht : σ.IsTerminal) (hp : σ.prot.Nonempty)

abbrev relativeNormalizedStage : MixedStage Q := σ.flip σ.solidLeftFlip

abbrev relativeNormalizedTerminal : σ.relativeNormalizedStage.IsTerminal :=
  σ.flip_isTerminal σ.solidLeftFlip ht

abbrev relativeNormalizedInc : ∀ k : σ.relativeNormalizedStage.ProtSeam, ∀ t,
    Function.Injective
      (FundamentalGroup.map (σ.relativeNormalizedStage.toTorus.seamTorus k.val) t) :=
  σ.flip_protected_injective σ.solidLeftFlip hInc

def relativeInitialCentre : Fin (Fintype.card σ.relativeNormalizedStage.RelativeCentre) ≃
    σ.relativeNormalizedStage.RelativeCentre := (Fintype.equivFin _).symm

def relativeInitialTransfer (f : σ.Frozen) :
    PieceTransfer σ.toTorus f.val σ.relativeNormalizedStage.toTorus f.val where
  map := Diffeomorph.refl _ _ ∞
  side := σ.toTorus.ownedSideFlip σ.solidLeftFlip f.val
  collar_eq s p hp := by
    change (σ.toTorus.flipSeams σ.solidLeftFlip).pieceCollar f.val
      (σ.toTorus.ownedSideFlip σ.solidLeftFlip f.val s) p = σ.toTorus.pieceCollar f.val s p
    rw [σ.toTorus.pieceCollar_flip]

theorem relativeInitialRest_not_frozen (i : Fin σ.toTorus.components.count)
    (hi : ∀ f : σ.Frozen, f.val ≠ i) : i ∉ σ.frozen :=
  fun hf => hi ⟨i, hf⟩ rfl

include hInc ht hp in
theorem relativeInitialRest_not_one (i : Fin σ.toTorus.components.count)
    (hi : ∀ f : σ.Frozen, f.val ≠ i)
    (houtside : ∀ a : Fin (Fintype.card σ.relativeNormalizedStage.RelativeCentre),
      i ∉ (σ.relativeNormalizedStage.relativeFamilyGroup (σ.relativeNormalizedTerminal ht)
        (σ.relativeInitialCentre a)).set) : σ.kind i ≠ 1 :=
  σ.solidLeftFlip_outside_family_not_one hInc ht hp i
    (σ.relativeInitialRest_not_frozen i hi) (fun c => by
      obtain ⟨a, rfl⟩ := σ.relativeInitialCentre.surjective c
      exact houtside a)

include hInc ht hp

open Classical in
def relativeInitialGrouping : RelativeGrouping σ σ.relativeNormalizedStage.toTorus
    (Fintype.card σ.relativeNormalizedStage.RelativeCentre) where
  data a := σ.relativeNormalizedStage.relativeFamilyData (σ.relativeNormalizedTerminal ht)
    (σ.relativeInitialCentre a)
  group a := σ.relativeNormalizedStage.relativeFamilyGroup (σ.relativeNormalizedTerminal ht)
    (σ.relativeInitialCentre a)
  arm_pos a := σ.relativeNormalizedStage.relativeFamilyData_fillingCount_pos
    (σ.relativeNormalizedTerminal ht) (σ.relativeInitialCentre a)
  good a := σ.relativeNormalizedStage.relativeFamilyData_good
    (σ.relativeNormalizedTerminal ht) (σ.relativeInitialCentre a)
  disjoint a b hab := σ.relativeNormalizedStage.relativeFamilyGroup_disjoint
    (σ.relativeNormalizedTerminal ht) (fun he => hab (σ.relativeInitialCentre.injective he))
  protectedIndex := ⟨Subtype.val, Subtype.val_injective⟩
  protected_seam := σ.solidLeftFlip_protected_seam hInc
  protected_matching := σ.solidLeftFlip_protected_matching hInc
  protected_outside j a hj := σ.relativeNormalizedStage.relativeFamilyGroup_selected_not_protected
    (σ.relativeNormalizedInc hInc) (σ.relativeNormalizedTerminal ht) (σ.relativeInitialCentre a)
    j.val hj j.property
  frozen := ⟨Subtype.val, Subtype.val_injective⟩
  transfer := σ.relativeInitialTransfer
  oriented f := by
    change (Diffeomorph.refl σ.toTorus.cutCarrier.model
      (σ.toTorus.components.piece f.val) ∞).preservesOrientation _ _
    exact Diffeomorph.preservesOrientation_refl
      (componentCarrier σ.toTorus.cutCarrier σ.toTorus.components f.val).orientation
  cutMap f x := by
    change σ.toTorus.flipReconstruction σ.solidLeftFlip
      ((flipPairing σ.toTorus.pairing σ.solidLeftFlip).quotientMap x.val) = _
    exact σ.toTorus.flipReconstruction_apply σ.solidLeftFlip x.val
  frozen_outside f a hf := σ.relativeNormalizedStage.relativeFamilyGroup_set_not_frozen
    (σ.relativeNormalizedInc hInc) (σ.relativeNormalizedTerminal ht) (σ.relativeInitialCentre a)
    f.val hf f.property
  rest i houtside hi :=
    ⟨σ.relativeNormalizedStage.unfilledPieceBlock i (σ.relativeInitialRest_not_frozen i hi)
      (σ.relativeInitialRest_not_one hInc ht hp i hi houtside),
      goodData_productData _ _
        (σ.relativeNormalizedStage.unfilled_kind_bounds i (σ.relativeInitialRest_not_frozen i hi)
          (σ.relativeInitialRest_not_one hInc ht hp i hi houtside)).1
        (σ.relativeNormalizedStage.unfilled_kind_bounds i (σ.relativeInitialRest_not_frozen i hi)
          (σ.relativeInitialRest_not_one hInc ht hp i hi houtside)).2⟩

theorem relativeTerminal_exists_groupedPresentation :
    Nonempty (RelativeGroupedPresentation σ) :=
  RelativeGrouping.exists_groupedPresentation _ (σ.relativeInitialGrouping hInc ht hp)

end GC.Seifert.RelativeNormalization.MixedStage
