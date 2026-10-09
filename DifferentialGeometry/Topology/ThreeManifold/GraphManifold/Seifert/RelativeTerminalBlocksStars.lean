import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeTerminalBlocksGroup
import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeTerminalBlocksProtected

/-!
# Derived actual stars of a terminal mixed stage

At a nonfrozen pants center, the inner seams with a solid left endpoint form a finite actual
star. Terminality makes their filling distances at least two. Primitive cone coordinates
give its actual selected Seifert block, whose grouped compact component is good, including
zero arms and zero ports. Host self seams are omitted from the selected arm set.
-/

set_option autoImplicit false

noncomputable section

open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology

universe u

namespace GC.Seifert.RelativeNormalization.MixedStage

variable {Q : ConnectedClosedOrientedManifold.{u} 3} (σ : MixedStage Q)

abbrev RelativeArm (c : Fin σ.toTorus.components.count) :=
  {j : Fin σ.toTorus.pairing.count // j ∉ σ.prot ∧ σ.toTorus.rightPiece j = c ∧
    σ.kind (σ.toTorus.leftPiece j) = 1}

instance relativeArm_fintype (c : Fin σ.toTorus.components.count) :
    Fintype (σ.RelativeArm c) := by
  classical
  exact Subtype.fintype _

def relativeArmCount (c : Fin σ.toTorus.components.count) : ℕ :=
  Fintype.card (σ.RelativeArm c)

def relativeArmEquiv (c : Fin σ.toTorus.components.count) :
    Fin (σ.relativeArmCount c) ≃ σ.RelativeArm c := (Fintype.equivFin _).symm

def relativeArmSide (c : Fin σ.toTorus.components.count) (j : σ.RelativeArm c) :
    σ.toTorus.OwnedSide c := ⟨.inr (.inl j.val), j.property.2.1⟩

theorem relativeArmSide_injective (c : Fin σ.toTorus.components.count) :
    Function.Injective (σ.relativeArmSide c) := by
  intro j k he
  exact Subtype.ext (Sum.inl_injective (Sum.inr_injective (congrArg Subtype.val he)))

theorem relativeArmCount_le_three (c : Fin σ.toTorus.components.count)
    (hi : c ∉ σ.frozen) (hc : σ.kind c = 3) : σ.relativeArmCount c ≤ 3 := by
  have hb := Fintype.card_le_of_injective (σ.relativeArmSide c) (σ.relativeArmSide_injective c)
  rw [(σ.piece c hi).card_ownedSide, hc] at hb
  exact hb

variable (ht : σ.IsTerminal) (c : Fin σ.toTorus.components.count)
  (hi : c ∉ σ.frozen) (hc : σ.kind c = 3)

def relativeArmSlope (l : Fin (σ.relativeArmCount c)) : PrimitiveSlope :=
  torusUnit (σ.toTorus.pairing.matching (σ.relativeArmEquiv c l).val) • meridianSlope

include ht hc in
theorem relativeArmSlope_distance (l : Fin (σ.relativeArmCount c)) :
    2 ≤ PrimitiveSlope.delta (σ.relativeArmSlope c l) fiberSlope := by
  let j := σ.relativeArmEquiv c l
  exact σ.terminal_inner_solid_distance_ge_two ht true j.property.1 j.property.2.2
    (by change σ.kind (σ.toTorus.rightPiece j.val) = 3; rw [j.property.2.1]; exact hc)

def relativeArmCone (l : Fin (σ.relativeArmCount c)) : ℕ × ℤ :=
  Classical.choose (exists_cone_of_two_le_delta _ (σ.relativeArmSlope_distance ht c hc l))

theorem relativeArmCone_spec (l : Fin (σ.relativeArmCount c)) :
    ∃ hp : Int.gcd ((σ.relativeArmCone ht c hc l).1 : ℤ)
        (σ.relativeArmCone ht c hc l).2 = 1,
      2 ≤ (σ.relativeArmCone ht c hc l).1 ∧
        σ.relativeArmSlope c l = PrimitiveSlope.mk
          (((σ.relativeArmCone ht c hc l).1 : ℤ), (σ.relativeArmCone ht c hc l).2) hp :=
  Classical.choose_spec (exists_cone_of_two_le_delta _ (σ.relativeArmSlope_distance ht c hc l))

def relativeCentreData : SeifertData :=
  coneData (σ.relativeArmCount c) (σ.relativeArmCount_le_three c hi hc)
    (σ.relativeArmCone ht c hc) (fun l => (σ.relativeArmCone_spec ht c hc l).2.1)
    (fun l => (σ.relativeArmCone_spec ht c hc l).1)

theorem relativeCentreData_fillingCount :
    (σ.relativeCentreData ht c hi hc).fillingCount = σ.relativeArmCount c :=
  coneData_fillingCount _ _ _ _ _

def relativeCentreArm (l : Fin (σ.relativeCentreData ht c hi hc).fillingCount) :
    σ.RelativeArm c :=
  σ.relativeArmEquiv c (l.cast (σ.relativeCentreData_fillingCount ht c hi hc))

def relativeCentreGroup : SelectedStarGroup σ.toTorus (σ.relativeCentreData ht c hi hc) where
  center := c
  product := by
    have P := σ.piece c hi
    rw [hc] at P
    exact P
  arm l := (σ.relativeCentreArm ht c hi hc l).val
  solid l := by
    let j := σ.relativeCentreArm ht c hi hc l
    have P := σ.piece (σ.toTorus.leftPiece j.val) (σ.seamPiece_not_mem_frozen j.property.1 true)
    rw [j.property.2.2] at P
    exact P
  arm_right l := (σ.relativeCentreArm ht c hi hc l).property.2.1
  arm_injective l k he := by
    have h := (σ.relativeArmEquiv c).injective (Subtype.ext he)
    exact Fin.cast_injective (σ.relativeCentreData_fillingCount ht c hi hc) h
  solid_ne_center l := by
    intro he
    have hs := (σ.relativeCentreArm ht c hi hc l).property.2.2
    rw [he, hc] at hs
    omega
  slope l := by
    refine (σ.relativeArmCone_spec ht c hc _).2.2.trans
      ((PrimitiveSlope.mk_eq_mk_iff _ _).mpr (Or.inl ?_))
    exact coneData_fillingSlope _ _ _ _ _ l

theorem relativeCentreData_good : GoodData.{u} (σ.relativeCentreData ht c hi hc) := by
  by_cases hm : σ.relativeArmCount c = 0
  · intro V B
    exact SeifertBlock.isGoodBlock_of_fillingCount_eq_zero B (by change 2 ≤ 3; norm_num)
      ((σ.relativeCentreData_fillingCount ht c hi hc).trans hm)
  · exact goodData_coneData _ _ (Nat.pos_of_ne_zero hm) _ _ _

theorem relativeCentreGroupBlock_isGood :
    ((σ.relativeCentreGroup ht c hi hc).relativeSelectedGroupBlock
      (TorusPresentation.externalPiece_not_mem_of_closed _ _)
      (σ.toTorus.cutCarrier_kind_of_pos
        (σ.selectedStar_pairing_pos (σ.relativeCentreGroup ht c hi hc)))).block.IsGoodBlock := by
  exact σ.relativeCentreData_good ht c hi hc _ _

end GC.Seifert.RelativeNormalization.MixedStage
