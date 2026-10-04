import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeTerminalBlocksFlip
import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeTerminalBlocksIncidence
import
DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Seifert.RelativeTerminalBlocksStars

/-!
# The actual initial family of a terminal mixed stage

The canonical actual flip places every nonfrozen solid endpoint on the left. The finite centers
with positive arm count give pairwise disjoint selected stars. Every nonfrozen solid piece lies
in one of these actual stars, so the remaining nonfrozen pieces are unfilled good block vertices.
Only the original protected injection and terminality assumptions are used.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint GC.GraphManifold
open scoped Manifold ContDiff Topology
universe u
namespace GC.Seifert.RelativeNormalization.MixedStage
variable {Q : ConnectedClosedOrientedManifold.{u} 3} (σ : MixedStage Q)

abbrev RelativeCentre :=
  {c : Fin σ.toTorus.components.count //
    c ∉ σ.frozen ∧ σ.kind c = 3 ∧ 0 < σ.relativeArmCount c}

instance relativeCentre_fintype : Fintype σ.RelativeCentre := by
  classical
  exact Subtype.fintype _

abbrev relativeFamilyData (ht : σ.IsTerminal) (c : σ.RelativeCentre) : SeifertData :=
  σ.relativeCentreData ht c.val c.property.1 c.property.2.1

theorem relativeFamilyData_good (ht : σ.IsTerminal) (c : σ.RelativeCentre) :
    GoodData.{u} (σ.relativeFamilyData ht c) :=
  σ.relativeCentreData_good ht c.val c.property.1 c.property.2.1

theorem relativeFamilyData_fillingCount_pos (ht : σ.IsTerminal) (c : σ.RelativeCentre) :
    0 < (σ.relativeFamilyData ht c).fillingCount :=
  lt_of_lt_of_eq c.property.2.2
    (σ.relativeCentreData_fillingCount ht c.val c.property.1 c.property.2.1).symm

def relativeFamilyGroup (ht : σ.IsTerminal) (c : σ.RelativeCentre) :
    SelectedStarGroup σ.toTorus (σ.relativeFamilyData ht c) :=
  σ.relativeCentreGroup ht c.val c.property.1 c.property.2.1

theorem relativeFamilyGroup_center (ht : σ.IsTerminal) (c : σ.RelativeCentre) :
    (σ.relativeFamilyGroup ht c).center = c.val := rfl

theorem relativeFamilyGroup_arm_kind (ht : σ.IsTerminal) (c : σ.RelativeCentre)
    (l : Fin (σ.relativeCentreData ht c.val c.property.1 c.property.2.1).fillingCount) :
    σ.kind (σ.toTorus.leftPiece ((σ.relativeFamilyGroup ht c).arm l)) = 1 :=
  (σ.relativeCentreArm ht c.val c.property.1 c.property.2.1 l).property.2.2

theorem relativeFamilyGroup_disjoint (ht : σ.IsTerminal) :
    Pairwise fun c c' : σ.RelativeCentre =>
      Disjoint (σ.relativeFamilyGroup ht c).set (σ.relativeFamilyGroup ht c').set := by
  classical
  intro c c' hcc
  apply Finset.disjoint_left.mpr
  intro i hi hi'
  let G := σ.relativeFamilyGroup ht c
  let H := σ.relativeFamilyGroup ht c'
  rcases G.mem_set hi with hc | ⟨l, hl⟩
  · rcases H.mem_set hi' with hc' | ⟨m, hm⟩
    · exact hcc (Subtype.ext (hc.symm.trans hc'))
    · have he := congrArg σ.kind (hc.symm.trans hm)
      have hbad : (3 : ℕ) = 1 := c.property.2.1.symm.trans
        (he.trans (σ.relativeFamilyGroup_arm_kind ht c' m))
      omega
  · rcases H.mem_set hi' with hc' | ⟨m, hm⟩
    · have he := congrArg σ.kind (hl.symm.trans hc')
      have hbad : (1 : ℕ) = 3 := (σ.relativeFamilyGroup_arm_kind ht c l).symm.trans
        (he.trans c'.property.2.1)
      omega
    · have he := G.side_eq_of_solid l (.inl (H.arm m)) (hm.symm.trans hl)
      have hj : H.arm m = G.arm l := Sum.inl_injective he
      have hh : c.val = c'.val :=
        (G.arm_right l).symm.trans ((congrArg σ.toTorus.rightPiece hj).symm.trans
          (H.arm_right m))
      exact hcc (Subtype.ext hh)

theorem relativeFamilyGroup_set_not_frozen
    (hInc : ∀ k : σ.ProtSeam, ∀ t,
      Function.Injective (FundamentalGroup.map (σ.toTorus.seamTorus k.val) t))
    (ht : σ.IsTerminal) (c : σ.RelativeCentre)
    (i : Fin σ.toTorus.components.count) (hi : i ∈ (σ.relativeFamilyGroup ht c).set) :
    i ∉ σ.frozen :=
  σ.selectedStar_set_not_frozen hInc (σ.relativeFamilyGroup ht c) c.property.1 i hi

theorem relativeFamilyGroup_selected_not_protected
    (hInc : ∀ k : σ.ProtSeam, ∀ t,
      Function.Injective (FundamentalGroup.map (σ.toTorus.seamTorus k.val) t))
    (ht : σ.IsTerminal) (c : σ.RelativeCentre) (j : Fin σ.toTorus.pairing.count)
    (hj : j ∈ (σ.relativeFamilyGroup ht c).selected) : j ∉ σ.prot :=
  σ.selectedStar_not_protected hInc (σ.relativeFamilyGroup ht c) j hj

theorem solidLeftFlip_right_not_one
    (hInc : ∀ k : σ.ProtSeam, ∀ t,
      Function.Injective (FundamentalGroup.map (σ.toTorus.seamTorus k.val) t))
    (hp : σ.prot.Nonempty) (j : Fin σ.toTorus.pairing.count)
    (hj : (σ.flip σ.solidLeftFlip).toTorus.rightPiece j ∉ (σ.flip σ.solidLeftFlip).frozen) :
    (σ.flip σ.solidLeftFlip).kind ((σ.flip σ.solidLeftFlip).toTorus.rightPiece j) ≠ 1 := by
  by_cases hf : σ.solidLeftFlip j = true
  · have hs : σ.toTorus.rightPiece j ∉ σ.frozen ∧
        σ.kind (σ.toTorus.rightPiece j) = 1 := of_decide_eq_true hf
    have hinner := σ.solid_seam_not_protected hInc false hs.1 hs.2
    have hh := σ.inner_solid_host_not_one hInc hp false hinner hs.2
    change σ.kind (if σ.solidLeftFlip j then σ.toTorus.leftPiece j
      else σ.toTorus.rightPiece j) ≠ 1
    change σ.kind (σ.toTorus.leftPiece j) ≠ 1 at hh
    simpa only [hf, ↓reduceIte] using hh
  · have he : (σ.flip σ.solidLeftFlip).toTorus.rightPiece j = σ.toTorus.rightPiece j := by
      change (if σ.solidLeftFlip j then σ.toTorus.leftPiece j
        else σ.toTorus.rightPiece j) = _
      exact ite_eq_right hf
    intro hk
    have hnon : σ.toTorus.rightPiece j ∉ σ.frozen := by simpa only [he, frozen_flip] using hj
    have hkind : σ.kind (σ.toTorus.rightPiece j) = 1 := by simpa only [he, kind_flip] using hk
    exact hf (decide_eq_true ⟨hnon, hkind⟩)

theorem solidLeftFlip_solid_in_family
    (hInc : ∀ k : σ.ProtSeam, ∀ t,
      Function.Injective (FundamentalGroup.map (σ.toTorus.seamTorus k.val) t))
    (ht : σ.IsTerminal) (hp : σ.prot.Nonempty)
    (i : Fin σ.toTorus.components.count) (hi : i ∉ (σ.flip σ.solidLeftFlip).frozen)
    (hk : (σ.flip σ.solidLeftFlip).kind i = 1) :
    ∃ c : (σ.flip σ.solidLeftFlip).RelativeCentre,
      i ∈ ((σ.flip σ.solidLeftFlip).relativeFamilyGroup
        (σ.flip_isTerminal σ.solidLeftFlip ht) c).set := by
  classical
  let τ := σ.flip σ.solidLeftFlip
  have htτ : τ.IsTerminal := σ.flip_isTerminal σ.solidLeftFlip ht
  have hIncτ := σ.flip_protected_injective σ.solidLeftFlip hInc
  have hpτ : τ.prot.Nonempty := hp
  have P : SolidTorusPiece τ.toTorus i := by
    have P := τ.piece i hi
    rw [hk] at P
    exact P
  let s := P.port 0
  obtain ⟨j, hj⟩ : ∃ j : Fin τ.toTorus.pairing.count, τ.toTorus.leftPiece j = i := by
    rcases hs : s.val with j | j | e
    · have ho := s.property
      rw [hs] at ho
      exact ⟨j, ho⟩
    · have ho := s.property
      rw [hs] at ho
      have he : τ.toTorus.rightPiece j = i := ho
      exact False.elim (σ.solidLeftFlip_right_not_one hInc hp j (he ▸ hi) (he ▸ hk))
    · exact Fin.elim0 (e.cast τ.toTorus.externalCount_eq_zero)
  have hleft : τ.seamPiece j true = i := hj
  have hinner : j ∉ τ.prot :=
    τ.solid_seam_not_protected hIncτ true (hleft ▸ hi) (hleft ▸ hk)
  have hc : τ.kind (τ.toTorus.rightPiece j) = 3 :=
    τ.terminal_inner_solid_host_eq_three hIncτ hpτ htτ true hinner (hleft ▸ hk)
  have hcf : τ.toTorus.rightPiece j ∉ τ.frozen := τ.hostPiece_not_mem_frozen hinner true
  let a : τ.RelativeArm (τ.toTorus.rightPiece j) := ⟨j, hinner, rfl, hj ▸ hk⟩
  have hpos : 0 < τ.relativeArmCount (τ.toTorus.rightPiece j) := by
    have : Nonempty (τ.RelativeArm (τ.toTorus.rightPiece j)) := ⟨a⟩
    exact Fintype.card_pos
  let c : τ.RelativeCentre := ⟨τ.toTorus.rightPiece j, hcf, hc, hpos⟩
  let G := τ.relativeFamilyGroup htτ c
  let l : Fin (τ.relativeArmCount c.val) := (τ.relativeArmEquiv c.val).symm a
  let m : Fin (τ.relativeCentreData htτ c.val c.property.1 c.property.2.1).fillingCount :=
    l.cast (τ.relativeCentreData_fillingCount htτ c.val c.property.1 c.property.2.1).symm
  have hm : τ.relativeCentreArm htτ c.val c.property.1 c.property.2.1 m = a := by
    simp only [relativeCentreArm, m, Fin.cast_cast, Fin.cast_eq_self, l,
      Equiv.apply_symm_apply]
  refine ⟨c, ?_⟩
  have him := G.solid_mem m
  change τ.toTorus.leftPiece
    (τ.relativeCentreArm htτ c.val c.property.1 c.property.2.1 m).val ∈ G.set at him
  rw [hm, hj] at him
  exact him

theorem solidLeftFlip_outside_family_not_one
    (hInc : ∀ k : σ.ProtSeam, ∀ t,
      Function.Injective (FundamentalGroup.map (σ.toTorus.seamTorus k.val) t))
    (ht : σ.IsTerminal) (hp : σ.prot.Nonempty)
    (i : Fin σ.toTorus.components.count) (hi : i ∉ (σ.flip σ.solidLeftFlip).frozen)
    (houtside : ∀ c : (σ.flip σ.solidLeftFlip).RelativeCentre,
      i ∉ ((σ.flip σ.solidLeftFlip).relativeFamilyGroup
        (σ.flip_isTerminal σ.solidLeftFlip ht) c).set) :
    (σ.flip σ.solidLeftFlip).kind i ≠ 1 := by
  intro hk
  obtain ⟨c, hc⟩ := σ.solidLeftFlip_solid_in_family hInc ht hp i hi hk
  exact houtside c hc

end GC.Seifert.RelativeNormalization.MixedStage
