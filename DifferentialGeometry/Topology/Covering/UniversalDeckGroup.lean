import DifferentialGeometry.Topology.Covering.DeckFixedPoint
import DifferentialGeometry.Topology.Covering.DeckAction

noncomputable section
open Set Function
open DifferentialGeometry.Geometry.Riemannian.Topology

namespace DifferentialGeometry.Topology.Covering

variable {B C : Type*} [TopologicalSpace B] [TopologicalSpace C]


def deckGroup (p : C → B) : Subgroup (C ≃ₜ C) where
  carrier := {F | ∀ x, p (F x) = p x}
  one_mem' _ := rfl
  mul_mem' hF hG x := (hF _).trans (hG x)
  inv_mem' {F} hF x := by
    have h := hF (F.symm x)
    simpa using h.symm


theorem deckGroup_eq_one_of_fixed_point [PreconnectedSpace C]
    {p : C → B} (hp : IsCoveringMap p) (F : deckGroup p) (x : C) (hx : F.val x = x) : F = 1 := by
  apply Subtype.ext
  apply Homeomorph.ext
  exact congrFun (deck_eq_id_of_fixed_point hp F.val F.val.continuous F.property x hx)

variable {X : Type*} [TopologicalSpace X] [Inhabited X] [LocallyPathConnectedSpace X]

def fundamentalGroupToDeck : FundamentalGroup X (default : X) →*
    deckGroup (UniversalCover.proj : UniversalCover X → X) where
  toFun a := ⟨{
    toEquiv := MulAction.toPerm a
    continuous_toFun := UniversalCover.loopShift_cont (FundamentalGroup.toPath a⁻¹)
    continuous_invFun := UniversalCover.loopShift_cont (FundamentalGroup.toPath (a⁻¹)⁻¹)
  }, UniversalCover.proj_deckAct a⟩
  map_one' := by
    apply Subtype.ext
    apply Homeomorph.ext
    intro x
    exact one_smul (FundamentalGroup X (default : X)) x
  map_mul' a b := by
    apply Subtype.ext
    apply Homeomorph.ext
    intro x
    exact mul_smul a b x


theorem fundamentalGroupToDeck_injective : Function.Injective (fundamentalGroupToDeck (X := X)) := by
  intro a b hab
  have h := congrArg (fun F : deckGroup (UniversalCover.proj : UniversalCover X → X) =>
    F.val (UniversalCover.basePoint (X := X))) hab
  have hpath : FundamentalGroup.toPath a⁻¹ = FundamentalGroup.toPath b⁻¹ := by
    have hh := (Sigma.mk.inj_iff.mp h).2
    have hq := eq_of_heq hh
    simpa only [fundamentalGroupToDeck, UniversalCover.deckAct, UniversalCover.loopShift,
      UniversalCover.basePoint, Path.Homotopic.Quotient.mk_refl, Path.Homotopic.Quotient.trans_refl] using hq
  have hi : a⁻¹ = b⁻¹ := congrArg FundamentalGroup.fromPath hpath
  exact inv_injective hi


theorem fundamentalGroupToDeck_surjective [SemilocallySimplyConnectedSpace X] :
    Function.Surjective (fundamentalGroupToDeck (X := X)) := by
  intro F
  let z := UniversalCover.basePoint (X := X)
  obtain ⟨a, ha⟩ := (UniversalCover.proj_eq_iff_smul z (F.val z)).mp (F.property z).symm
  refine ⟨a, ?_⟩
  apply Subtype.ext
  apply Homeomorph.ext
  have heq := UniversalCover.proj_isCoveringMap.eq_of_comp_eq
    (fundamentalGroupToDeck a).val.continuous F.val.continuous
    (funext (fun x => (UniversalCover.proj_deckAct a x).trans (F.property x).symm)) z ha
  exact congrFun heq


def fundamentalGroupEquivDeck [SemilocallySimplyConnectedSpace X] :
    FundamentalGroup X (default : X) ≃* deckGroup (UniversalCover.proj : UniversalCover X → X) :=
  MulEquiv.ofBijective fundamentalGroupToDeck
    ⟨fundamentalGroupToDeck_injective, fundamentalGroupToDeck_surjective⟩

end DifferentialGeometry.Topology.Covering
