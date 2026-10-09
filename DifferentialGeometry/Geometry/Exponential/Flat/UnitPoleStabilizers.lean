import DifferentialGeometry.Geometry.Exponential.Flat.UnitPoleAction
import DifferentialGeometry.Geometry.Exponential.Flat.FixedAxisCyclic

/-!
Every actual finite positive point-group pole stabilizer is cyclic, by its faithful fixed-axis
SO3 image. Actual nonidentity stabilizers and actual lattice rotation orders make its cardinal
exactly two, three, four or six, without an assumed stabilizer classification.
-/

set_option autoImplicit false

noncomputable section

open Module

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem finitePositive_unitPole_stabilizer_isCyclic (H : Subgroup (E3 ≃ₗᵢ[ℝ] E3))
    [instH : Finite H] (hpos : ∀ a : H, 0 < LinearMap.det a.val.toLinearMap)
    (x : unitPoleSet H) : IsCyclic (MulAction.stabilizer H x) := by
  let K := MulAction.stabilizer H x
  let J := K.map H.subtype
  let e : K ≃* J := K.equivMapOfInjective H.subtype Subtype.val_injective
  let instJ : Finite J := Finite.of_equiv K e.toEquiv
  have hposJ (g : J) : 0 < LinearMap.det g.val.toLinearMap := by
    obtain ⟨a, ha, he⟩ := g.property
    rw [← he]
    exact hpos a
  have hfixJ (g : J) : g.val x.val = x.val := by
    obtain ⟨a, ha, he⟩ := g.property
    rw [← he]
    have hx : a • x = x := ha
    exact congrArg Subtype.val hx
  have hxn : x.val ≠ 0 := by
    intro he
    have hn := x.property.1
    rw [he, norm_zero] at hn
    norm_num at hn
  let instCyclic : IsCyclic J := finitePositive_fixedAxis_isCyclic J hposJ x.val hxn hfixJ
  exact isCyclic_of_injective e.toMonoidHom e.injective

theorem affineFree_unitPole_stabilizer_order_cases (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hpos : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap)
    (x : unitPoleSet (affineLinearHom.comp G.subtype).range) :
    Nat.card (MulAction.stabilizer (affineLinearHom.comp G.subtype).range x) = 2 ∨
    Nat.card (MulAction.stabilizer (affineLinearHom.comp G.subtype).range x) = 3 ∨
    Nat.card (MulAction.stabilizer (affineLinearHom.comp G.subtype).range x) = 4 ∨
    Nat.card (MulAction.stabilizer (affineLinearHom.comp G.subtype).range x) = 6 := by
  let H := (affineLinearHom.comp G.subtype).range
  let S := MulAction.stabilizer H x
  have hposH (a : H) : 0 < LinearMap.det a.val.toLinearMap := by
    obtain ⟨γ, hγ⟩ := a.property
    rw [← hγ]
    exact hpos γ
  let instCyclic : IsCyclic S := finitePositive_unitPole_stabilizer_isCyclic H hposH x
  obtain ⟨hnorm, a, ha, hfix⟩ := x.property
  have ham : a ∈ S := Subtype.ext hfix
  let instNontrivial : Nontrivial S :=
    ⟨⟨⟨a, ham⟩, 1, by intro he; exact ha (congrArg Subtype.val he)⟩⟩
  let instFintypeS : Fintype S := Fintype.ofFinite S
  have hcard2 : 2 ≤ Nat.card S := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  obtain ⟨s, hs⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := S)
  let f : S →* (E3 ≃ₗᵢ[ℝ] E3) := H.subtype.comp S.subtype
  have hfinj : Function.Injective f := Subtype.val_injective.comp Subtype.val_injective
  obtain ⟨γ, hγ⟩ := s.val.property
  change γ.val.linearIsometryEquiv = s.val.val at hγ
  have horder : orderOf γ.val.linearIsometryEquiv = Nat.card S := by
    rw [hγ]
    exact (orderOf_injective f hfinj s).trans hs
  have hc := affineFree_linear_order_cases G b hb hfree γ (hpos γ)
  rw [horder] at hc
  rcases hc with h | h
  · omega
  · exact h

end DifferentialGeometry.Geometry.FlatSurface
