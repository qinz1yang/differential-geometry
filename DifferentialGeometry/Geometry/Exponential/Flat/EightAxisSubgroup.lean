import DifferentialGeometry.Geometry.Exponential.Flat.EightHolonomyAxis
import DifferentialGeometry.Geometry.Exponential.Flat.LineHolonomySubgroup

/-!
The actual eight-element point subgroup has a cyclic normal four-element axis stabilizer
of index two. The internally constructed unoriented line bounds the index, and actual
crystallographic generator orders exclude a cyclic eight-element stabilizer.
-/

set_option autoImplicit false

noncomputable section

open Module

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem faithful_cyclic_holonomy_card_cases (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hpos : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap)
    (A : Type*) [instA : Group A] [instC : IsCyclic A]
    (rho : A →* (affineLinearHom.comp G.subtype).range) (hrho : Function.Injective rho) :
    Nat.card A = 1 ∨ Nat.card A = 2 ∨ Nat.card A = 3 ∨ Nat.card A = 4 ∨ Nat.card A = 6 := by
  let H := (affineLinearHom.comp G.subtype).range
  let f : A →* (E3 ≃ₗᵢ[ℝ] E3) := H.subtype.comp rho
  have hf : Function.Injective f := Subtype.val_injective.comp hrho
  obtain ⟨a, ha⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := A)
  obtain ⟨γ, hγ⟩ := (rho a).property
  change γ.val.linearIsometryEquiv = f a at hγ
  have hord : orderOf γ.val.linearIsometryEquiv = Nat.card A := by
    rw [hγ]
    exact (orderOf_injective f hf a).trans ha
  have hcases := affineFree_linear_order_cases G b hb hfree γ (hpos γ)
  rw [hord] at hcases
  exact hcases

theorem affineFree_eight_subgroup_cyclicIndexTwo (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hpos : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap)
    (K : Subgroup (affineLinearHom.comp G.subtype).range) (hc : Nat.card K = 8) :
    ∃ (q : E3) (S : Subgroup K), q ≠ 0 ∧ IsCyclic S ∧ S.Normal ∧
      Nat.card S = 4 ∧ S.index = 2 ∧ ∀ a : K, a ∈ S ↔ a.val.val q = q := by
  obtain ⟨q, hq, hline⟩ := affineFree_eight_subgroup_axis G b hb hfree hpos K hc
  let H := (affineLinearHom.comp G.subtype).range
  let rhoL := H.subtype.comp K.subtype
  have hrhoL : Function.Injective rhoL :=
    Subtype.val_injective.comp Subtype.val_injective
  have hposK (a : K) : 0 < LinearMap.det a.val.val.toLinearMap := by
    obtain ⟨γ, hγ⟩ := a.val.property
    change γ.val.linearIsometryEquiv = a.val.val at hγ
    rw [← hγ]
    exact hpos γ
  let instAction : MulAction K E3 :=
    { smul := fun a x => a.val.val x
      one_smul := by intro x; rfl
      mul_smul := by intro a d x; rfl }
  let S := MulAction.stabilizer K q
  have hS (a : K) : a ∈ S ↔ a.val.val q = q := Iff.rfl
  let J := S.map rhoL
  let e : S ≃* J := S.equivMapOfInjective rhoL hrhoL
  let instJ : Finite J := Finite.of_equiv S e.toEquiv
  have hpJ (a : J) : 0 < LinearMap.det a.val.toLinearMap := by
    obtain ⟨d, hd, he⟩ := a.property
    rw [← he]
    change 0 < LinearMap.det d.val.val.toLinearMap
    exact hposK d
  have hfixJ (a : J) : a.val q = q := by
    obtain ⟨d, hd, he⟩ := a.property
    rw [← he]
    change d.val.val q = q
    exact (hS d).mp hd
  let instCyclicJ : IsCyclic J := finitePositive_fixedAxis_isCyclic J hpJ q hq hfixJ
  let instCyclicS : IsCyclic S := isCyclic_of_injective e.toMonoidHom e.injective
  have hnormal : S.Normal := by
    constructor
    intro n hn g
    have hnq := (hS n).mp hn
    have hninv : n.val.val ((g⁻¹).val.val q) = (g⁻¹).val.val q := by
      rcases hline g⁻¹ with h | h
      · rw [h, hnq]
      · rw [h, map_neg, hnq]
    change g.val.val (n.val.val (g.val.val.symm q)) = q
    change n.val.val (g.val.val.symm q) = g.val.val.symm q at hninv
    rw [hninv, g.val.val.apply_symm_apply]
  have hindex : S.index ≤ 2 := by
    change (MulAction.stabilizer K q).index ≤ 2
    rw [MulAction.index_stabilizer]
    have horbit : MulAction.orbit K q ⊆ ({q, -q} : Set E3) := by
      intro x hx
      obtain ⟨a, rfl⟩ := hx
      change a.val.val q ∈ ({q, -q} : Set E3)
      simpa only [Set.mem_insert_iff, Set.mem_singleton_iff] using hline a
    have hpair : ({q, -q} : Set E3).ncard ≤ 2 := by
      simpa only [Set.ncard_singleton] using Set.ncard_insert_le q ({-q} : Set E3)
    exact (Set.ncard_le_ncard horbit).trans hpair
  let rhoS : S →* H := K.subtype.comp S.subtype
  have hrhoS : Function.Injective rhoS :=
    Subtype.val_injective.comp Subtype.val_injective
  have hcards := faithful_cyclic_holonomy_card_cases G b hb hfree hpos S rhoS hrhoS
  have hmul := S.card_mul_index
  rw [hc] at hmul
  have hi : S.index ≠ 0 := S.index_ne_zero_of_finite
  have htwo : S.index = 2 := by
    have hcases : S.index = 1 ∨ S.index = 2 := by omega
    rcases hcases with h | h
    · rw [h] at hmul
      rcases hcards with hs | hs | hs | hs | hs <;> omega
    · exact h
  have hcard : Nat.card S = 4 := by rw [htwo] at hmul; omega
  exact ⟨q, S, hq, instCyclicS, hnormal, hcard, htwo, hS⟩

end DifferentialGeometry.Geometry.FlatSurface
