import DifferentialGeometry.Geometry.Exponential.Flat.NormalFourThreeTorsion
import DifferentialGeometry.Geometry.Exponential.Flat.ThreeHolonomyComplement

/-!
Actual free positive lattice affine holonomy cannot have twelve elements. A normal four-group
is incompatible with internally chosen cubic motion; the actual Burnside complement gives
that subgroup in order twelve and reduces order twenty-four to a normal eight-element group.
-/

set_option autoImplicit false

noncomputable section

open Module

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem affineFree_normal_four_threeDiv_obstruction (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hpos : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap)
    (K : Subgroup (affineLinearHom.comp G.subtype).range)
    [instK : Fintype K] [instN : K.Normal] (hc : Fintype.card K = 4)
    (h3 : 3 ∣ Nat.card (affineLinearHom.comp G.subtype).range) : False := by
  let H := (affineLinearHom.comp G.subtype).range
  let instF : Fintype H := Fintype.ofFinite H
  let instPrime : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd : 3 ∣ Fintype.card H := by
    rw [← Nat.card_eq_fintype_card]
    exact h3
  obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card 3 hd
  have hr3 : r ^ 3 = 1 := by simpa only [hr] using pow_orderOf_eq_one r
  have hrn : r ≠ 1 := by intro he; rw [he, orderOf_one] at hr; norm_num at hr
  obtain ⟨g, hgr⟩ := r.property
  change g.val.linearIsometryEquiv = r.val at hgr
  have hg3 : g.val.linearIsometryEquiv ^ 3 = 1 := by
    rw [hgr]
    exact congrArg Subtype.val hr3
  have hgn : g.val.linearIsometryEquiv ≠ 1 := by
    intro he
    apply hrn
    apply Subtype.ext
    rw [← hgr]
    exact he
  exact affineFree_normal_four_three_obstruction G b hb hfree hpos K hc g hg3 hgn

theorem affineFree_card_twelve_impossible (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hpos : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap)
    (hc : Nat.card (affineLinearHom.comp G.subtype).range = 12) : False := by
  obtain ⟨K, hn, hcard, _h2⟩ :=
    affineFree_large_holonomy_normalTwo_complement G b hb hfree hpos (Or.inl hc)
  rcases hcard with h | h
  · let instK : Fintype K := Fintype.ofFinite K
    let instN : K.Normal := hn
    have hK : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, h]
    exact affineFree_normal_four_threeDiv_obstruction G b hb hfree hpos K hK
      (by rw [hc]; norm_num)
  · have hd := K.card_subgroup_dvd_card
    rw [h, hc] at hd
    norm_num at hd

theorem affineFree_card_twentyFour_normalEight (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hpos : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap)
    (hc : Nat.card (affineLinearHom.comp G.subtype).range = 24) :
    ∃ K : Subgroup (affineLinearHom.comp G.subtype).range,
      K.Normal ∧ Nat.card K = 8 ∧ IsPGroup 2 K := by
  obtain ⟨K, hn, hcard, h2⟩ :=
    affineFree_large_holonomy_normalTwo_complement G b hb hfree hpos (Or.inr hc)
  rcases hcard with h | h
  · exfalso
    let instK : Fintype K := Fintype.ofFinite K
    let instN : K.Normal := hn
    have hK : Fintype.card K = 4 := by rw [← Nat.card_eq_fintype_card, h]
    exact affineFree_normal_four_threeDiv_obstruction G b hb hfree hpos K hK
      (by rw [hc]; norm_num)
  · exact ⟨K, hn, h, h2⟩

end DifferentialGeometry.Geometry.FlatSurface
