import DifferentialGeometry.Geometry.Exponential.Flat.SixElementHolonomy
import DifferentialGeometry.Geometry.Exponential.Flat.HolonomyCardinality
import Mathlib.GroupTheory.SpecificGroups.KleinFour

/-!
A four-element group is cyclic or actually Klein four. Combined with the internally proved
six-element free affine case and actual holonomy cardinal cases, this dispatches the actual
cardinal-at-most-six branch without a cyclic or Klein classification premise.
-/

set_option autoImplicit false

noncomputable section

open Module

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem finite_card_four_classification (H : Type*) [instH : Group H] [instF : Finite H]
    (hc : Nat.card H = 4) :
    IsCyclic H ∨ Nonempty (H ≃* (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) := by
  classical
  by_cases htwo : ∀ g : H, g ^ 2 = 1
  · have hdiv : Monoid.exponent H ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one htwo
    rcases (Nat.dvd_prime Nat.prime_two).mp hdiv with h1 | h2
    · let instSubsingleton : Subsingleton H := Monoid.exp_eq_one_iff.mp h1
      exact Or.inl inferInstance
    · let instKlein : IsKleinFour H := ⟨hc, h2⟩
      let instTarget : IsKleinFour (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
        { card_four := by simp
          exponent_two := by simp [Monoid.exponent_prod] }
      exact Or.inr IsKleinFour.nonempty_mulEquiv
  · push Not at htwo
    obtain ⟨g, hg⟩ := htwo
    have hd := orderOf_dvd_natCard g
    rw [hc] at hd
    have hpos : 0 < orderOf g := Nat.pos_of_dvd_of_pos hd (by decide)
    have hle : orderOf g ≤ 4 := Nat.le_of_dvd (by decide) hd
    have hcases : orderOf g = 1 ∨ orderOf g = 2 ∨ orderOf g = 4 := by
      generalize hk : orderOf g = k at hd hpos hle ⊢
      interval_cases k <;> norm_num at hd <;> omega
    rcases hcases with h1 | h2 | h4
    · exact False.elim (hg (by rw [orderOf_eq_one_iff.mp h1, one_pow]))
    · exact False.elim (hg (by simpa only [h2] using pow_orderOf_eq_one g))
    · exact Or.inl (isCyclic_of_orderOf_eq_card g (h4.trans hc.symm))

theorem affineFree_small_holonomy_classification (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hpos : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap)
    (hsmall : Nat.card (affineLinearHom.comp G.subtype).range ≤ 6) :
    IsCyclic (affineLinearHom.comp G.subtype).range ∨
      Nonempty ((affineLinearHom.comp G.subtype).range ≃*
        (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) := by
  let H := (affineLinearHom.comp G.subtype).range
  rcases affineFree_holonomy_card_cases G b hb hfree hpos with h | h | h | h | h | h | h | h
  · exact Or.inl (isCyclic_of_orderOf_eq_card (1 : H) (by rw [orderOf_one, h]))
  · let instPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact Or.inl (isCyclic_of_prime_card (p := 2) h)
  · let instPrime : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact Or.inl (isCyclic_of_prime_card (p := 3) h)
  · exact finite_card_four_classification H h
  · exact Or.inl (affineFree_card_six_holonomy_isCyclic G b hb hfree hpos h)
  · omega
  · omega
  · omega

end DifferentialGeometry.Geometry.FlatSurface
