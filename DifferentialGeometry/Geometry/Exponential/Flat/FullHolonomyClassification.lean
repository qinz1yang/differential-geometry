import DifferentialGeometry.Geometry.Exponential.Flat.EightHolonomyTorsion
import DifferentialGeometry.Geometry.Exponential.Flat.SmallHolonomyClassification

/-!
Actual finite positive holonomy of a free lattice affine group is cyclic or Klein four.
The eight-, twelve-, and twenty-four-element alternatives are excluded internally.
-/

set_option autoImplicit false

noncomputable section

open Module

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem affineFree_holonomy_card_le_six (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hpos : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap) :
    Nat.card (affineLinearHom.comp G.subtype).range ≤ 6 := by
  rcases affineFree_holonomy_card_cases G b hb hfree hpos with h | h | h | h | h | h | h | h
  · omega
  · omega
  · omega
  · omega
  · omega
  · exact False.elim (affineFree_card_eight_obstruction G b hb hfree hpos h)
  · exact False.elim (affineFree_card_twelve_impossible G b hb hfree hpos h)
  · exact False.elim (affineFree_card_twentyFour_obstruction G b hb hfree hpos h)

theorem affineFree_holonomy_classification (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hpos : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap) :
    IsCyclic (affineLinearHom.comp G.subtype).range ∨
      Nonempty ((affineLinearHom.comp G.subtype).range ≃*
        (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))) :=
  affineFree_small_holonomy_classification G b hb hfree hpos
    (affineFree_holonomy_card_le_six G b hb hfree hpos)

end DifferentialGeometry.Geometry.FlatSurface
