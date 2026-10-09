import DifferentialGeometry.Geometry.Exponential.Flat.EightDihedralRelations
import DifferentialGeometry.Geometry.Exponential.Flat.DihedralFourTorsion
import DifferentialGeometry.Geometry.Exponential.Flat.LargeHolonomyReduction

/-!
An actual eight-element point subgroup supplies actual dihedral motions and hence torsion.
This excludes whole point groups of cardinal eight and twenty-four internally.
-/

set_option autoImplicit false

noncomputable section

open Module

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem affineFree_eight_subgroup_obstruction (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hpos : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap)
    (K : Subgroup (affineLinearHom.comp G.subtype).range) (hc : Nat.card K = 8) :
    False := by
  obtain ⟨q, r, k, hq, hr, hk2, hkr, _hgen, hfix, hflip⟩ :=
    affineFree_eight_subgroup_dihedral G b hb hfree hpos K hc
  let H := (affineLinearHom.comp G.subtype).range
  let rho : K →* (E3 ≃ₗᵢ[ℝ] E3) := H.subtype.comp K.subtype
  have hrho : Function.Injective rho :=
    Subtype.val_injective.comp Subtype.val_injective
  have horder : orderOf (rho r) = 4 := (orderOf_injective rho hrho r).trans hr
  obtain ⟨g, hg⟩ := r.val.property
  change g.val.linearIsometryEquiv = rho r at hg
  obtain ⟨γ, hγ⟩ := k.val.property
  change γ.val.linearIsometryEquiv = rho k at hγ
  have hγ2 : γ.val.linearIsometryEquiv ^ 2 = 1 := by
    rw [hγ]
    simpa only [map_pow, map_one] using congrArg rho hk2
  have hconj : γ.val.linearIsometryEquiv * g.val.linearIsometryEquiv *
      γ.val.linearIsometryEquiv⁻¹ = g.val.linearIsometryEquiv⁻¹ := by
    rw [hγ, hg]
    simpa only [map_mul, map_inv] using congrArg rho hkr
  have hgq : g.val.linearIsometryEquiv q = q := by rw [hg]; exact hfix
  have hγq : γ.val.linearIsometryEquiv q = -q := by rw [hγ]; exact hflip
  exact affineFree_dihedralFour_obstruction G b hb hfree g γ
    (by rw [hg]; exact horder) (hpos g) (hpos γ) hγ2 hconj q hq hgq hγq

theorem affineFree_card_eight_obstruction (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hpos : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap)
    (hc : Nat.card (affineLinearHom.comp G.subtype).range = 8) : False := by
  apply affineFree_eight_subgroup_obstruction G b hb hfree hpos ⊤
  simpa only [Subgroup.card_top] using hc

theorem affineFree_card_twentyFour_obstruction (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hpos : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap)
    (hc : Nat.card (affineLinearHom.comp G.subtype).range = 24) : False := by
  obtain ⟨K, _hn, hcard, _h2⟩ := affineFree_card_twentyFour_normalEight G b hb hfree hpos hc
  exact affineFree_eight_subgroup_obstruction G b hb hfree hpos K hcard

end DifferentialGeometry.Geometry.FlatSurface
