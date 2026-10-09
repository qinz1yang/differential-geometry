import DifferentialGeometry.Geometry.Exponential.Flat.NormalThreeNormalizer
import DifferentialGeometry.Geometry.Exponential.Flat.OrderThreeLineHolonomy

/-!
A six-element actual holonomy group of a free oriented affine lattice deck action is cyclic.
Cauchy and index two construct its actual normal order-three subgroup; lifting its generator
to the same deck group supplies the proved inverse-normalizer branch internally.
-/

set_option autoImplicit false

noncomputable section

open Module

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem affineFree_card_six_holonomy_isCyclic (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hpos : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap)
    (hc : Nat.card (affineLinearHom.comp G.subtype).range = 6) :
    IsCyclic (affineLinearHom.comp G.subtype).range := by
  let H := (affineLinearHom.comp G.subtype).range
  obtain ⟨r, hr, hn⟩ := exists_normal_three_of_card_six H hc
  have hr3 : r ^ 3 = 1 := by simpa only [hr] using pow_orderOf_eq_one r
  have hrn : r ≠ 1 := by intro he; rw [he, orderOf_one] at hr; norm_num at hr
  have hl3 : r.val ^ 3 = 1 := congrArg Subtype.val hr3
  have hnormalizer := normal_cube_zpowers_inverseNormalizer H r hr3 hrn hn
  obtain ⟨g, hgr⟩ := r.property
  change g.val.linearIsometryEquiv = r.val at hgr
  have hg3 : g.val.linearIsometryEquiv ^ 3 = 1 := by rw [hgr]; exact hl3
  have hgn : g.val.linearIsometryEquiv ≠ 1 := by
    intro he
    apply hrn
    apply Subtype.ext
    rw [← hgr]
    exact he
  have hconj (γ : G) : γ.val.linearIsometryEquiv * g.val.linearIsometryEquiv *
      γ.val.linearIsometryEquiv⁻¹ = g.val.linearIsometryEquiv ∨
      γ.val.linearIsometryEquiv * g.val.linearIsometryEquiv *
        γ.val.linearIsometryEquiv⁻¹ = g.val.linearIsometryEquiv⁻¹ := by
    let a : H := (affineLinearHom.comp G.subtype).rangeRestrict γ
    rcases hnormalizer a with he | he
    · left
      have hv := congrArg Subtype.val he
      change γ.val.linearIsometryEquiv * r.val * γ.val.linearIsometryEquiv⁻¹ = r.val at hv
      rw [← hgr] at hv
      exact hv
    · right
      have hv := congrArg Subtype.val he
      change γ.val.linearIsometryEquiv * r.val * γ.val.linearIsometryEquiv⁻¹ = r.val⁻¹ at hv
      rw [← hgr] at hv
      exact hv
  exact affineFree_orderThree_normalizerHolonomy_isCyclic G b hb hfree hpos g hg3 hgn hconj

end DifferentialGeometry.Geometry.FlatSurface
