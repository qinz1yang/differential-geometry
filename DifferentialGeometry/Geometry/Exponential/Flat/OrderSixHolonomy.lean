import DifferentialGeometry.Geometry.Exponential.Flat.OrderThreeLineHolonomy

/-!
The square of an actual order-six rotation is a nontrivial order-three rotation, and every
inverse-normalizer relation transports to that square. Thus the actual free oriented lattice
deck normalizer branch has cyclic holonomy, with no supplied axis or cyclic classification.
-/

set_option autoImplicit false

noncomputable section

open Module

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem orderSix_square_cube_nontrivial (L : E3 ≃ₗᵢ[ℝ] E3) (ho : orderOf L = 6) :
    (L ^ 2) ^ 3 = 1 ∧ L ^ 2 ≠ 1 := by
  constructor
  · rw [← pow_mul]
    simpa only [ho] using pow_orderOf_eq_one L
  · intro he
    have hd := orderOf_dvd_of_pow_eq_one he
    norm_num [ho] at hd

theorem inverseNormalizer_square (K L : E3 ≃ₗᵢ[ℝ] E3)
    (hc : K * L * K⁻¹ = L ∨ K * L * K⁻¹ = L⁻¹) :
    K * L ^ 2 * K⁻¹ = L ^ 2 ∨ K * L ^ 2 * K⁻¹ = (L ^ 2)⁻¹ := by
  rcases hc with h | h
  · left
    have he := congrArg (fun T : E3 ≃ₗᵢ[ℝ] E3 => T ^ 2) h
    rw [conj_pow] at he
    exact he
  · right
    have he := congrArg (fun T : E3 ≃ₗᵢ[ℝ] E3 => T ^ 2) h
    rw [conj_pow, inv_pow] at he
    exact he

theorem affineFree_orderSix_normalizerHolonomy_isCyclic (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hpos : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap)
    (g : G) (ho : orderOf g.val.linearIsometryEquiv = 6)
    (hc : ∀ γ : G, γ.val.linearIsometryEquiv * g.val.linearIsometryEquiv *
      γ.val.linearIsometryEquiv⁻¹ = g.val.linearIsometryEquiv ∨
      γ.val.linearIsometryEquiv * g.val.linearIsometryEquiv *
        γ.val.linearIsometryEquiv⁻¹ = g.val.linearIsometryEquiv⁻¹) :
    IsCyclic (affineLinearHom.comp G.subtype).range := by
  obtain ⟨hp, hn⟩ := orderSix_square_cube_nontrivial g.val.linearIsometryEquiv ho
  have hsq : (g ^ 2).val.linearIsometryEquiv = g.val.linearIsometryEquiv ^ 2 :=
    map_pow (affineLinearHom.comp G.subtype) g 2
  have hp' : (g ^ 2).val.linearIsometryEquiv ^ 3 = 1 := by rw [hsq]; exact hp
  have hn' : (g ^ 2).val.linearIsometryEquiv ≠ 1 := by rw [hsq]; exact hn
  have hs (γ : G) : γ.val.linearIsometryEquiv * (g ^ 2).val.linearIsometryEquiv *
      γ.val.linearIsometryEquiv⁻¹ = (g ^ 2).val.linearIsometryEquiv ∨
      γ.val.linearIsometryEquiv * (g ^ 2).val.linearIsometryEquiv *
        γ.val.linearIsometryEquiv⁻¹ = (g ^ 2).val.linearIsometryEquiv⁻¹ := by
    rw [hsq]
    exact inverseNormalizer_square γ.val.linearIsometryEquiv g.val.linearIsometryEquiv (hc γ)
  exact affineFree_orderThree_normalizerHolonomy_isCyclic G b hb hfree hpos (g ^ 2) hp' hn' hs

end DifferentialGeometry.Geometry.FlatSurface
