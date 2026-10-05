import DifferentialGeometry.Geometry.Exponential.Flat.RotationNormalizerAxis

/-!
A crystallographic positive rotation with a nonzero fixed vector can reverse a nonzero
vector only when it is an involution. Actual free lattice deck motions supply the fixed
screw vector internally, so every line-reversing point motion has square one.
-/

set_option autoImplicit false

noncomputable section

open Module

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem realVector_eq_neg_zero (x : E3) (he : x = -x) : x = 0 := by
  have hs : (2 : ℝ) • x = 0 := by
    rw [two_smul]
    exact add_eq_zero_iff_eq_neg.mpr he
  exact (smul_eq_zero.mp hs).resolve_left (by norm_num)

theorem crystallographic_lineReverse_involution (L : E3 ≃ₗᵢ[ℝ] E3)
    (ho : orderOf L = 1 ∨ orderOf L = 2 ∨ orderOf L = 3 ∨ orderOf L = 4 ∨ orderOf L = 6)
    (hpos : 0 < LinearMap.det L.toLinearMap)
    (r q : E3) (hr : r ≠ 0) (hfix : L r = r) (hq : q ≠ 0) (hflip : L q = -q) :
    L ^ 2 = 1 := by
  have hq2 : (L ^ 2) q = q := by
    change L (L q) = q
    rw [hflip, map_neg, hflip, neg_neg]
  have hr2 : (L ^ 2) r = r := by change L (L r) = r; rw [hfix, hfix]
  have hpos2 : 0 < LinearMap.det (L ^ 2).toLinearMap := by
    change 0 < LinearMap.det (L.toLinearMap ^ 2)
    rw [map_pow]
    exact pow_pos hpos 2
  have hs (ho2 : orderOf (L ^ 2) = 2 ∨ orderOf (L ^ 2) = 3) : False := by
    have hsorder : orderOf (L ^ 2) = 2 ∨ orderOf (L ^ 2) = 3 ∨
        orderOf (L ^ 2) = 4 ∨ orderOf (L ^ 2) = 6 := by
      rcases ho2 with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    obtain ⟨a, ha⟩ := crystallographic_fixedVector_uniqueLine (L ^ 2) hsorder hpos2
      q r hq hq2 hr2
    have he : L r = -r := by rw [ha, map_smul, hflip, smul_neg]
    exact hr (realVector_eq_neg_zero r (hfix.symm.trans he))
  rcases ho with h | h | h | h | h
  · have hL := orderOf_eq_one_iff.mp h
    have he : q = -q := by rw [hL] at hflip; exact hflip
    exact False.elim (hq (realVector_eq_neg_zero q he))
  · simpa only [h] using pow_orderOf_eq_one L
  · have hp : L ^ 3 = 1 := by simpa only [h] using pow_orderOf_eq_one L
    have he : (L ^ 3) q = -q := by
      change L (L (L q)) = -q
      rw [hflip, map_neg, hflip, neg_neg, hflip]
    rw [hp] at he
    change q = -q at he
    exact False.elim (hq (realVector_eq_neg_zero q he))
  · have ho2 : orderOf (L ^ 2) = 2 := by
      rw [orderOf_pow_of_dvd (by decide : (2 : ℕ) ≠ 0) (by rw [h]; decide), h]
    exact False.elim (hs (Or.inl ho2))
  · have ho2 : orderOf (L ^ 2) = 3 := by
      rw [orderOf_pow_of_dvd (by decide : (2 : ℕ) ≠ 0) (by rw [h]; decide), h]
    exact False.elim (hs (Or.inr ho2))

theorem affineFree_lineReverse_involution (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (γ : G) (hpos : 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap)
    (q : E3) (hq : q ≠ 0) (hflip : γ.val.linearIsometryEquiv q = -q) :
    γ.val.linearIsometryEquiv ^ 2 = 1 := by
  have hγ : γ ≠ 1 := by
    intro he
    rw [he] at hflip
    change q = -q at hflip
    exact hq (realVector_eq_neg_zero q hflip)
  obtain ⟨p, r, hp, hr⟩ := exists_affineAxis_point γ.val
  have hr0 : r ≠ 0 := by
    intro he
    exact hfree γ hγ p (by simpa only [he, add_zero] using hp)
  exact crystallographic_lineReverse_involution γ.val.linearIsometryEquiv
    (affineFree_linear_order_cases G b hb hfree γ hpos) hpos r q hr0 hr hq hflip

end DifferentialGeometry.Geometry.FlatSurface
