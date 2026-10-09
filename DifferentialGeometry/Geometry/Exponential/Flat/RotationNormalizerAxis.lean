import DifferentialGeometry.Geometry.Exponential.Flat.OrderThreeAxis
import DifferentialGeometry.Geometry.Exponential.Flat.InvolutionAxis
import DifferentialGeometry.Geometry.Exponential.Flat.CrystallographicOrders

/-!
The actual crystallographic order cases reduce every nontrivial rotation to a nontrivial
involution or order-three square. Its fixed space is one-dimensional, and a normalizer
preserves the actual unoriented screw axis of a free affine lattice group.
-/

set_option autoImplicit false

noncomputable section

open Module

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem crystallographic_fixedVector_uniqueLine (L : E3 ≃ₗᵢ[ℝ] E3)
    (ho : orderOf L = 2 ∨ orderOf L = 3 ∨ orderOf L = 4 ∨ orderOf L = 6)
    (hpos : 0 < LinearMap.det L.toLinearMap) (q v : E3)
    (hq : q ≠ 0) (hfixq : L q = q) (hfixv : L v = v) : ∃ a : ℝ, v = a • q := by
  have hn : L ≠ 1 := by
    intro he
    rcases ho with h | h | h | h <;> simp [he] at h
  have hs (hh : orderOf L = 4 ∨ orderOf L = 6) : L ^ 2 ≠ 1 := by
    intro hp
    have hd := orderOf_dvd_of_pow_eq_one hp
    rcases hh with h | h <;> norm_num [h] at hd
  have hq2 : (L ^ 2) q = q := by change L (L q) = q; rw [hfixq, hfixq]
  have hv2 : (L ^ 2) v = v := by change L (L v) = v; rw [hfixv, hfixv]
  have hpos2 : 0 < LinearMap.det (L ^ 2).toLinearMap := by
    change 0 < LinearMap.det (L.toLinearMap ^ 2)
    rw [map_pow]
    exact pow_pos hpos 2
  rcases ho with h | h | h | h
  · exact involution_fixedVector_uniqueLine L (by simpa only [h] using pow_orderOf_eq_one L) hn hpos
      q v hq hfixq hfixv
  · exact orderThree_fixedVector_uniqueLine L (by simpa only [h] using pow_orderOf_eq_one L) hn hpos
      q v hq hfixq hfixv
  · have hp : (L ^ 2) ^ 2 = 1 := by rw [← pow_mul]; simpa only [h] using pow_orderOf_eq_one L
    exact involution_fixedVector_uniqueLine (L ^ 2) hp (hs (Or.inl h)) hpos2 q v hq hq2 hv2
  · have hp : (L ^ 2) ^ 3 = 1 := by rw [← pow_mul]; simpa only [h] using pow_orderOf_eq_one L
    exact orderThree_fixedVector_uniqueLine (L ^ 2) hp (hs (Or.inr h)) hpos2 q v hq hq2 hv2

theorem crystallographic_normalizer_preserves_axis (L K : E3 ≃ₗᵢ[ℝ] E3)
    (ho : orderOf L = 2 ∨ orderOf L = 3 ∨ orderOf L = 4 ∨ orderOf L = 6)
    (hpos : 0 < LinearMap.det L.toLinearMap)
    (hconj : K * L * K⁻¹ = L ∨ K * L * K⁻¹ = L⁻¹)
    (q : E3) (hq : q ≠ 0) (hfixq : L q = q) : K q = q ∨ K q = -q := by
  have hc : (K * L * K⁻¹) (K q) = K q := by
    change K (L (K.symm (K q))) = K q
    rw [K.symm_apply_apply, hfixq]
  have hf : L (K q) = K q := by
    rcases hconj with h | h
    · rw [h] at hc
      exact hc
    · rw [h] at hc
      have he := congrArg L hc
      change L (L.symm (K q)) = L (K q) at he
      rw [L.apply_symm_apply] at he
      exact he.symm
  obtain ⟨a, ha⟩ := crystallographic_fixedVector_uniqueLine L ho hpos q (K q) hq hfixq hf
  have hm : |a| * ‖q‖ = 1 * ‖q‖ := by
    have hn := K.norm_map q
    rw [ha, norm_smul, Real.norm_eq_abs] at hn
    simpa only [one_mul] using hn
  have habs : |a| = 1 := mul_right_cancel₀ (norm_ne_zero_iff.mpr hq) hm
  rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp habs with h | h
  · left
    rw [h, one_smul] at ha
    exact ha
  · right
    rw [h, neg_one_smul] at ha
    exact ha

theorem exists_crystallographic_normalizerDeck_axis (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hpos : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap)
    (g : G)
    (hne : g.val.linearIsometryEquiv ≠ 1)
    (hconj : ∀ γ : G, γ.val.linearIsometryEquiv * g.val.linearIsometryEquiv *
      γ.val.linearIsometryEquiv⁻¹ = g.val.linearIsometryEquiv ∨
      γ.val.linearIsometryEquiv * g.val.linearIsometryEquiv *
        γ.val.linearIsometryEquiv⁻¹ = g.val.linearIsometryEquiv⁻¹) :
    ∃ q : E3, q ≠ 0 ∧ ∀ γ : G, γ.val.linearIsometryEquiv q = q ∨
      γ.val.linearIsometryEquiv q = -q := by
  have hg : g ≠ 1 := by
    intro he
    apply hne
    rw [he]
    rfl
  have ho : orderOf g.val.linearIsometryEquiv = 2 ∨
      orderOf g.val.linearIsometryEquiv = 3 ∨ orderOf g.val.linearIsometryEquiv = 4 ∨
      orderOf g.val.linearIsometryEquiv = 6 := by
    rcases affineFree_linear_order_cases G b hb hfree g (hpos g) with h | h
    · exact False.elim (hne (orderOf_eq_one_iff.mp h))
    · exact h
  obtain ⟨p, q, hpoint, hfixed⟩ := exists_affineAxis_point g.val
  have hq : q ≠ 0 := by
    intro hz
    exact hfree g hg p (by simpa only [hz, add_zero] using hpoint)
  refine ⟨q, hq, ?_⟩
  intro γ
  exact crystallographic_normalizer_preserves_axis g.val.linearIsometryEquiv
    γ.val.linearIsometryEquiv ho (hpos g) (hconj γ) q hq hfixed

end DifferentialGeometry.Geometry.FlatSurface
