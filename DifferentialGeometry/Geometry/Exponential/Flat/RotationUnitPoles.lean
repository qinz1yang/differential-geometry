import DifferentialGeometry.Geometry.Exponential.Flat.RotationNormalizerAxis
import Mathlib.Data.Set.Card

/-!
Every actual nonidentity point rotation of a free oriented lattice deck group has exactly
two unit fixed vectors. They are the normalized screw axis and its negative. The finite
actual point group therefore has a finite pole set, with no cardinality premise.
-/

set_option autoImplicit false

noncomputable section

open Module

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem crystallographic_unit_fixed_set (L : E3 ≃ₗᵢ[ℝ] E3)
    (ho : orderOf L = 2 ∨ orderOf L = 3 ∨ orderOf L = 4 ∨ orderOf L = 6)
    (hpos : 0 < LinearMap.det L.toLinearMap) (q : E3) (hq : q ≠ 0) (hfix : L q = q) :
    {v : E3 | L v = v ∧ ‖v‖ = 1} = {‖q‖⁻¹ • q, -(‖q‖⁻¹ • q)} := by
  let u := ‖q‖⁻¹ • q
  have hu : ‖u‖ = 1 := by
    simp only [u, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hq)]
  have huf : L u = u := by simp only [u, map_smul, hfix]
  have hun : u ≠ 0 := by intro he; rw [he, norm_zero] at hu; norm_num at hu
  ext v
  constructor
  · intro hv
    obtain ⟨a, ha⟩ := crystallographic_fixedVector_uniqueLine L ho hpos u v hun huf hv.1
    have hn := hv.2
    rw [ha, norm_smul, hu, mul_one, Real.norm_eq_abs] at hn
    rcases (abs_eq (by norm_num : (0 : ℝ) ≤ 1)).mp hn with h | h
    · rw [h, one_smul] at ha
      exact Set.mem_insert_iff.mpr (Or.inl ha)
    · rw [h, neg_one_smul] at ha
      exact Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr ha))
  · intro hv
    rcases Set.mem_insert_iff.mp hv with h | h
    · rw [h]
      exact ⟨huf, hu⟩
    · rw [Set.mem_singleton_iff.mp h]
      exact ⟨by rw [map_neg, huf], by rw [norm_neg, hu]⟩

theorem crystallographic_unit_fixed_card (L : E3 ≃ₗᵢ[ℝ] E3)
    (ho : orderOf L = 2 ∨ orderOf L = 3 ∨ orderOf L = 4 ∨ orderOf L = 6)
    (hpos : 0 < LinearMap.det L.toLinearMap) (q : E3) (hq : q ≠ 0) (hfix : L q = q) :
    ({v : E3 | L v = v ∧ ‖v‖ = 1} : Set E3).ncard = 2 := by
  rw [crystallographic_unit_fixed_set L ho hpos q hq hfix]
  apply Set.ncard_pair
  let u := ‖q‖⁻¹ • q
  have hun : u ≠ 0 := smul_ne_zero (inv_ne_zero (norm_ne_zero_iff.mpr hq)) hq
  intro he
  have hc := smul_left_injective ℝ hun
    (show (1 : ℝ) • u = (-1 : ℝ) • u by simpa only [one_smul, neg_one_smul] using he)
  norm_num at hc

theorem affineFree_unit_fixed_card (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (γ : G) (hpos : 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap)
    (hne : γ.val.linearIsometryEquiv ≠ 1) :
    ({v : E3 | γ.val.linearIsometryEquiv v = v ∧ ‖v‖ = 1} : Set E3).ncard = 2 := by
  have hγ : γ ≠ 1 := by intro he; apply hne; rw [he]; rfl
  obtain ⟨p, q, hp, hfix⟩ := exists_affineAxis_point γ.val
  have hq : q ≠ 0 := by
    intro he
    exact hfree γ hγ p (by simpa only [he, add_zero] using hp)
  have ho : orderOf γ.val.linearIsometryEquiv = 2 ∨ orderOf γ.val.linearIsometryEquiv = 3 ∨
      orderOf γ.val.linearIsometryEquiv = 4 ∨ orderOf γ.val.linearIsometryEquiv = 6 := by
    rcases affineFree_linear_order_cases G b hb hfree γ hpos with h | h
    · exact False.elim (hne (orderOf_eq_one_iff.mp h))
    · exact h
  exact crystallographic_unit_fixed_card γ.val.linearIsometryEquiv ho hpos q hq hfix

theorem affineFree_finite_unitPoleSet (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hpos : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap) :
    Set.Finite {v : E3 | ‖v‖ = 1 ∧
      ∃ a : (affineLinearHom.comp G.subtype).range, a ≠ 1 ∧ a.val v = v} := by
  let H := (affineLinearHom.comp G.subtype).range
  let F (a : H) : Set E3 := {v | a ≠ 1 ∧ a.val v = v ∧ ‖v‖ = 1}
  have hfinite (a : H) : (F a).Finite := by
    by_cases ha : a = 1
    · subst a
      simpa only [F, ne_eq, not_true_eq_false, false_and, Set.ofPred_false] using Set.finite_empty
    · obtain ⟨γ, hγ⟩ := a.property
      change γ.val.linearIsometryEquiv = a.val at hγ
      have hne : γ.val.linearIsometryEquiv ≠ 1 := by
        intro he
        apply ha
        apply Subtype.ext
        exact hγ.symm.trans he
      have hc := affineFree_unit_fixed_card G b hb hfree γ (hpos γ) hne
      have heq : F a = {v : E3 | γ.val.linearIsometryEquiv v = v ∧ ‖v‖ = 1} := by
        ext v
        simp only [F, ha, ne_eq, not_false_eq_true, true_and, hγ]
      rw [heq]
      exact Set.finite_of_ncard_ne_zero (by rw [hc]; norm_num)
  have hf := Set.finite_iUnion hfinite
  apply hf.subset
  intro v hv
  obtain ⟨hnorm, a, ha, hfix⟩ := hv
  exact Set.mem_iUnion.mpr ⟨a, ha, hfix, hnorm⟩

end DifferentialGeometry.Geometry.FlatSurface
