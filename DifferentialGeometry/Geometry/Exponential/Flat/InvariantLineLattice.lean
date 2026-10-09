import DifferentialGeometry.Geometry.Exponential.Flat.AffineTranslations
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.LinearAlgebra.Finsupp.LinearCombination

/-!
An actual finite affine point group preserving a nonzero unoriented direction constructs
an invariant nonzero vector of its same translation lattice. The signs are derived from
the actual direction action, and a signed finite average of lattice basis vectors stays
in that lattice and is nonzero by its inner product with the direction.
-/

set_option autoImplicit false

noncomputable section

open Module
open scoped BigOperators

namespace DifferentialGeometry.Geometry.FlatSurface

variable {V : Type*} [instV : NormedAddCommGroup V]
  [instInner : InnerProductSpace ℝ V] {ι : Type*}

theorem exists_invariantLine_integerVector (G : Subgroup (V ≃ᵃⁱ[ℝ] V))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis ι ℝ V)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (q : V) (hq : q ≠ 0)
    (hline : ∀ γ : G, γ.val.linearIsometryEquiv q = q ∨ γ.val.linearIsometryEquiv q = -q) :
    ∃ v : V, v ≠ 0 ∧ v ∈ affineTranslationModule G ∧
      ∀ γ : G, γ.val.linearIsometryEquiv v = v ∨ γ.val.linearIsometryEquiv v = -v := by
  classical
  let H := (affineLinearHom.comp G.subtype).range
  let instFintype : Fintype H := Fintype.ofFinite H
  let r := (affineLinearHom.comp G.subtype).rangeRestrict
  let sigma : H → ℤ := fun a => if a.val q = q then 1 else -1
  have hsign (a : H) : sigma a = 1 ∨ sigma a = -1 := by
    dsimp only [sigma]
    split_ifs with ha
    · exact Or.inl rfl
    · exact Or.inr rfl
  have hlineH (a : H) : a.val q = q ∨ a.val q = -q := by
    obtain ⟨γ, hγ⟩ := (affineLinearHom.comp G.subtype).rangeRestrict_surjective a
    have he := congrArg Subtype.val hγ
    change γ.val.linearIsometryEquiv = a.val at he
    rw [← he]
    exact hline γ
  have hact (a : H) : a.val q = (sigma a : ℝ) • q := by
    by_cases ha : a.val q = q
    · simp only [sigma, ite_eq_left ha, Int.cast_one, one_smul]
      exact ha
    · simp only [sigma, ite_eq_right ha, Int.cast_neg, Int.cast_one, neg_one_smul]
      exact (hlineH a).resolve_left ha
  have hmul (a c : H) : sigma (a * c) = sigma a * sigma c := by
    have he : (sigma (a * c) : ℝ) • q = ((sigma a : ℝ) * (sigma c : ℝ)) • q := by
      rw [← hact (a * c)]
      change a.val (c.val q) = _
      rw [hact c, map_smul, hact a, smul_smul, mul_comm]
    have hc := smul_left_injective ℝ hq he
    exact_mod_cast hc
  have hcancel (a c : H) : sigma a * sigma (a * c) = sigma c := by
    rw [hmul]
    rcases hsign a with h | h <;> rw [h] <;> ring
  obtain ⟨i, hi⟩ : ∃ i, inner ℝ q (b i) ≠ 0 := by
    by_contra! hz
    exact hq (InnerProductSpace.ext_inner_right_basis b
      (by intro i; simpa only [inner_zero_left] using hz i))
  let v : V := ∑ a : H, sigma a • a.val (b i)
  have hpair (a : H) : inner ℝ q (sigma a • a.val (b i)) = inner ℝ q (b i) := by
    rw [← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right]
    have he := a.val.inner_map_map q (b i)
    rw [hact a, real_inner_smul_left] at he
    exact he
  have hpairv : inner ℝ q v = (Fintype.card H : ℝ) * inner ℝ q (b i) := by
    change inner ℝ q (∑ a : H, sigma a • a.val (b i)) = _
    rw [inner_sum]
    simp only [hpair, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hnonzero : v ≠ 0 := by
    intro hz
    rw [hz, inner_zero_right] at hpairv
    exact mul_ne_zero (by exact_mod_cast (Fintype.card_pos (α := H)).ne') hi hpairv.symm
  have hmem : v ∈ affineTranslationModule G := by
    apply Submodule.sum_mem
    intro a ha
    apply (affineTranslationModule G).smul_mem
    obtain ⟨γ, hγ⟩ := (affineLinearHom.comp G.subtype).rangeRestrict_surjective a
    have he := congrArg Subtype.val hγ
    change γ.val.linearIsometryEquiv = a.val at he
    rw [← he]
    exact affineTranslationModule_linear_mem G γ
      (hb ▸ Submodule.subset_span ⟨i, rfl⟩)
  have hcov (γ : G) : γ.val.linearIsometryEquiv v = sigma (r γ) • v := by
    change γ.val.linearIsometryEquiv (∑ a : H, sigma a • a.val (b i)) = _
    rw [map_sum]
    simp only [map_zsmul]
    change (∑ a : H, sigma a • (r γ * a).val (b i)) = _
    have heq : (∑ a : H, sigma (r γ * a) • (r γ * a).val (b i)) = v :=
      Fintype.sum_equiv (Equiv.mulLeft (r γ)) _ _ (by intro a; rfl)
    calc
      _ = ∑ a : H, sigma (r γ) • (sigma (r γ * a) • (r γ * a).val (b i)) := by
        apply Finset.sum_congr rfl
        intro a ha
        rw [smul_smul, hcancel]
      _ = sigma (r γ) • (∑ a : H, sigma (r γ * a) • (r γ * a).val (b i)) :=
        Finset.smul_sum.symm
      _ = sigma (r γ) • v := congrArg (fun w : V => sigma (r γ) • w) heq
  refine ⟨v, hnonzero, hmem, ?_⟩
  intro γ
  rcases hsign (r γ) with h | h
  · left
    simpa only [h, one_smul] using hcov γ
  · right
    simpa only [h, neg_one_smul] using hcov γ

end DifferentialGeometry.Geometry.FlatSurface
