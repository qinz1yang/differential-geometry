import DifferentialGeometry.Geometry.Exponential.Flat.CentralDeckAxis
import Mathlib.Analysis.InnerProductSpace.Dual

/-!
A common invariant direction of the actual finite lattice point group yields a nonzero
central translation in the same affine group. Averaging actual lattice basis vectors preserves
the lattice and is nonzero by inner-product separation, with no supplied rational axis.
-/

set_option autoImplicit false

noncomputable section

open Module
open scoped BigOperators

namespace DifferentialGeometry.Geometry.FlatSurface

variable {V : Type*} [instV : NormedAddCommGroup V]
  [instInner : InnerProductSpace ℝ V] {ι : Type*}

theorem exists_invariantAxis_centralTranslation (G : Subgroup (V ≃ᵃⁱ[ℝ] V))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis ι ℝ V)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (q : V) (hq : q ≠ 0) (hfix : ∀ γ : G, γ.val.linearIsometryEquiv q = q) :
    ∃ v : V, v ≠ 0 ∧ v ∈ affineTranslationModule G ∧
      ∀ γ : G, γ.val.linearIsometryEquiv v = v := by
  classical
  let H := (affineLinearHom.comp G.subtype).range
  let instFintype : Fintype H := Fintype.ofFinite H
  let r := (affineLinearHom.comp G.subtype).rangeRestrict
  obtain ⟨i, hi⟩ : ∃ i, inner ℝ q (b i) ≠ 0 := by
    by_contra! hz
    exact hq (InnerProductSpace.ext_inner_right_basis b
      (by intro i; simpa only [inner_zero_left] using hz i))
  have hfixed (a : H) : a.val q = q := by
    obtain ⟨γ, hγ⟩ := (affineLinearHom.comp G.subtype).rangeRestrict_surjective a
    have he := congrArg Subtype.val hγ
    change γ.val.linearIsometryEquiv = a.val at he
    rw [← he]
    exact hfix γ
  let v : V := ∑ a : H, a.val (b i)
  have hpair : inner ℝ q v = (Fintype.card H : ℝ) * inner ℝ q (b i) := by
    change inner ℝ q (∑ a : H, a.val (b i)) = _
    rw [inner_sum]
    have hin (a : H) : inner ℝ q (a.val (b i)) = inner ℝ q (b i) := by
      simpa only [hfixed a] using a.val.inner_map_map q (b i)
    simp only [hin, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  refine ⟨v, ?_, ?_, ?_⟩
  · intro hz
    rw [hz, inner_zero_right] at hpair
    exact mul_ne_zero (by exact_mod_cast (Fintype.card_pos (α := H)).ne') hi hpair.symm
  · apply Submodule.sum_mem
    intro a ha
    obtain ⟨γ, hγ⟩ := (affineLinearHom.comp G.subtype).rangeRestrict_surjective a
    have he := congrArg Subtype.val hγ
    change γ.val.linearIsometryEquiv = a.val at he
    rw [← he]
    exact affineTranslationModule_linear_mem G γ
      (hb ▸ Submodule.subset_span ⟨i, rfl⟩)
  · intro γ
    change γ.val.linearIsometryEquiv (∑ a : H, a.val (b i)) = _
    rw [map_sum]
    exact Fintype.sum_equiv (Equiv.mulLeft (r γ)) _ _ (by intro a; rfl)

theorem exists_centralDeck_of_invariantAxis (G : Subgroup (V ≃ᵃⁱ[ℝ] V))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis ι ℝ V)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (q : V) (hq : q ≠ 0) (hfix : ∀ γ : G, γ.val.linearIsometryEquiv q = q) :
    ∃ g : G, g ≠ 1 ∧ g ∈ Subgroup.center G ∧ g.val.linearIsometryEquiv = 1 := by
  obtain ⟨v, hv, hmem, hfixed⟩ :=
    exists_invariantAxis_centralTranslation G b hb q hq hfix
  let g : G := ⟨AffineIsometryEquiv.constVAdd ℝ V v, hmem⟩
  refine ⟨g, ?_, ?_, rfl⟩
  · intro he
    have hz := congrArg (fun a : G => a.val 0) he
    change v + 0 = 0 at hz
    exact hv (by simpa only [add_zero] using hz)
  · rw [Subgroup.mem_center_iff]
    intro γ
    apply Subtype.ext
    have he : γ.val * g.val * γ.val⁻¹ = g.val := by
      change γ.val * AffineIsometryEquiv.constVAdd ℝ V v * γ.val⁻¹ = _
      rw [affine_conjugate_constVAdd, hfixed γ]
    have hm := congrArg (fun a => a * γ.val) he
    change γ.val * g.val = g.val * γ.val
    simpa only [mul_assoc, inv_mul_cancel, mul_one] using hm

end DifferentialGeometry.Geometry.FlatSurface
