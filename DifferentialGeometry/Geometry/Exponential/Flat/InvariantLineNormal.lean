import DifferentialGeometry.Geometry.Exponential.Flat.InvariantLineLattice
import DifferentialGeometry.Geometry.Exponential.Flat.AffineScrewPeriods
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
A nonzero actual lattice vector preserved up to sign gives a normal infinite cyclic
translation subgroup of the same free affine group. Conjugation sends the constructed
translation to itself or its inverse. Signed lattice averaging produces this subgroup
from an ordinary invariant unoriented direction without a supplied normal subgroup.
-/

set_option autoImplicit false

noncomputable section

open Module

namespace DifferentialGeometry.Geometry.FlatSurface

variable {V : Type*} [instV : NormedAddCommGroup V]
  [instInner : InnerProductSpace ℝ V] [instFD : FiniteDimensional ℝ V] {ι : Type*}

theorem exists_normalCyclic_translation (G : Subgroup (V ≃ᵃⁱ[ℝ] V))
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : V, γ.val x ≠ x)
    (v : V) (hv : v ≠ 0) (hL : v ∈ affineTranslationModule G)
    (hline : ∀ γ : G, γ.val.linearIsometryEquiv v = v ∨ γ.val.linearIsometryEquiv v = -v) :
    ∃ a : G, a ≠ 1 ∧ Infinite (Subgroup.zpowers a) ∧
      (Subgroup.zpowers a).Normal ∧ a.val.linearIsometryEquiv = 1 := by
  let a : G := ⟨AffineIsometryEquiv.constVAdd ℝ V v, hL⟩
  have ha : a ≠ 1 := by
    intro he
    have hz := congrArg (fun γ : G => γ.val 0) he
    change v + 0 = 0 at hz
    exact hv (by simpa only [add_zero] using hz)
  have hconj (γ : G) : γ * a * γ⁻¹ = a ∨ γ * a * γ⁻¹ = a⁻¹ := by
    rcases hline γ with h | h
    · left
      apply Subtype.ext
      change γ.val * AffineIsometryEquiv.constVAdd ℝ V v * γ.val⁻¹ =
        AffineIsometryEquiv.constVAdd ℝ V v
      rw [affine_conjugate_constVAdd, h]
    · right
      apply Subtype.ext
      change γ.val * AffineIsometryEquiv.constVAdd ℝ V v * γ.val⁻¹ =
        (AffineIsometryEquiv.constVAdd ℝ V v)⁻¹
      rw [affine_conjugate_constVAdd, h, affine_constVAdd_neg]
  have hn : (Subgroup.zpowers a).Normal := by
    rw [Subgroup.normal_iff_map_conj_eq]
    intro γ
    rw [MonoidHom.map_zpowers]
    change Subgroup.zpowers (γ * a * γ⁻¹) = Subgroup.zpowers a
    rcases hconj γ with h | h
    · rw [h]
    · rw [h, Subgroup.zpowers_inv]
  exact ⟨a, ha, infinite_zpowers.mpr (affineFree_no_finiteOrder G hfree ha), hn, rfl⟩

theorem exists_invariantLine_normalCyclic (G : Subgroup (V ≃ᵃⁱ[ℝ] V))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis ι ℝ V)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : V, γ.val x ≠ x)
    (q : V) (hq : q ≠ 0)
    (hline : ∀ γ : G, γ.val.linearIsometryEquiv q = q ∨ γ.val.linearIsometryEquiv q = -q) :
    ∃ a : G, a ≠ 1 ∧ Infinite (Subgroup.zpowers a) ∧
      (Subgroup.zpowers a).Normal ∧ a.val.linearIsometryEquiv = 1 := by
  obtain ⟨v, hv, hL, hcov⟩ := exists_invariantLine_integerVector G b hb q hq hline
  exact exists_normalCyclic_translation G hfree v hv hL hcov

end DifferentialGeometry.Geometry.FlatSurface
