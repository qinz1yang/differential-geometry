import DifferentialGeometry.Geometry.Exponential.Flat.RotationUnitPoles
import DifferentialGeometry.Geometry.Exponential.Flat.FiniteTwoFixedOrbits

/-!
The actual unit pole set is invariant under the actual point group, by conjugating its
nonidentity stabilizer. Its resulting action retains the same vectors and group elements,
so actual two-fixed-point counting supplies the finite pole orbit bound internally.
-/

set_option autoImplicit false

noncomputable section

open Module

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

def unitPoleSet (H : Subgroup (E3 ≃ₗᵢ[ℝ] E3)) : Set E3 :=
  {v | ‖v‖ = 1 ∧ ∃ a : H, a ≠ 1 ∧ a.val v = v}

instance instUnitPoleAction (H : Subgroup (E3 ≃ₗᵢ[ℝ] E3)) : MulAction H (unitPoleSet H) where
  smul g x := ⟨g.val x.val, by
    obtain ⟨hnorm, a, ha, hfix⟩ := x.property
    refine ⟨(g.val.norm_map x.val).trans hnorm, g * a * g⁻¹, ?_, ?_⟩
    · intro he
      apply ha
      have hh := congrArg (fun b : H => g⁻¹ * b * g) he
      simpa [mul_assoc] using hh
    · change g.val (a.val (g.val.symm (g.val x.val))) = g.val x.val
      rw [g.val.symm_apply_apply, hfix]⟩
  one_smul := by intro x; apply Subtype.ext; rfl
  mul_smul := by intro g h x; apply Subtype.ext; rfl

def unitPole_fixedByEquiv (H : Subgroup (E3 ≃ₗᵢ[ℝ] E3)) (a : H) (ha : a ≠ 1) :
    MulAction.fixedBy (unitPoleSet H) a ≃ {v : E3 // a.val v = v ∧ ‖v‖ = 1} where
  toFun x := ⟨x.val.val, congrArg Subtype.val x.property, x.val.property.1⟩
  invFun x := ⟨⟨x.val, x.property.2, a, ha, x.property.1⟩, Subtype.ext x.property.1⟩
  left_inv x := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv x := by apply Subtype.ext; rfl

theorem affineFree_unitPole_orbits_le_three (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hpos : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap) :
    Nat.card (Quotient (MulAction.orbitRel (affineLinearHom.comp G.subtype).range
      (unitPoleSet (affineLinearHom.comp G.subtype).range))) ≤ 3 := by
  let H := (affineLinearHom.comp G.subtype).range
  have hf : (unitPoleSet H).Finite := affineFree_finite_unitPoleSet G b hb hfree hpos
  let instPoleFinite : Finite (unitPoleSet H) := hf.to_subtype
  have htwo (a : H) (ha : a ≠ 1) : Nat.card (MulAction.fixedBy (unitPoleSet H) a) = 2 := by
    obtain ⟨γ, hγ⟩ := a.property
    change γ.val.linearIsometryEquiv = a.val at hγ
    have hne : γ.val.linearIsometryEquiv ≠ 1 := by
      intro he
      apply ha
      apply Subtype.ext
      exact hγ.symm.trans he
    have hc := affineFree_unit_fixed_card G b hb hfree γ (hpos γ) hne
    rw [hγ] at hc
    exact (Nat.card_congr (unitPole_fixedByEquiv H a ha)).trans
      ((Nat.card_coe_set_eq _).trans hc)
  have hnontrivial (x : unitPoleSet H) : ∃ a : H, a ≠ 1 ∧ a • x = x := by
    obtain ⟨hnorm, a, ha, hfix⟩ := x.property
    exact ⟨a, ha, Subtype.ext hfix⟩
  exact finite_twoFixed_orbits_le_three H (unitPoleSet H) htwo hnontrivial

end DifferentialGeometry.Geometry.FlatSurface
