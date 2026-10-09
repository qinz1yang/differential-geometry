import DifferentialGeometry.Geometry.Exponential.Flat.DihedralThreeTorsion
import DifferentialGeometry.Geometry.Exponential.Flat.FixedAxisCyclic

/-!
An actual free oriented lattice deck group preserving a line and containing a nontrivial
order-three rotation has cyclic holonomy. A reversal and its product with that rotation
are actual half-turns, which give the excluded dihedral-three affine relation.
-/

set_option autoImplicit false

noncomputable section

open Module

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem involutions_product_conjugate_inverse (K L : E3 ≃ₗᵢ[ℝ] E3)
    (hk : K ^ 2 = 1) (hkl : (K * L) ^ 2 = 1) : K * L * K⁻¹ = L⁻¹ := by
  have hinv : K⁻¹ = K := inv_eq_of_mul_eq_one_left (by simpa only [pow_two] using hk)
  rw [hinv]
  apply eq_inv_iff_mul_eq_one.mpr
  simpa only [pow_two, mul_assoc] using hkl

theorem affineFree_orderThree_lineHolonomy_isCyclic (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hpos : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap)
    (q : E3) (hq : q ≠ 0)
    (hline : ∀ γ : G, γ.val.linearIsometryEquiv q = q ∨ γ.val.linearIsometryEquiv q = -q)
    (g : G) (hg3 : g.val.linearIsometryEquiv ^ 3 = 1)
    (hgn : g.val.linearIsometryEquiv ≠ 1) (hfix : g.val.linearIsometryEquiv q = q) :
    IsCyclic (affineLinearHom.comp G.subtype).range := by
  have hfixed (k : G) : k.val.linearIsometryEquiv q = q := by
    rcases hline k with h | h
    · exact h
    · exfalso
      have hk2 := affineFree_lineReverse_involution G b hb hfree k (hpos k) q hq h
      have hkg : (k * g).val.linearIsometryEquiv q = -q := by
        change k.val.linearIsometryEquiv (g.val.linearIsometryEquiv q) = -q
        rw [hfix]
        exact h
      have hkg2 := affineFree_lineReverse_involution G b hb hfree (k * g) (hpos (k * g))
        q hq hkg
      change (k.val.linearIsometryEquiv * g.val.linearIsometryEquiv) ^ 2 = 1 at hkg2
      have hc := involutions_product_conjugate_inverse k.val.linearIsometryEquiv
        g.val.linearIsometryEquiv hk2 hkg2
      exact affineFree_dihedralThree_obstruction G hfree g k hg3 hgn (hpos g)
        hk2 hc q hq hfix h
  let H := (affineLinearHom.comp G.subtype).range
  have hposH (a : H) : 0 < LinearMap.det a.val.toLinearMap := by
    obtain ⟨γ, hγ⟩ := a.property
    rw [← hγ]
    exact hpos γ
  have hfixedH (a : H) : a.val q = q := by
    obtain ⟨γ, hγ⟩ := a.property
    rw [← hγ]
    exact hfixed γ
  exact finitePositive_fixedAxis_isCyclic H hposH q hq hfixedH

theorem affineFree_orderThree_normalizerHolonomy_isCyclic (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hpos : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap)
    (g : G) (hg3 : g.val.linearIsometryEquiv ^ 3 = 1)
    (hgn : g.val.linearIsometryEquiv ≠ 1)
    (hc : ∀ γ : G, γ.val.linearIsometryEquiv * g.val.linearIsometryEquiv *
      γ.val.linearIsometryEquiv⁻¹ = g.val.linearIsometryEquiv ∨
      γ.val.linearIsometryEquiv * g.val.linearIsometryEquiv *
        γ.val.linearIsometryEquiv⁻¹ = g.val.linearIsometryEquiv⁻¹) :
    IsCyclic (affineLinearHom.comp G.subtype).range := by
  have hg : g ≠ 1 := by intro he; apply hgn; rw [he]; rfl
  obtain ⟨p, q, hp, hfix⟩ := exists_affineAxis_point g.val
  have hq : q ≠ 0 := by
    intro he
    exact hfree g hg p (by simpa only [he, add_zero] using hp)
  have hline (γ : G) : γ.val.linearIsometryEquiv q = q ∨
      γ.val.linearIsometryEquiv q = -q :=
    orderThree_normalizer_preserves_axis g.val.linearIsometryEquiv
      γ.val.linearIsometryEquiv hg3 hgn (hpos g) (hc γ) q hq hfix
  exact affineFree_orderThree_lineHolonomy_isCyclic G b hb hfree hpos q hq hline
    g hg3 hgn hfix

end DifferentialGeometry.Geometry.FlatSurface
