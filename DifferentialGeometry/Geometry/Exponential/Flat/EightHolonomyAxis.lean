import DifferentialGeometry.Geometry.Exponential.Flat.RotationNormalizerAxis
import Mathlib.GroupTheory.PGroup

/-!
An actual eight-element point subgroup of a free positive lattice affine group preserves an
unoriented line. Its nontrivial two-group center supplies an actual motion lift and nonzero
screw vector; central conjugation and the actual rotation orders preserve that line.
-/

set_option autoImplicit false

noncomputable section

open Module

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem affineFree_eight_subgroup_axis (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hpos : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap)
    (K : Subgroup (affineLinearHom.comp G.subtype).range) (hc : Nat.card K = 8) :
    ∃ q : E3, q ≠ 0 ∧ ∀ a : K, a.val.val q = q ∨ a.val.val q = -q := by
  let H := (affineLinearHom.comp G.subtype).range
  let instNontrivial : Nontrivial K :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hc]; norm_num)
  let instPrime : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP : IsPGroup 2 K := IsPGroup.of_card (n := 3) (by simpa using hc)
  let instCenter : Nontrivial (Subgroup.center K) := hP.center_nontrivial
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center K)
  let c : K := z.val
  let rho := H.subtype.comp K.subtype
  have hrho : Function.Injective rho :=
    Subtype.val_injective.comp Subtype.val_injective
  have hcn : c ≠ 1 := by intro he; exact hz (Subtype.ext he)
  have hn : rho c ≠ 1 := by
    intro he
    exact hcn (hrho (he.trans rho.map_one.symm))
  obtain ⟨g, hg⟩ := c.val.property
  change g.val.linearIsometryEquiv = rho c at hg
  have hgn : g.val.linearIsometryEquiv ≠ 1 := by rw [hg]; exact hn
  have hgne : g ≠ 1 := by intro he; apply hgn; rw [he]; rfl
  have ho : orderOf g.val.linearIsometryEquiv = 2 ∨
      orderOf g.val.linearIsometryEquiv = 3 ∨ orderOf g.val.linearIsometryEquiv = 4 ∨
      orderOf g.val.linearIsometryEquiv = 6 := by
    rcases affineFree_linear_order_cases G b hb hfree g (hpos g) with h | h
    · exact False.elim (hgn (orderOf_eq_one_iff.mp h))
    · exact h
  obtain ⟨p, q, hp, hfix⟩ := exists_affineAxis_point g.val
  have hq : q ≠ 0 := by
    intro he
    exact hfree g hgne p (by simpa only [he, add_zero] using hp)
  refine ⟨q, hq, ?_⟩
  intro a
  have hcomm : a * c = c * a := Subgroup.mem_center_iff.mp z.property a
  have hca : a * c * a⁻¹ = c := by
    rw [hcomm, mul_assoc, mul_inv_cancel, mul_one]
  have hcL : rho a * g.val.linearIsometryEquiv * (rho a)⁻¹ =
      g.val.linearIsometryEquiv := by
    rw [hg, ← map_inv, ← map_mul, ← map_mul, hca]
  exact crystallographic_normalizer_preserves_axis g.val.linearIsometryEquiv (rho a)
    ho (hpos g) (Or.inl hcL) q hq hfix

end DifferentialGeometry.Geometry.FlatSurface
