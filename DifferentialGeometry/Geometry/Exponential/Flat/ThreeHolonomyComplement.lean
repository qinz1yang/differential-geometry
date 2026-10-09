import DifferentialGeometry.Geometry.Exponential.Flat.OrderThreeNormalizerFixedAxis
import Mathlib.GroupTheory.Transfer

/-!
Actual cardinal twelve or twenty-four free positive lattice affine holonomy has a normal
four- or eight-element two-group complement. Its cubic Sylow normalizer centralizes by the
compiled affine obstruction, so Burnside's transfer constructs the complement internally.
-/

set_option autoImplicit false

noncomputable section

open Module

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem affineFree_large_holonomy_normalTwo_complement (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hpos : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap)
    (hc : Nat.card (affineLinearHom.comp G.subtype).range = 12 ∨
      Nat.card (affineLinearHom.comp G.subtype).range = 24) :
    ∃ K : Subgroup (affineLinearHom.comp G.subtype).range,
      K.Normal ∧ (Nat.card K = 4 ∨ Nat.card K = 8) ∧ IsPGroup 2 K := by
  classical
  let H := (affineLinearHom.comp G.subtype).range
  change Nat.card H = 12 ∨ Nat.card H = 24 at hc
  let instPrime : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P : Sylow 3 H⟩ := Sylow.nonempty (p := 3) (G := H)
  have hPcard : Nat.card P = 3 := by
    rw [Sylow.card_eq_multiplicity]
    rcases hc with h | h
    · rw [h]
      have he : 12 = 3 * 4 := rfl
      rw [he, Nat.factorization_mul_apply_of_coprime (by decide),
        Nat.prime_three.factorization_self, Nat.factorization_eq_zero_of_not_dvd (by decide)]
      norm_num
    · rw [h]
      have he : 24 = 3 * 8 := rfl
      rw [he, Nat.factorization_mul_apply_of_coprime (by decide),
        Nat.prime_three.factorization_self, Nat.factorization_eq_zero_of_not_dvd (by decide)]
      norm_num
  let instCyclic : IsCyclic P := isCyclic_of_prime_card (p := 3) hPcard
  obtain ⟨rP, hrP⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := P)
  let r : H := rP.val
  let fP : P →* H := (P : Subgroup H).subtype
  have hfP : Function.Injective fP := Subtype.val_injective
  have horder : orderOf r = 3 := by
    change orderOf (fP rP) = 3
    exact (orderOf_injective fP hfP rP).trans (hrP.trans hPcard)
  have hr3 : r ^ 3 = 1 := by simpa only [horder] using pow_orderOf_eq_one r
  have hrn : r ≠ 1 := by intro he; rw [he, orderOf_one] at horder; norm_num at horder
  have hzp : Subgroup.zpowers r = (P : Subgroup H) := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr rP.property)
    rw [hPcard, Nat.card_zpowers, horder]
  have hcentral : Subgroup.normalizer (P : Set H) ≤ Subgroup.centralizer (P : Set H) := by
    change Subgroup.normalizer ((P : Subgroup H) : Set H) ≤
      Subgroup.centralizer ((P : Subgroup H) : Set H)
    rw [← hzp]
    exact affineFree_orderThree_normalizer_le_centralizer G b hb hfree hpos r hr3 hrn
  let f := MonoidHom.transferSylow P hcentral
  let K := f.ker
  have hcomp : K.IsComplement' (P : Subgroup H) :=
    MonoidHom.ker_transferSylow_isComplement' P hcentral
  have hmul : Nat.card K * 3 = Nat.card H := by
    have he := hcomp.card_mul_card
    rw [hPcard] at he
    exact he
  have hKcard : Nat.card K = 4 ∨ Nat.card K = 8 := by rcases hc with h | h <;> omega
  refine ⟨K, inferInstance, hKcard, ?_⟩
  rcases hKcard with h | h
  · exact IsPGroup.of_card (n := 2) (by simpa using h)
  · exact IsPGroup.of_card (n := 3) (by simpa using h)

end DifferentialGeometry.Geometry.FlatSurface
