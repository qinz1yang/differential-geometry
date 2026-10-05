import DifferentialGeometry.Geometry.Exponential.Flat.EightAxisSubgroup
import DifferentialGeometry.Geometry.Exponential.Flat.NormalFourThreeTorsion

/-!
An actual eight-element affine point subgroup has actual dihedral generators: a fourfold
axis rotation and an involutive axis reversal conjugating it to its inverse. Their subgroup
is the whole actual point subgroup, obtained from the constructed index-two stabilizer.
-/

set_option autoImplicit false

noncomputable section

open Module

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

private theorem index_two_pair_generates (K : Type*) [instK : Group K] [instF : Finite K]
    (S : Subgroup K) (hi : S.index = 2) (r k : K)
    (hZ : Subgroup.zpowers r = S) (hk : k ∉ S) :
    Subgroup.closure ({r, k} : Set K) = ⊤ := by
  let U := Subgroup.closure ({r, k} : Set K)
  have hrU : r ∈ U := Subgroup.subset_closure (by simp)
  have hkU : k ∈ U := Subgroup.subset_closure (by simp)
  have hSU : S ≤ U := by rw [← hZ]; exact Subgroup.zpowers_le.mpr hrU
  have hne : S ≠ U := by intro he; exact hk (he.symm ▸ hkU)
  have hlt : S < U := lt_of_le_of_ne hSU hne
  have hindex : U.index < 2 := by simpa only [hi] using Subgroup.index_strictAnti hlt
  have hpos : U.index ≠ 0 := U.index_ne_zero_of_finite
  have hUone : U.index = 1 := by omega
  exact Subgroup.index_eq_one.mp hUone

private theorem index_two_four_generator_frame (K : Type*) [instK : Group K]
    [instF : Finite K] (S : Subgroup K) (hcyc : IsCyclic S) (hn : S.Normal)
    (hcard : Nat.card S = 4) (hi : S.index = 2) :
    ∃ r k : K, orderOf r = 4 ∧ r ∈ S ∧ k ∉ S ∧
      (Subgroup.zpowers r).Normal ∧ Subgroup.closure ({r, k} : Set K) = ⊤ := by
  classical
  let instCyclic : IsCyclic S := hcyc
  obtain ⟨rS, hrS⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := S)
  let r : K := rS.val
  have hr : orderOf r = 4 :=
    (orderOf_injective S.subtype Subtype.val_injective rS).trans (hrS.trans hcard)
  have hZ : Subgroup.zpowers r = S := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr rS.property)
    rw [hcard, Nat.card_zpowers, hr]
  have hnotop : S ≠ ⊤ := by intro he; rw [he, Subgroup.index_top] at hi; norm_num at hi
  have hex : ∃ k : K, k ∉ S := by
    by_contra he
    apply hnotop
    apply le_antisymm le_top
    intro k _hk
    by_contra hk
    exact he ⟨k, hk⟩
  obtain ⟨k, hk⟩ := hex
  exact ⟨r, k, hr, rS.property, hk, hZ.symm ▸ hn,
    index_two_pair_generates K S hi r k hZ hk⟩

private theorem affine_reversal_inverse_relation (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hpos : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap)
    (g k : G) (q : E3) (hq : q ≠ 0)
    (hfix : g.val.linearIsometryEquiv q = q) (hflip : k.val.linearIsometryEquiv q = -q) :
    k.val.linearIsometryEquiv ^ 2 = 1 ∧
      k.val.linearIsometryEquiv * g.val.linearIsometryEquiv * k.val.linearIsometryEquiv⁻¹ =
        g.val.linearIsometryEquiv⁻¹ := by
  have hk2 := affineFree_lineReverse_involution G b hb hfree k (hpos k) q hq hflip
  have hkg : (k * g).val.linearIsometryEquiv q = -q := by
    change k.val.linearIsometryEquiv (g.val.linearIsometryEquiv q) = -q
    rw [hfix]
    exact hflip
  have hkg2 := affineFree_lineReverse_involution G b hb hfree (k * g) (hpos (k * g))
    q hq hkg
  change (k.val.linearIsometryEquiv * g.val.linearIsometryEquiv) ^ 2 = 1 at hkg2
  exact ⟨hk2, involutions_product_conjugate_inverse k.val.linearIsometryEquiv
    g.val.linearIsometryEquiv hk2 hkg2⟩

private theorem normal_four_representation_cases (K : Type*) [instK : Group K]
    (r k : K) (hr4 : r ^ 4 = 1) (hr2 : r ^ 2 ≠ 1) (hn : (Subgroup.zpowers r).Normal)
    (rho : K →* (E3 ≃ₗᵢ[ℝ] E3)) :
    rho k * rho r * (rho k)⁻¹ = rho r ∨ rho k * rho r * (rho k)⁻¹ = (rho r)⁻¹ := by
  rcases normal_four_zpowers_inverseNormalizer K r hr4 hr2 hn k with he | he
  · left
    simpa only [map_mul, map_inv] using congrArg rho he
  · right
    simpa only [map_mul, map_inv] using congrArg rho he

private theorem represented_four_reversal (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hpos : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap)
    (A : Type*) [instA : Group A]
    (rho : A →* (affineLinearHom.comp G.subtype).range) (hrho : Function.Injective rho)
    (r k : A) (hr : orderOf r = 4) (hn : (Subgroup.zpowers r).Normal)
    (q : E3) (hq : q ≠ 0) (hfix : (rho r).val q = q) (hnfix : (rho k).val q ≠ q) :
    k ^ 2 = 1 ∧ k * r * k⁻¹ = r⁻¹ ∧ (rho k).val q = -q := by
  have hr4 : r ^ 4 = 1 := by simpa only [hr] using pow_orderOf_eq_one r
  have hr2 : r ^ 2 ≠ 1 := by
    intro he
    have hd := orderOf_dvd_of_pow_eq_one he
    norm_num [hr] at hd
  let H := (affineLinearHom.comp G.subtype).range
  let phi : A →* (E3 ≃ₗᵢ[ℝ] E3) := H.subtype.comp rho
  have hphi : Function.Injective phi := Subtype.val_injective.comp hrho
  obtain ⟨g, hg⟩ := (rho r).property
  change g.val.linearIsometryEquiv = phi r at hg
  have horder : orderOf (phi r) = 4 := (orderOf_injective phi hphi r).trans hr
  have hcases := normal_four_representation_cases A r k hr4 hr2 hn phi
  have hpR : 0 < LinearMap.det (phi r).toLinearMap := by rw [← hg]; exact hpos g
  have hflip : phi k q = -q := by
    rcases crystallographic_normalizer_preserves_axis (phi r) (phi k)
        (Or.inr (Or.inr (Or.inl horder))) hpR hcases q hq hfix with he | he
    · exact False.elim (hnfix he)
    · exact he
  obtain ⟨γ, hγ⟩ := (rho k).property
  change γ.val.linearIsometryEquiv = phi k at hγ
  have hγq : γ.val.linearIsometryEquiv q = -q := by rw [hγ]; exact hflip
  have hgfix : g.val.linearIsometryEquiv q = q := by rw [hg]; exact hfix
  obtain ⟨hγ2, hinv⟩ := affine_reversal_inverse_relation G b hb hfree hpos g γ
    q hq hgfix hγq
  rw [hγ, hg] at hinv
  have hk2 : k ^ 2 = 1 := by
    apply hphi
    rw [map_pow, map_one, ← hγ]
    exact hγ2
  have hkr : k * r * k⁻¹ = r⁻¹ := by
    apply hphi
    simpa only [map_mul, map_inv] using hinv
  exact ⟨hk2, hkr, hflip⟩

theorem affineFree_eight_subgroup_dihedral (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hpos : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap)
    (K : Subgroup (affineLinearHom.comp G.subtype).range) (hc : Nat.card K = 8) :
    ∃ (q : E3) (r k : K), q ≠ 0 ∧ orderOf r = 4 ∧ k ^ 2 = 1 ∧
      k * r * k⁻¹ = r⁻¹ ∧ Subgroup.closure ({r, k} : Set K) = ⊤ ∧
      r.val.val q = q ∧ k.val.val q = -q := by
  classical
  obtain ⟨q, S, hq, hcyc, hn, hcard, hi, hS⟩ :=
    affineFree_eight_subgroup_cyclicIndexTwo G b hb hfree hpos K hc
  obtain ⟨r, k, hr, hrmem, hk, hnZ, hgen⟩ :=
    index_two_four_generator_frame K S hcyc hn hcard hi
  have hfix : r.val.val q = q := (hS r).mp hrmem
  have hnfix : k.val.val q ≠ q := by intro he; exact hk ((hS k).mpr he)
  obtain ⟨hk2, hkr, hflip⟩ := represented_four_reversal G b hb hfree hpos K
    K.subtype Subtype.val_injective r k hr hnZ q hq hfix hnfix
  exact ⟨q, r, k, hq, hr, hk2, hkr, hgen, hfix, hflip⟩

end DifferentialGeometry.Geometry.FlatSurface
