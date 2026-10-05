import DifferentialGeometry.Geometry.Exponential.Flat.NormalKleinThreeTorsion
import DifferentialGeometry.Geometry.Exponential.Flat.SmallHolonomyClassification

/-!
No actual normal four-element point subgroup can coexist with a nontrivial cubic motion in
free positive lattice affine holonomy. The involutive branch gives genuine tetrahedral
torsion; the cyclic-four branch forces cyclic holonomy with incompatible actual orders.
-/

set_option autoImplicit false

noncomputable section

open Module

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem normal_four_zpowers_inverseNormalizer (H : Type*) [instH : Group H]
    (r : H) (hr4 : r ^ 4 = 1) (hr2 : r ^ 2 ≠ 1) (hn : (Subgroup.zpowers r).Normal) :
    ∀ a : H, a * r * a⁻¹ = r ∨ a * r * a⁻¹ = r⁻¹ := by
  have hd := orderOf_dvd_of_pow_eq_one hr4
  have hpos : 0 < orderOf r := Nat.pos_of_dvd_of_pos hd (by decide)
  have hle : orderOf r ≤ 4 := Nat.le_of_dvd (by decide) hd
  have hcases : orderOf r = 1 ∨ orderOf r = 2 ∨ orderOf r = 4 := by
    generalize hk : orderOf r = k at hd hpos hle ⊢
    interval_cases k <;> norm_num at hd <;> omega
  have horder : orderOf r = 4 := by
    rcases hcases with h | h | h
    · exact False.elim (hr2 (by rw [orderOf_eq_one_iff.mp h, one_pow]))
    · exact False.elim (hr2 (by simpa only [h] using pow_orderOf_eq_one r))
    · exact h
  have hf : IsOfFinOrder r := isOfFinOrder_iff_pow_eq_one.mpr ⟨4, by decide, hr4⟩
  let e : Fin 4 ≃ Subgroup.zpowers r := (finCongr horder.symm).trans (finEquivZPowers hf)
  intro a
  have hm : a * r * a⁻¹ ∈ Subgroup.zpowers r := hn.conj_mem r (Subgroup.mem_zpowers r) a
  let c : Subgroup.zpowers r := ⟨a * r * a⁻¹, hm⟩
  obtain ⟨i, hi⟩ := e.surjective c
  have hp : r ^ (i : ℕ) = a * r * a⁻¹ := by
    have he := congrArg Subtype.val hi
    change r ^ ((finCongr horder.symm) i : ℕ) = a * r * a⁻¹ at he
    simpa using he
  have hc2 : (a * r * a⁻¹) ^ 2 ≠ 1 := by
    intro he
    apply hr2
    have hh := congrArg (fun x : H => a⁻¹ * x * a) he
    simpa [pow_two, mul_assoc] using hh
  fin_cases i
  · exact False.elim (hc2 (by rw [← hp]; simp))
  · exact Or.inl (by simpa only [pow_one] using hp.symm)
  · exact False.elim (hc2 (by rw [← hp, ← pow_mul]; exact hr4))
  · right
    have hri : r ^ 3 = r⁻¹ := by
      apply eq_inv_iff_mul_eq_one.mpr
      rw [← pow_succ]
      exact hr4
    exact hp.symm.trans hri

private theorem normal_four_and_three_cyclic (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hpos : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap)
    (r : (affineLinearHom.comp G.subtype).range) (hr : orderOf r = 4)
    (hn : (Subgroup.zpowers r).Normal) (g : G)
    (hg3 : g.val.linearIsometryEquiv ^ 3 = 1) (hgn : g.val.linearIsometryEquiv ≠ 1) :
    IsCyclic (affineLinearHom.comp G.subtype).range := by
  let H := (affineLinearHom.comp G.subtype).range
  have hr4 : r ^ 4 = 1 := by simpa only [hr] using pow_orderOf_eq_one r
  have hr2 : r ^ 2 ≠ 1 := by
    intro he
    have hd := orderOf_dvd_of_pow_eq_one he
    norm_num [hr] at hd
  have hcases := normal_four_zpowers_inverseNormalizer H r hr4 hr2 hn
  obtain ⟨k, hkr⟩ := r.property
  change k.val.linearIsometryEquiv = r.val at hkr
  have hkn : k.val.linearIsometryEquiv ≠ 1 := by
    intro he
    have hre : r = 1 := Subtype.ext (hkr.symm.trans he)
    simp [hre] at hr
  have hk : k ≠ 1 := by intro he; apply hkn; rw [he]; rfl
  obtain ⟨p, q, hp, hfix⟩ := exists_affineAxis_point k.val
  have hq : q ≠ 0 := by
    intro he
    exact hfree k hk p (by simpa only [he, add_zero] using hp)
  have horder : orderOf k.val.linearIsometryEquiv = 4 := by
    rw [hkr]
    exact (orderOf_injective H.subtype Subtype.val_injective r).trans hr
  have hconj (γ : G) : γ.val.linearIsometryEquiv * k.val.linearIsometryEquiv *
      γ.val.linearIsometryEquiv⁻¹ = k.val.linearIsometryEquiv ∨
      γ.val.linearIsometryEquiv * k.val.linearIsometryEquiv *
        γ.val.linearIsometryEquiv⁻¹ = k.val.linearIsometryEquiv⁻¹ := by
    let a : H := (affineLinearHom.comp G.subtype).rangeRestrict γ
    rcases hcases a with he | he
    · left
      have hv := congrArg Subtype.val he
      change γ.val.linearIsometryEquiv * r.val * γ.val.linearIsometryEquiv⁻¹ = r.val at hv
      rw [← hkr] at hv
      exact hv
    · right
      have hv := congrArg Subtype.val he
      change γ.val.linearIsometryEquiv * r.val * γ.val.linearIsometryEquiv⁻¹ = r.val⁻¹ at hv
      rw [← hkr] at hv
      exact hv
  have hline (γ : G) : γ.val.linearIsometryEquiv q = q ∨
      γ.val.linearIsometryEquiv q = -q :=
    crystallographic_normalizer_preserves_axis k.val.linearIsometryEquiv
      γ.val.linearIsometryEquiv (Or.inr (Or.inr (Or.inl horder))) (hpos k)
      (hconj γ) q hq hfix
  have hfixg : g.val.linearIsometryEquiv q = q := by
    rcases hline g with he | he
    · exact he
    · exfalso
      have hh : (g.val.linearIsometryEquiv ^ 3) q = -q := by
        change g.val.linearIsometryEquiv
          (g.val.linearIsometryEquiv (g.val.linearIsometryEquiv q)) = -q
        rw [he, map_neg, he, neg_neg, he]
      rw [hg3] at hh
      change q = -q at hh
      have hz : (2 : ℝ) • q = 0 := by
        rw [two_smul]
        exact add_eq_zero_iff_eq_neg.mpr hh
      exact hq ((smul_eq_zero.mp hz).resolve_left (by norm_num))
  exact affineFree_orderThree_lineHolonomy_isCyclic G b hb hfree hpos q hq hline
    g hg3 hgn hfixg

private theorem cyclic_four_and_three_impossible (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hpos : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap)
    [instC : IsCyclic (affineLinearHom.comp G.subtype).range]
    (r : (affineLinearHom.comp G.subtype).range) (hr : orderOf r = 4) (g : G)
    (hg3 : g.val.linearIsometryEquiv ^ 3 = 1) (hgn : g.val.linearIsometryEquiv ≠ 1) :
    False := by
  let H := (affineLinearHom.comp G.subtype).range
  let s : H := (affineLinearHom.comp G.subtype).rangeRestrict g
  have hs3 : s ^ 3 = 1 := by apply Subtype.ext; exact hg3
  have hsn : s ≠ 1 := by intro he; exact hgn (congrArg Subtype.val he)
  have hsorder : orderOf s = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hs3) with h | h
    · exact False.elim (hsn (orderOf_eq_one_iff.mp h))
    · exact h
  have hd4 : 4 ∣ Nat.card H := by simpa only [hr] using orderOf_dvd_natCard r
  have hd3 : 3 ∣ Nat.card H := by simpa only [hsorder] using orderOf_dvd_natCard s
  obtain ⟨t, ht⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := H)
  obtain ⟨γ, hγ⟩ := t.property
  change γ.val.linearIsometryEquiv = t.val at hγ
  have hord : orderOf γ.val.linearIsometryEquiv = Nat.card H := by
    rw [hγ]
    exact (orderOf_injective H.subtype Subtype.val_injective t).trans ht
  have hcases := affineFree_linear_order_cases G b hb hfree γ (hpos γ)
  rw [hord] at hcases
  rcases hcases with h | h | h | h | h
  · norm_num [h] at hd3
  · norm_num [h] at hd3
  · norm_num [h] at hd4
  · norm_num [h] at hd3
  · norm_num [h] at hd4

theorem affineFree_normal_four_three_obstruction (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hpos : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap)
    (K : Subgroup (affineLinearHom.comp G.subtype).range)
    [instK : Fintype K] [instN : K.Normal] (hc : Fintype.card K = 4) (g : G)
    (hg3 : g.val.linearIsometryEquiv ^ 3 = 1) (hgn : g.val.linearIsometryEquiv ≠ 1) :
    False := by
  classical
  by_cases htwo : ∀ a : K, a.val.val ^ 2 = 1
  · exact affineFree_normalKlein_three_obstruction G b hb hfree hpos K hc htwo g hg3 hgn
  · push Not at htwo
    obtain ⟨a, ha⟩ := htwo
    have hncard : Nat.card K = 4 := Nat.card_eq_fintype_card.trans hc
    have hd := orderOf_dvd_natCard a
    rw [hncard] at hd
    have hposA : 0 < orderOf a := Nat.pos_of_dvd_of_pos hd (by decide)
    have hle : orderOf a ≤ 4 := Nat.le_of_dvd (by decide) hd
    have hcases : orderOf a = 1 ∨ orderOf a = 2 ∨ orderOf a = 4 := by
      generalize hk : orderOf a = k at hd hposA hle ⊢
      interval_cases k <;> norm_num at hd <;> omega
    have horderA : orderOf a = 4 := by
      rcases hcases with h | h | h
      · have he : a = 1 := orderOf_eq_one_iff.mp h
        exact False.elim (ha (by rw [he]; rfl))
      · have he : a ^ 2 = 1 := by simpa only [h] using pow_orderOf_eq_one a
        exact False.elim (ha (congrArg (fun d : K => d.val.val) he))
      · exact h
    let H := (affineLinearHom.comp G.subtype).range
    let r : H := a.val
    have horder : orderOf r = 4 :=
      (orderOf_injective K.subtype Subtype.val_injective a).trans horderA
    have hzp : Subgroup.zpowers r = K := by
      apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr a.property)
      rw [hncard, Nat.card_zpowers, horder]
    have hn : (Subgroup.zpowers r).Normal := hzp.symm ▸ instN
    let instC : IsCyclic H :=
      normal_four_and_three_cyclic G b hb hfree hpos r horder hn g hg3 hgn
    exact cyclic_four_and_three_impossible G b hb hfree hpos r horder g hg3 hgn

end DifferentialGeometry.Geometry.FlatSurface
