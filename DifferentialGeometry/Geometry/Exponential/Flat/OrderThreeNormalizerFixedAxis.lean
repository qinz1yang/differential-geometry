import DifferentialGeometry.Geometry.Exponential.Flat.NormalThreeNormalizer
import DifferentialGeometry.Geometry.Exponential.Flat.OrderThreeLineHolonomy

/-!
Every actual order-three rotation normalizer in a free positive lattice affine point group
fixes its screw axis. Its finite point subgroup is cyclic and centralizes the cubic subgroup,
providing actual normalizer data for the normal-complement theorem.
-/

set_option autoImplicit false

noncomputable section

open Module
open scoped IsMulCommutative

namespace DifferentialGeometry.Geometry.FlatSurface

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem cube_normalizer_conjugate_cases (H : Type*) [instH : Group H]
    (r : H) (hr3 : r ^ 3 = 1) (hrn : r ≠ 1) (a : H)
    (ha : a ∈ Subgroup.normalizer (Subgroup.zpowers r : Set H)) :
    a * r * a⁻¹ = r ∨ a * r * a⁻¹ = r⁻¹ := by
  have horder : orderOf r = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hr3) with h | h
    · exact False.elim (hrn (orderOf_eq_one_iff.mp h))
    · exact h
  have hf : IsOfFinOrder r := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by decide, hr3⟩
  let e : Fin 3 ≃ Subgroup.zpowers r := (finCongr horder.symm).trans (finEquivZPowers hf)
  have hm : a * r * a⁻¹ ∈ Subgroup.zpowers r := (ha r).mp (Subgroup.mem_zpowers r)
  let c : Subgroup.zpowers r := ⟨a * r * a⁻¹, hm⟩
  obtain ⟨i, hi⟩ := e.surjective c
  have hp : r ^ (i : ℕ) = a * r * a⁻¹ := by
    have he := congrArg Subtype.val hi
    change r ^ ((finCongr horder.symm) i : ℕ) = a * r * a⁻¹ at he
    simpa using he
  have hne : a * r * a⁻¹ ≠ 1 := by
    intro he
    apply hrn
    have hh := congrArg (fun x : H => a⁻¹ * x * a) he
    simpa [mul_assoc] using hh
  fin_cases i
  · exact False.elim (hne (by simpa only [pow_zero] using hp.symm))
  · left
    simpa only [pow_one] using hp.symm
  · right
    have hri : r ^ 2 = r⁻¹ := by
      apply eq_inv_iff_mul_eq_one.mpr
      rw [← pow_succ]
      exact hr3
    exact hp.symm.trans hri

theorem affineFree_orderThree_normalizer_fixes_axis (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hpos : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap)
    (g k : G) (hg3 : g.val.linearIsometryEquiv ^ 3 = 1)
    (hgn : g.val.linearIsometryEquiv ≠ 1)
    (hconj : k.val.linearIsometryEquiv * g.val.linearIsometryEquiv *
      k.val.linearIsometryEquiv⁻¹ = g.val.linearIsometryEquiv ∨
      k.val.linearIsometryEquiv * g.val.linearIsometryEquiv *
        k.val.linearIsometryEquiv⁻¹ = g.val.linearIsometryEquiv⁻¹)
    (q : E3) (hq : q ≠ 0) (hfix : g.val.linearIsometryEquiv q = q) :
    k.val.linearIsometryEquiv q = q := by
  rcases orderThree_normalizer_preserves_axis g.val.linearIsometryEquiv
      k.val.linearIsometryEquiv hg3 hgn (hpos g) hconj q hq hfix with he | he
  · exact he
  · exfalso
    have hk2 := affineFree_lineReverse_involution G b hb hfree k (hpos k) q hq he
    have hkg : (k * g).val.linearIsometryEquiv q = -q := by
      change k.val.linearIsometryEquiv (g.val.linearIsometryEquiv q) = -q
      rw [hfix]
      exact he
    have hkg2 := affineFree_lineReverse_involution G b hb hfree (k * g) (hpos (k * g))
      q hq hkg
    change (k.val.linearIsometryEquiv * g.val.linearIsometryEquiv) ^ 2 = 1 at hkg2
    have hc := involutions_product_conjugate_inverse k.val.linearIsometryEquiv
      g.val.linearIsometryEquiv hk2 hkg2
    exact affineFree_dihedralThree_obstruction G hfree g k hg3 hgn (hpos g)
      hk2 hc q hq hfix he

theorem affineFree_orderThree_normalizer_isCyclic (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hpos : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap)
    (r : (affineLinearHom.comp G.subtype).range) (hr3 : r ^ 3 = 1) (hrn : r ≠ 1) :
    IsCyclic (Subgroup.normalizer (Subgroup.zpowers r :
      Set (affineLinearHom.comp G.subtype).range)) := by
  let H := (affineLinearHom.comp G.subtype).range
  let N := Subgroup.normalizer (Subgroup.zpowers r : Set H)
  let J := N.map H.subtype
  let e : N ≃* J := N.equivMapOfInjective H.subtype Subtype.val_injective
  let instJ : Finite J := Finite.of_equiv N e.toEquiv
  obtain ⟨g, hgr⟩ := r.property
  change g.val.linearIsometryEquiv = r.val at hgr
  have hg3 : g.val.linearIsometryEquiv ^ 3 = 1 := by
    rw [hgr]
    exact congrArg Subtype.val hr3
  have hgn : g.val.linearIsometryEquiv ≠ 1 := by
    intro he
    apply hrn
    apply Subtype.ext
    rw [← hgr]
    exact he
  have hg : g ≠ 1 := by intro he; apply hgn; rw [he]; rfl
  obtain ⟨p, q, hp, hfix⟩ := exists_affineAxis_point g.val
  have hq : q ≠ 0 := by
    intro he
    exact hfree g hg p (by simpa only [he, add_zero] using hp)
  have hpJ (d : J) : 0 < LinearMap.det d.val.toLinearMap := by
    obtain ⟨a, ha, he⟩ := d.property
    obtain ⟨k, hk⟩ := a.property
    rw [← he]
    change 0 < LinearMap.det a.val.toLinearMap
    change k.val.linearIsometryEquiv = a.val at hk
    rw [← hk]
    exact hpos k
  have hfixJ (d : J) : d.val q = q := by
    obtain ⟨a, ha, he⟩ := d.property
    have hcases := cube_normalizer_conjugate_cases H r hr3 hrn a ha
    obtain ⟨k, hk⟩ := a.property
    change k.val.linearIsometryEquiv = a.val at hk
    have hcL : k.val.linearIsometryEquiv * g.val.linearIsometryEquiv *
        k.val.linearIsometryEquiv⁻¹ = g.val.linearIsometryEquiv ∨
        k.val.linearIsometryEquiv * g.val.linearIsometryEquiv *
          k.val.linearIsometryEquiv⁻¹ = g.val.linearIsometryEquiv⁻¹ := by
      rcases hcases with h | h
      · left
        have hv := congrArg Subtype.val h
        change a.val * r.val * a.val⁻¹ = r.val at hv
        rw [← hk, ← hgr] at hv
        exact hv
      · right
        have hv := congrArg Subtype.val h
        change a.val * r.val * a.val⁻¹ = r.val⁻¹ at hv
        rw [← hk, ← hgr] at hv
        exact hv
    rw [← he]
    change a.val q = q
    rw [← hk]
    exact affineFree_orderThree_normalizer_fixes_axis G b hb hfree hpos g k
      hg3 hgn hcL q hq hfix
  let instCyclic : IsCyclic J := finitePositive_fixedAxis_isCyclic J hpJ q hq hfixJ
  exact isCyclic_of_injective e.toMonoidHom e.injective

theorem affineFree_orderThree_normalizer_le_centralizer (G : Subgroup (E3 ≃ᵃⁱ[ℝ] E3))
    [instH : Finite (affineLinearHom.comp G.subtype).range] (b : Basis (Fin 3) ℝ E3)
    (hb : Submodule.span ℤ (Set.range b) = affineTranslationModule G)
    (hfree : ∀ γ : G, γ ≠ 1 → ∀ x : E3, γ.val x ≠ x)
    (hpos : ∀ γ : G, 0 < LinearMap.det γ.val.linearIsometryEquiv.toLinearMap)
    (r : (affineLinearHom.comp G.subtype).range) (hr3 : r ^ 3 = 1) (hrn : r ≠ 1) :
    Subgroup.normalizer (Subgroup.zpowers r : Set (affineLinearHom.comp G.subtype).range) ≤
      Subgroup.centralizer (Subgroup.zpowers r : Set (affineLinearHom.comp G.subtype).range) := by
  let H := (affineLinearHom.comp G.subtype).range
  let N := Subgroup.normalizer (Subgroup.zpowers r : Set H)
  let instCyclic : IsCyclic N :=
    affineFree_orderThree_normalizer_isCyclic G b hb hfree hpos r hr3 hrn
  intro a ha k hk
  let na : N := ⟨a, ha⟩
  let nk : N := ⟨k, (Subgroup.zpowers r).le_normalizer hk⟩
  exact congrArg Subtype.val (mul_comm nk na)

end DifferentialGeometry.Geometry.FlatSurface
