import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.Perm.Cycle.Type

/-!
A normal actual order-three cyclic subgroup has only the two inverse-normalizer generator
images. Every finite six-element group supplies such a subgroup by Cauchy's theorem and
its actual index two, without a normalizer or cyclic classification premise.
-/

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.Geometry.FlatSurface

theorem normal_cube_zpowers_inverseNormalizer (H : Type*) [instH : Group H]
    (r : H) (hr3 : r ^ 3 = 1) (hrn : r ≠ 1) (hn : (Subgroup.zpowers r).Normal) :
    ∀ a : H, a * r * a⁻¹ = r ∨ a * r * a⁻¹ = r⁻¹ := by
  have horder : orderOf r = 3 := by
    rcases (Nat.dvd_prime Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hr3) with h | h
    · exact False.elim (hrn (orderOf_eq_one_iff.mp h))
    · exact h
  have hf : IsOfFinOrder r := isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by decide, hr3⟩
  let e : Fin 3 ≃ Subgroup.zpowers r := (finCongr horder.symm).trans (finEquivZPowers hf)
  intro a
  have hm : a * r * a⁻¹ ∈ Subgroup.zpowers r := hn.conj_mem r (Subgroup.mem_zpowers r) a
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

theorem exists_normal_three_of_card_six (H : Type*) [instH : Group H] [instF : Finite H]
    (hc : Nat.card H = 6) : ∃ r : H, orderOf r = 3 ∧ (Subgroup.zpowers r).Normal := by
  let instFintype : Fintype H := Fintype.ofFinite H
  let instPrime : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd : 3 ∣ Fintype.card H := by rw [← Nat.card_eq_fintype_card, hc]; norm_num
  obtain ⟨r, hr⟩ := exists_prime_orderOf_dvd_card 3 hd
  have hzr : Nat.card (Subgroup.zpowers r) = 3 := (Nat.card_zpowers r).trans hr
  have hi : (Subgroup.zpowers r).index = 2 := by
    have he := (Subgroup.zpowers r).card_mul_index
    rw [hzr, hc] at he
    omega
  exact ⟨r, hr, Subgroup.normal_of_index_eq_two hi⟩

end DifferentialGeometry.Geometry.FlatSurface
