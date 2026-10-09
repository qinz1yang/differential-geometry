import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Int.GCD
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Seifert arithmetic: three cone points with positive orbifold Euler characteristic

A closed Seifert manifold over `S²` with exactly three genuine cone points `(pᵢ, qᵢ)`, `pᵢ ≥ 2`,
`gcd (pᵢ, qᵢ) = 1`, and positive orbifold Euler characteristic `1/p₁ + 1/p₂ + 1/p₃ > 1` has
nonzero Euler number `e = -∑ qᵢ/pᵢ` (Scott 1983, p. 459). Up to order the cone orders are
`(2, 2, n)`, `(2, 3, 3)`, `(2, 3, 4)` or `(2, 3, 5)` (`exists_platonic_perm`, via `Tuple.sort`),
and in each case clearing denominators leaves an integer identity whose residues contradict the
coprimality of some `(pᵢ, qᵢ)` (`sum_div_ne_zero_of_three_cones`).

The two closing examples show that neither `pᵢ ≥ 2` nor the strict inequality can be dropped:
`(1, 0), (2, 1), (2, -1)` has positive characteristic and vanishing sum, and
`(3, 1), (3, 1), (3, -2)` has three genuine cone points, characteristic zero and vanishing sum.
-/

namespace GC.Seifert

private lemma sorted_shape (a b c : ℕ) (ha : 2 ≤ a) (hab : a ≤ b) (hbc : b ≤ c)
    (h : a * b * c < b * c + a * c + a * b) :
    (a = 2 ∧ b = 2) ∨ (a = 2 ∧ b = 3 ∧ (c = 3 ∨ c = 4 ∨ c = 5)) := by
  have ha2 : a = 2 := by
    by_contra hne
    have h3 : 3 ≤ a := by omega
    have h1 : a * c ≤ b * c := Nat.mul_le_mul_right c hab
    have h2 : a * b ≤ c * b := Nat.mul_le_mul_right b (hab.trans hbc)
    have h4 : 3 * (b * c) ≤ a * (b * c) := Nat.mul_le_mul_right (b * c) h3
    nlinarith
  subst ha2
  have hb : b ≤ 3 := by
    by_contra hne
    have h4 : 4 * c ≤ b * c := Nat.mul_le_mul_right c (by omega)
    nlinarith
  interval_cases b <;> omega

private lemma mul_lt_of_one_lt_sum (a b c : ℕ) (ha : 2 ≤ a) (hb : 2 ≤ b) (hc : 2 ≤ c)
    (h : (1 : ℚ) < 1 / a + 1 / b + 1 / c) : a * b * c < b * c + a * c + a * b := by
  have ha0 : (0 : ℚ) < a := by exact_mod_cast (by omega : 0 < a)
  have hb0 : (0 : ℚ) < b := by exact_mod_cast (by omega : 0 < b)
  have hc0 : (0 : ℚ) < c := by exact_mod_cast (by omega : 0 < c)
  have e : (1 : ℚ) / a + 1 / b + 1 / c = (b * c + a * c + a * b) / (a * b * c) := by
    field_simp
  rw [e, lt_div_iff₀ (by positivity)] at h
  have h' : ((a * b * c : ℕ) : ℚ) < ((b * c + a * c + a * b : ℕ) : ℚ) := by
    push_cast
    linarith
  exact_mod_cast h'

theorem exists_platonic_perm (p : Fin 3 → ℕ) (hp : ∀ i, 2 ≤ p i)
    (hχ : (1 : ℚ) < ∑ i, (1 : ℚ) / (p i : ℚ)) :
    ∃ σ : Equiv.Perm (Fin 3), (p (σ 0) = 2 ∧ p (σ 1) = 2) ∨
      (p (σ 0) = 2 ∧ p (σ 1) = 3 ∧ (p (σ 2) = 3 ∨ p (σ 2) = 4 ∨ p (σ 2) = 5)) := by
  refine ⟨Tuple.sort p, ?_⟩
  have hm := Tuple.monotone_sort p
  rw [← Equiv.sum_comp (Tuple.sort p), Fin.sum_univ_three] at hχ
  exact sorted_shape _ _ _ (hp _) (hm (by decide : (0 : Fin 3) ≤ 1))
    (hm (by decide : (1 : Fin 3) ≤ 2))
    (mul_lt_of_one_lt_sum _ _ _ (hp _) (hp _) (hp _) hχ)

private lemma false_of_common_dvd {m d : ℕ} {n : ℤ} (h : Int.gcd (m : ℤ) n = 1) (hd : 2 ≤ d)
    (hm : (d : ℤ) ∣ m) (hn : (d : ℤ) ∣ n) : False := by
  have h1 := Int.dvd_gcd hm hn
  rw [h, Nat.dvd_one] at h1
  omega

private lemma ne_zero_of_shape (a b c : ℕ) (x y z : ℤ) (hc : 2 ≤ c)
    (hx : Int.gcd (a : ℤ) x = 1) (hy : Int.gcd (b : ℤ) y = 1) (hz : Int.gcd (c : ℤ) z = 1)
    (hs : (a = 2 ∧ b = 2) ∨ (a = 2 ∧ b = 3 ∧ (c = 3 ∨ c = 4 ∨ c = 5))) :
    (x : ℚ) / a + y / b + z / c ≠ 0 := by
  intro h
  rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl | rfl | rfl⟩
  · have hc0 : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
    have e : (c : ℤ) * (x + y) + 2 * z = 0 := by
      have e' : ((c : ℤ) * (x + y) + 2 * z : ℚ) = 0 := by
        push_cast at h ⊢
        field_simp at h
        linarith
      exact_mod_cast e'
    have hx2 : ¬ ((2 : ℕ) : ℤ) ∣ x := false_of_common_dvd hx le_rfl dvd_rfl
    have hy2 : ¬ ((2 : ℕ) : ℤ) ∣ y := false_of_common_dvd hy le_rfl dvd_rfl
    obtain ⟨k, hk⟩ : (2 : ℤ) ∣ x + y := by omega
    rw [hk] at e
    exact false_of_common_dvd hz hc dvd_rfl ⟨-k, by linarith⟩
  · have e : 3 * x + 2 * y + 2 * z = 0 := by
      have e' : (3 * x + 2 * y + 2 * z : ℚ) = 0 := by push_cast at h; linarith
      exact_mod_cast e'
    exact false_of_common_dvd (d := 2) hx le_rfl dvd_rfl (by omega)
  · have e : 6 * x + 4 * y + 3 * z = 0 := by
      have e' : (6 * x + 4 * y + 3 * z : ℚ) = 0 := by push_cast at h; linarith
      exact_mod_cast e'
    exact false_of_common_dvd (d := 2) hz le_rfl (by norm_num) (by omega)
  · have e : 15 * x + 10 * y + 6 * z = 0 := by
      have e' : (15 * x + 10 * y + 6 * z : ℚ) = 0 := by push_cast at h; linarith
      exact_mod_cast e'
    exact false_of_common_dvd (d := 2) hx le_rfl dvd_rfl (by omega)

theorem sum_div_ne_zero_of_three_cones (p : Fin 3 → ℕ) (q : Fin 3 → ℤ)
    (hp : ∀ i, 2 ≤ p i) (hcop : ∀ i, Int.gcd (p i : ℤ) (q i) = 1)
    (hχ : (1 : ℚ) < ∑ i, (1 : ℚ) / (p i : ℚ)) :
    ∑ i, (q i : ℚ) / (p i : ℚ) ≠ 0 := by
  obtain ⟨σ, hσ⟩ := exists_platonic_perm p hp hχ
  rw [← Equiv.sum_comp σ, Fin.sum_univ_three]
  exact ne_zero_of_shape _ _ _ _ _ _ (hp _) (hcop _) (hcop _) (hcop _) hσ

example :
    (∀ i, Int.gcd ((![1, 2, 2] : Fin 3 → ℕ) i : ℤ) ((![0, 1, -1] : Fin 3 → ℤ) i) = 1) ∧
      (1 : ℚ) < ∑ i, (1 : ℚ) / ((![1, 2, 2] : Fin 3 → ℕ) i : ℚ) ∧
      ∑ i, ((![0, 1, -1] : Fin 3 → ℤ) i : ℚ) / ((![1, 2, 2] : Fin 3 → ℕ) i : ℚ) = 0 := by
  refine ⟨fun i => ?_, ?_, ?_⟩
  · fin_cases i <;> rfl
  · norm_num [Fin.sum_univ_three]
  · norm_num [Fin.sum_univ_three]

example :
    (∀ i, 2 ≤ (![3, 3, 3] : Fin 3 → ℕ) i) ∧
      (∀ i, Int.gcd ((![3, 3, 3] : Fin 3 → ℕ) i : ℤ) ((![1, 1, -2] : Fin 3 → ℤ) i) = 1) ∧
      ∑ i, (1 : ℚ) / ((![3, 3, 3] : Fin 3 → ℕ) i : ℚ) = 1 ∧
      ∑ i, ((![1, 1, -2] : Fin 3 → ℤ) i : ℚ) / ((![3, 3, 3] : Fin 3 → ℕ) i : ℚ) = 0 := by
  refine ⟨fun i => ?_, fun i => ?_, ?_, ?_⟩
  · fin_cases i <;> decide
  · fin_cases i <;> rfl
  · norm_num [Fin.sum_univ_three]
  · norm_num [Fin.sum_univ_three]

end GC.Seifert
