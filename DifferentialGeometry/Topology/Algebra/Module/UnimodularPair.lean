import Mathlib.RingTheory.Coprime.Basic
import Mathlib.Data.Int.Order.Units
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.Ring

set_option autoImplicit false

namespace IsCoprime

variable {R : Type*} [CommRing R] {a b c d : R}

theorem det_eq_zero_iff (h : IsCoprime a b) :
    a * d - b * c = 0 ↔ ∃ r : R, c = r * a ∧ d = r * b := by
  constructor
  · intro hdet
    obtain ⟨u, v, huv⟩ := h
    refine ⟨u * c + v * d, ?_, ?_⟩
    · linear_combination -c * huv - v * hdet
    · linear_combination -d * huv + u * hdet
  · rintro ⟨r, rfl, rfl⟩
    ring

theorem exists_unit_mul_of_det_eq_zero (h : IsCoprime a b) (h' : IsCoprime c d)
    (hdet : a * d - b * c = 0) :
    ∃ u : Rˣ, c = u * a ∧ d = u * b := by
  obtain ⟨r, hc, hd⟩ := h.det_eq_zero_iff.mp hdet
  obtain ⟨u, hu⟩ := h'.isUnit_of_dvd' ⟨a, hc⟩ ⟨b, hd⟩
  exact ⟨u, hu.symm ▸ hc, hu.symm ▸ hd⟩

theorem injective_smul_pair (h : IsCoprime a b) (M : Type*)
    [AddCommGroup M] [Module R M] :
    Function.Injective (fun x : M => (a • x, b • x)) := by
  obtain ⟨u, v, huv⟩ := h
  intro x y hxy
  have ha : a • x = a • y := congrArg Prod.fst hxy
  have hb : b • x = b • y := congrArg Prod.snd hxy
  calc
    x = (u * a + v * b) • x := by rw [huv, one_smul]
    _ = u • (a • x) + v • (b • x) := by rw [add_smul, mul_smul, mul_smul]
    _ = u • (a • y) + v • (b • y) := by rw [ha, hb]
    _ = (u * a + v * b) • y := by rw [add_smul, mul_smul, mul_smul]
    _ = y := by rw [huv, one_smul]

theorem mem_range_smul_pair_iff (h : IsCoprime a b) {M : Type*}
    [AddCommGroup M] [Module R M] (x y : M) :
    (x, y) ∈ Set.range (fun t : M => (a • t, b • t)) ↔ b • x = a • y := by
  constructor
  · rintro ⟨t, ht⟩
    cases ht
    rw [smul_smul, smul_smul, mul_comm]
  · intro hxy
    obtain ⟨u, v, huv⟩ := h
    refine ⟨u • x + v • y, Prod.ext ?_ ?_⟩
    · calc
        a • (u • x + v • y) = u • (a • x) + v • (a • y) := by
          simp only [smul_add, smul_smul, mul_comm]
        _ = u • (a • x) + v • (b • x) := by rw [hxy]
        _ = (u * a + v * b) • x := by rw [add_smul, smul_smul, smul_smul]
        _ = x := by rw [huv, one_smul]
    · calc
        b • (u • x + v • y) = u • (b • x) + v • (b • y) := by
          simp only [smul_add, smul_smul, mul_comm]
        _ = u • (a • y) + v • (b • y) := by rw [hxy]
        _ = (u * a + v * b) • y := by rw [add_smul, smul_smul, smul_smul]
        _ = y := by rw [huv, one_smul]

end IsCoprime

namespace Int

theorem det_eq_zero_iff_eq_or_eq_neg {a b c d : ℤ}
    (h : IsCoprime a b) (h' : IsCoprime c d) :
    a * d - b * c = 0 ↔ (c = a ∧ d = b) ∨ (c = -a ∧ d = -b) := by
  constructor
  · intro hdet
    obtain ⟨u, hc, hd⟩ := h.exists_unit_mul_of_det_eq_zero h' hdet
    rcases Int.isUnit_iff.mp u.isUnit with hu | hu
    · left
      simpa only [hu, one_mul] using And.intro hc hd
    · right
      simpa only [hu, neg_one_mul] using And.intro hc hd
  · rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩) <;> ring

end Int

namespace Matrix

variable {R : Type*} [CommRing R]

theorem det_pair_mulVec (A : Matrix (Fin 2) (Fin 2) R) (v w : Fin 2 → R) :
    (A *ᵥ v) 0 * (A *ᵥ w) 1 - (A *ᵥ v) 1 * (A *ᵥ w) 0 =
      A.det * (v 0 * w 1 - v 1 * w 0) := by
  simp only [mulVec, dotProduct, Fin.sum_univ_two, det_fin_two]
  ring

theorem isCoprime_mulVec_of_isUnit_det (A : Matrix (Fin 2) (Fin 2) R)
    (hA : IsUnit A.det) {v : Fin 2 → R} (hv : IsCoprime (v 0) (v 1)) :
    IsCoprime ((A *ᵥ v) 0) ((A *ᵥ v) 1) := by
  obtain ⟨u, w, huw⟩ := hv
  obtain ⟨r, hr⟩ := isUnit_iff_exists_inv'.mp hA
  refine ⟨r * (u * A 1 1 - w * A 1 0),
    r * (w * A 0 0 - u * A 0 1), ?_⟩
  simp only [mulVec, dotProduct, Fin.sum_univ_two]
  rw [det_fin_two] at hr
  linear_combination r * (A 0 0 * A 1 1 - A 0 1 * A 1 0) * huw + hr

theorem abs_det_pair_mulVec (A : Matrix (Fin 2) (Fin 2) ℤ)
    (hA : IsUnit A.det) (v w : Fin 2 → ℤ) :
    |(A *ᵥ v) 0 * (A *ᵥ w) 1 - (A *ᵥ v) 1 * (A *ᵥ w) 0| =
      |v 0 * w 1 - v 1 * w 0| := by
  rw [det_pair_mulVec, abs_mul, Int.isUnit_iff_abs_eq.mp hA, one_mul]

end Matrix
