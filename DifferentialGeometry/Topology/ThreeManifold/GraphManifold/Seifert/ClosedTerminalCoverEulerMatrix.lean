import Mathlib.Analysis.SpecialFunctions.Complex.Log
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.GroupTheory.NoncommCoprod
import Mathlib.GroupTheory.FreeGroup.Basic
import Mathlib.Algebra.Ring.Parity

/-!
# Unimodular matrices for the three-cone relations

A `2 × 2` complex matrix of determinant one and trace `u + u⁻¹` satisfies `M² = (u + u⁻¹) M - 1`,
hence `(u - u⁻¹) Mⁿ⁺¹ = (uⁿ⁺¹ - u⁻ⁿ⁻¹) M - (uⁿ - u⁻ⁿ)` (`closedTriangleMatrix_pow_formula`); if
`u ≠ u⁻¹` and `uᵖ = u⁻ᵖ = ε` then `Mᵖ = ε` (`closedTriangleMatrix_pow`). For a cone `(p, q)` with
`2 ≤ p`, `gcd(p, q) = 1` take `u = exp(π i q / p)`: then `uᵖ = (-1)^q` and `u ≠ u⁻¹`.

The matrices `X = !![t₁, 1; -1, 0]` and `Y = !![0, -s; s⁻¹, t₂]` have determinant one, traces `t₁`,
`t₂`, and `YX = !![s, 0; s⁻¹ t₁ - t₂, s⁻¹]` has trace `s + s⁻¹`; so every triple of traces is
realised (Fricke). With the three roots of the three cones this gives a homomorphism from
`F(a, b) × ℤ` to `GL₂(ℂ)` sending `a ↦ X`, `b ↦ Y`, the fibre to `-1`, and killing
`w_j ^ p_j · h ^ q_j` for `w = ((ba)⁻¹, a, b)` (`exists_closedTriangleMatrixHom`). Nothing about the
Euler number or the orbifold characteristic is used.
-/

set_option autoImplicit false

noncomputable section

open Multiplicative

namespace GC.Seifert

abbrev ClosedTriangleGL := (Matrix (Fin 2) (Fin 2) ℂ)ˣ

theorem closedTriangleMatrix_mul_self (M : Matrix (Fin 2) (Fin 2) ℂ) :
    M * M = M.trace • M - M.det • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.trace_fin_two, Matrix.det_fin_two] <;> ring

theorem closedTriangleMatrix_pow_formula (M : Matrix (Fin 2) (Fin 2) ℂ) (u v : ℂ)
    (huv : u * v = 1) (htr : M.trace = u + v) (hdet : M.det = 1) (n : ℕ) :
    (u - v) • M ^ (n + 1) = (u ^ (n + 1) - v ^ (n + 1)) • M - (u ^ n - v ^ n) • 1 := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hc : (u ^ (n + 1) - v ^ (n + 1)) * (u + v) - (u ^ n - v ^ n) =
        u ^ (n + 1 + 1) - v ^ (n + 1 + 1) := by
      linear_combination (u ^ n - v ^ n) * huv
    rw [pow_succ M (n + 1), ← smul_mul_assoc, ih, sub_mul, smul_mul_assoc, smul_mul_assoc,
      one_mul, closedTriangleMatrix_mul_self, htr, hdet, ← hc]
    simp only [smul_sub, smul_smul, sub_smul, one_smul]
    abel

theorem closedTriangleMatrix_pow (M : Matrix (Fin 2) (Fin 2) ℂ) (u v ε : ℂ) (huv : u * v = 1)
    (hne : u ≠ v) (htr : M.trace = u + v) (hdet : M.det = 1) (p : ℕ) (hu : u ^ p = ε)
    (hv : v ^ p = ε) : M ^ p = ε • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rcases p with _ | n
  · rw [pow_zero] at hu
    rw [pow_zero, ← hu, one_smul]
  · have h := closedTriangleMatrix_pow_formula M u v huv htr hdet n
    have hun : u ^ n = ε * v := by
      rw [← hu, pow_succ, mul_assoc, huv, mul_one]
    have hvn : v ^ n = ε * u := by
      rw [← hv, pow_succ, mul_assoc, mul_comm v u, huv, mul_one]
    rw [hu, hv, sub_self, zero_smul, zero_sub, hun, hvn] at h
    have hsub : u - v ≠ 0 := sub_ne_zero.mpr hne
    have h' : (u - v) • M ^ (n + 1) = (u - v) • (ε • (1 : Matrix (Fin 2) (Fin 2) ℂ)) := by
      rw [h, smul_smul, ← neg_smul]
      congr 1
      ring
    exact smul_right_injective _ hsub h'

def closedTriangleRoot (p q : ℤ) : ℂ := Complex.exp (Real.pi * Complex.I * q / p)

theorem closedTriangleRoot_mul_inv (p q : ℤ) :
    closedTriangleRoot p q * (closedTriangleRoot p q)⁻¹ = 1 :=
  mul_inv_cancel₀ (Complex.exp_ne_zero _)

theorem closedTriangleRoot_pow (p q : ℤ) (n : ℕ) (hn : (n : ℤ) = p) (hp : p ≠ 0) :
    closedTriangleRoot p q ^ n = (-1 : ℂ) ^ q := by
  rw [closedTriangleRoot, ← Complex.exp_nat_mul, ← Complex.exp_pi_mul_I, ← Complex.exp_int_mul]
  congr 1
  have hp' : (p : ℂ) ≠ 0 := Int.cast_ne_zero.mpr hp
  have hn' : (n : ℂ) = p := by exact_mod_cast hn
  rw [hn']
  field_simp

theorem closedTriangleRoot_inv_pow (p q : ℤ) (n : ℕ) (hn : (n : ℤ) = p) (hp : p ≠ 0) :
    (closedTriangleRoot p q)⁻¹ ^ n = (-1 : ℂ) ^ q := by
  rw [inv_pow, closedTriangleRoot_pow p q n hn hp, ← inv_zpow, inv_neg, inv_one]

theorem closedTriangleRoot_ne_inv (p q : ℤ) (hp : 2 ≤ p) (hpq : Int.gcd p q = 1) :
    closedTriangleRoot p q ≠ (closedTriangleRoot p q)⁻¹ := by
  intro h
  have h1 : closedTriangleRoot p q * closedTriangleRoot p q = 1 := by
    nth_rewrite 2 [h]
    exact closedTriangleRoot_mul_inv p q
  rw [closedTriangleRoot, ← Complex.exp_add, Complex.exp_eq_one_iff] at h1
  obtain ⟨n, hn⟩ := h1
  have hp' : (p : ℂ) ≠ 0 := Int.cast_ne_zero.mpr (by omega)
  have hπ : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
  have hq : (q : ℂ) = n * p := by
    field_simp at hn
    linear_combination hn / 2
  have hq' : q = n * p := by exact_mod_cast hq
  have hdvd : p ∣ q := ⟨n, by rw [hq', mul_comm]⟩
  have hg := Int.gcd_eq_natAbs_left_iff_dvd.mpr hdvd
  rw [hpq] at hg
  omega

def closedTriangleUnit (M : Matrix (Fin 2) (Fin 2) ℂ) (h : M.det = 1) : ClosedTriangleGL :=
  Matrix.nonsingInvUnit M (h.symm ▸ isUnit_one)

theorem val_closedTriangleUnit (M : Matrix (Fin 2) (Fin 2) ℂ) (h : M.det = 1) :
    (closedTriangleUnit M h : Matrix (Fin 2) (Fin 2) ℂ) = M := rfl

theorem closedTriangle_neg_one_zpow_val (q : ℤ) :
    (((-1 : ClosedTriangleGL) ^ q : ClosedTriangleGL) : Matrix (Fin 2) (Fin 2) ℂ) =
      ((-1 : ℂ) ^ q) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [neg_one_zpow_eq_ite, neg_one_zpow_eq_ite]
  split_ifs
  · simp
  · simp

theorem closedTriangleUnit_zpow (Z : ClosedTriangleGL) (n : ℕ) (q : ℤ)
    (h : (Z : Matrix (Fin 2) (Fin 2) ℂ) ^ n = ((-1 : ℂ) ^ q) • 1) :
    Z ^ (n : ℤ) = (-1) ^ q := by
  apply Units.ext
  rw [zpow_natCast, Units.val_pow_eq_pow_val, h, closedTriangle_neg_one_zpow_val]

theorem closedTriangle_neg_one_zpow_mul_self (q : ℤ) :
    ((-1 : ClosedTriangleGL) ^ q) * (-1) ^ q = 1 := by
  rw [← zpow_add]
  exact Even.neg_one_zpow ⟨q, rfl⟩

theorem closedTriangle_commute_neg_one_zpow (x : ClosedTriangleGL) (q : ℤ) :
    Commute x ((-1) ^ q) :=
  (Commute.neg_one_right x).zpow_right q

def closedTriangleMatrixHom (X Y : ClosedTriangleGL) :
    FreeGroup (Fin 2) × Multiplicative ℤ →* ClosedTriangleGL :=
  MonoidHom.noncommCoprod (FreeGroup.lift ![X, Y]) (zpowersHom ClosedTriangleGL (-1))
    (fun _ n => by
      rw [zpowersHom_apply]
      exact closedTriangle_commute_neg_one_zpow _ (toAdd n))

theorem closedTriangleMatrixHom_apply (X Y : ClosedTriangleGL) (w : FreeGroup (Fin 2)) (n : ℤ) :
    closedTriangleMatrixHom X Y (w, ofAdd n) = FreeGroup.lift ![X, Y] w * (-1) ^ n := by
  change FreeGroup.lift ![X, Y] w * zpowersHom ClosedTriangleGL (-1) (ofAdd n) = _
  rw [zpowersHom_apply, toAdd_ofAdd]

def closedTriangleMatX (t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![t, 1; -1, 0]

def closedTriangleMatY (s t : ℂ) : Matrix (Fin 2) (Fin 2) ℂ := !![0, -s; s⁻¹, t]

theorem det_closedTriangleMatX (t : ℂ) : (closedTriangleMatX t).det = 1 := by
  simp [closedTriangleMatX, Matrix.det_fin_two]

theorem det_closedTriangleMatY (s t : ℂ) (hs : s ≠ 0) : (closedTriangleMatY s t).det = 1 := by
  simp [closedTriangleMatY, Matrix.det_fin_two, hs]

theorem trace_closedTriangleMatX (t : ℂ) : (closedTriangleMatX t).trace = t := by
  simp [closedTriangleMatX, Matrix.trace_fin_two]

theorem trace_closedTriangleMatY (s t : ℂ) : (closedTriangleMatY s t).trace = t := by
  simp [closedTriangleMatY, Matrix.trace_fin_two]

theorem trace_closedTriangleMatYX (s t t' : ℂ) :
    (closedTriangleMatY s t' * closedTriangleMatX t).trace = s + s⁻¹ := by
  simp [closedTriangleMatX, closedTriangleMatY, Matrix.trace_fin_two]

theorem det_closedTriangleMatYX (s t t' : ℂ) (hs : s ≠ 0) :
    (closedTriangleMatY s t' * closedTriangleMatX t).det = 1 := by
  rw [Matrix.det_mul, det_closedTriangleMatY s t' hs, det_closedTriangleMatX, one_mul]

theorem closedTriangleMatrix_pow_root (M : Matrix (Fin 2) (Fin 2) ℂ) (p q : ℤ) (hp : 2 ≤ p)
    (hpq : Int.gcd p q = 1)
    (htr : M.trace = closedTriangleRoot p q + (closedTriangleRoot p q)⁻¹) (hdet : M.det = 1) :
    M ^ p.toNat = ((-1 : ℂ) ^ q) • 1 := by
  have hn : (p.toNat : ℤ) = p := Int.toNat_of_nonneg (by omega)
  exact closedTriangleMatrix_pow M _ _ _ (closedTriangleRoot_mul_inv p q)
    (closedTriangleRoot_ne_inv p q hp hpq) htr hdet p.toNat
    (closedTriangleRoot_pow p q _ hn (by omega)) (closedTriangleRoot_inv_pow p q _ hn (by omega))

theorem exists_closedTriangleMatrixHom (P Q : Fin 3 → ℤ) (hP : ∀ j, 2 ≤ P j)
    (hPQ : ∀ j, Int.gcd (P j) (Q j) = 1) :
    ∃ ι : FreeGroup (Fin 2) × Multiplicative ℤ →* ClosedTriangleGL,
      ι (1, ofAdd 1) = -1 ∧ ∀ j : Fin 3,
        ι (![(FreeGroup.of 1 * FreeGroup.of 0)⁻¹, FreeGroup.of 0, FreeGroup.of 1] j ^ P j,
          ofAdd (Q j)) = 1 := by
  let u : Fin 3 → ℂ := fun j => closedTriangleRoot (P j) (Q j)
  have hu0 : u 0 ≠ 0 := Complex.exp_ne_zero _
  let A := closedTriangleMatX (u 1 + (u 1)⁻¹)
  let B := closedTriangleMatY (u 0) (u 2 + (u 2)⁻¹)
  let X := closedTriangleUnit A (det_closedTriangleMatX _)
  let Y := closedTriangleUnit B (det_closedTriangleMatY _ _ hu0)
  have hP' : ∀ j, ((P j).toNat : ℤ) = P j := fun j => Int.toNat_of_nonneg (by linarith [hP j])
  have hX : X ^ P 1 = (-1) ^ Q 1 := by
    rw [← hP' 1]
    exact closedTriangleUnit_zpow X _ _ (closedTriangleMatrix_pow_root A (P 1) (Q 1) (hP 1)
      (hPQ 1) (trace_closedTriangleMatX _) (det_closedTriangleMatX _))
  have hY : Y ^ P 2 = (-1) ^ Q 2 := by
    rw [← hP' 2]
    exact closedTriangleUnit_zpow Y _ _ (closedTriangleMatrix_pow_root B (P 2) (Q 2) (hP 2)
      (hPQ 2) (trace_closedTriangleMatY _ _) (det_closedTriangleMatY _ _ hu0))
  have hYX : (Y * X) ^ P 0 = (-1) ^ Q 0 := by
    rw [← hP' 0]
    exact closedTriangleUnit_zpow (Y * X) _ _ (closedTriangleMatrix_pow_root (B * A) (P 0) (Q 0)
      (hP 0) (hPQ 0) (trace_closedTriangleMatYX _ _ _) (det_closedTriangleMatYX _ _ _ hu0))
  have e0 : FreeGroup.lift ![X, Y] (FreeGroup.of 0) = X := by simp
  have e1 : FreeGroup.lift ![X, Y] (FreeGroup.of 1) = Y := by simp
  refine ⟨closedTriangleMatrixHom X Y, ?_, fun j => ?_⟩
  · rw [closedTriangleMatrixHom_apply, map_one, one_mul, zpow_one]
  · rw [closedTriangleMatrixHom_apply]
    fin_cases j
    · change FreeGroup.lift ![X, Y] ((FreeGroup.of 1 * FreeGroup.of 0)⁻¹ ^ P 0) * (-1) ^ Q 0 = 1
      rw [map_zpow, map_inv, map_mul, e0, e1, inv_zpow, hYX, inv_mul_cancel]
    · change FreeGroup.lift ![X, Y] (FreeGroup.of 0 ^ P 1) * (-1) ^ Q 1 = 1
      rw [map_zpow, e0, hX, closedTriangle_neg_one_zpow_mul_self]
    · change FreeGroup.lift ![X, Y] (FreeGroup.of 1 ^ P 2) * (-1) ^ Q 2 = 1
      rw [map_zpow, e1, hY, closedTriangle_neg_one_zpow_mul_self]

theorem closedTriangle_neg_one_ne_one : (-1 : ClosedTriangleGL) ≠ 1 := by
  intro h
  have h1 := congrArg (fun x : ClosedTriangleGL => (x : Matrix (Fin 2) (Fin 2) ℂ) 0 0) h
  norm_num at h1

theorem closedTriangle_neg_one_mem_center (x : ClosedTriangleGL) :
    x * (-1) * x⁻¹ = -1 := by
  rw [mul_neg_one, neg_mul, mul_inv_cancel]

end GC.Seifert
