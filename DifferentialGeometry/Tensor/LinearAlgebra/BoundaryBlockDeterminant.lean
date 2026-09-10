import Mathlib.LinearAlgebra.Determinant
import Mathlib.Data.Real.Basic

noncomputable section
open Module

namespace Poincare.Analysis

theorem det_eq_normal_mul_of_horizontal
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (L : (ℝ × E) →ₗ[ℝ] (ℝ × E)) (A : E →ₗ[ℝ] E)
    (hA : ∀ z, L (0, z) = (0, A z)) :
    L.det = (L (1, 0)).1 * A.det := by
  classical
  let b₀ : Basis Unit ℝ ℝ := Basis.singleton Unit ℝ
  let b := Module.Free.chooseBasis ℝ E
  let : Fintype (Module.Free.ChooseBasisIndex ℝ E) := Module.Free.ChooseBasisIndex.fintype ℝ E
  let N : Matrix Unit Unit ℝ := fun _ _ ↦ (L (1, 0)).1
  let C : Matrix (Module.Free.ChooseBasisIndex ℝ E) Unit ℝ := fun i _ ↦ b.repr (L (1, 0)).2 i
  have hm : LinearMap.toMatrix (b₀.prod b) (b₀.prod b) L =
      Matrix.fromBlocks N 0 C (LinearMap.toMatrix b b A) := by
    ext (i | i) (j | j) <;>
      simp [LinearMap.toMatrix_apply, Basis.prod_apply, Matrix.fromBlocks, b₀, N, C, hA]
  rw [← LinearMap.det_toMatrix (b₀.prod b), hm, Matrix.det_fromBlocks_zero₁₂,
    LinearMap.det_toMatrix]
  have hN : N.det = (L (1, 0)).1 := Matrix.det_unique N
  rw [hN]

theorem normal_coefficient_pos_of_surjective
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    (L : (ℝ × E) →ₗ[ℝ] (ℝ × E)) (A : E →ₗ[ℝ] E)
    (hA : ∀ z, L (0, z) = (0, A z)) (hL : Function.Surjective L)
    (hn : 0 ≤ (L (1, 0)).1) : 0 < (L (1, 0)).1 := by
  have hnz : (L (1, 0)).1 ≠ 0 := by
    intro hz
    obtain ⟨q, hq⟩ := hL (1, 0)
    have heq : q = q.1 • ((1 : ℝ), (0 : E)) + (0, q.2) := by ext <;> simp
    have h := congrArg Prod.fst hq
    rw [heq, map_add, map_smul, hA] at h
    change q.1 * (L (1, 0)).1 + 0 = 1 at h
    rw [hz, mul_zero, zero_add] at h
    exact zero_ne_one h
  exact lt_of_le_of_ne hn hnz.symm

theorem det_pos_iff_horizontal_of_surjective
    {E : Type*} [AddCommGroup E] [Module ℝ E] [FiniteDimensional ℝ E]
    (L : (ℝ × E) →ₗ[ℝ] (ℝ × E)) (A : E →ₗ[ℝ] E)
    (hA : ∀ z, L (0, z) = (0, A z)) (hL : Function.Surjective L)
    (hn : 0 ≤ (L (1, 0)).1) : 0 < L.det ↔ 0 < A.det := by
  rw [det_eq_normal_mul_of_horizontal L A hA]
  exact mul_pos_iff_of_pos_left (normal_coefficient_pos_of_surjective L A hA hL hn)

end Poincare.Analysis
