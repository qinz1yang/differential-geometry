/-
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Hongzhou Lin
-/
import Mathlib.Topology.Instances.Matrix
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Tactic.NormNum

noncomputable section

open Set Filter Matrix
open scoped Topology

namespace DifferentialGeometry.BoundedTorsion

section Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem matrix_eq_one_of_pow_eq_one {A : Matrix ι ι ℝ} {k : ℕ}
    (hs : (∑ i ∈ Finset.range k, A ^ i).det ≠ 0) (hA : A ^ k = 1) :
    A = 1 := by
  have hu : IsUnit (∑ i ∈ Finset.range k, A ^ i) :=
    (Matrix.isUnit_iff_isUnit_det _).mpr (isUnit_iff_ne_zero.mpr hs)
  have h := geom_sum_mul A k
  rw [hA, sub_self] at h
  exact sub_eq_zero.mp (hu.mul_left_cancel (by simpa only [mul_zero] using h))

theorem exists_matrix_nhds_pow_eq_one (k : ℕ) (hk : 0 < k) :
    ∃ V : Set (Matrix ι ι ℝ), IsOpen V ∧ (1 : Matrix ι ι ℝ) ∈ V ∧
      ∀ A ∈ V, A ^ k = 1 → A = 1 := by
  let V : Set (Matrix ι ι ℝ) := {A | (∑ i ∈ Finset.range k, A ^ i).det ≠ 0}
  have hcont : Continuous (fun A : Matrix ι ι ℝ =>
      (∑ i ∈ Finset.range k, A ^ i).det) :=
    (continuous_finsetSum _ (fun i _ => continuous_id.pow i)).matrix_det
  refine ⟨V, isOpen_ne.preimage hcont, ?_, fun A hA => matrix_eq_one_of_pow_eq_one hA⟩
  change (∑ i ∈ Finset.range k, (1 : Matrix ι ι ℝ) ^ i).det ≠ 0
  have hsum : (∑ i ∈ Finset.range k, (1 : Matrix ι ι ℝ) ^ i)
      = (k : ℝ) • (1 : Matrix ι ι ℝ) := by
    simp only [one_pow, Finset.sum_const, Finset.card_range]
    exact (Nat.cast_smul_eq_nsmul ℝ k (1 : Matrix ι ι ℝ)).symm
  rw [hsum, Matrix.det_smul, Matrix.det_one, mul_one]
  exact pow_ne_zero _ (Nat.cast_ne_zero.mpr hk.ne')

end Matrix

end DifferentialGeometry.BoundedTorsion
