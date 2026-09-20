import Mathlib.LinearAlgebra.Basis.Bilinear
import Mathlib.Algebra.Module.BigOperators

open scoped BigOperators

namespace LinearMap

theorem sum_smul_apply_eq_sum_coordinates
    {R M N P ι ι' κ : Type*} [CommSemiring R]
    [AddCommMonoid M] [AddCommMonoid N] [AddCommMonoid P]
    [Module R M] [Module R N] [Module R P] [Fintype ι] [Fintype ι']
    (H : M →ₗ[R] N →ₗ[R] P) (e : Module.Basis ι R M) (f : Module.Basis ι' R N)
    (s : Finset κ) (a : κ → R) (v : κ → M) (w : κ → N) (C : ι → ι' → R)
    (hC : ∀ i j, C i j = ∑ k ∈ s, a k * e.repr (v k) i * f.repr (w k) j) :
    (∑ k ∈ s, a k • H (v k) (w k)) = ∑ i, ∑ j, C i j • H (e i) (f j) := by
  have hexpand (x : M) (y : N) :
      H x y = ∑ i, ∑ j, e.repr x i • f.repr y j • H (e i) (f j) := by
    rw [← sum_repr_mul_repr_mul e f (B := H) x y]
    rw [Finsupp.sum_fintype _ _ (fun _ => by simp)]
    apply Finset.sum_congr rfl
    intro i hi
    exact Finsupp.sum_fintype _ _ (fun _ => by simp)
  calc
    (∑ k ∈ s, a k • H (v k) (w k)) =
        ∑ k ∈ s, ∑ i, ∑ j,
          (a k * e.repr (v k) i * f.repr (w k) j) • H (e i) (f j) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [hexpand (v k) (w k)]
      simp only [Finset.smul_sum, smul_smul, mul_assoc]
    _ = ∑ i, ∑ j,
        (∑ k ∈ s, a k * e.repr (v k) i * f.repr (w k) j) • H (e i) (f j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j hj
      rw [Finset.sum_smul]
    _ = ∑ i, ∑ j, C i j • H (e i) (f j) := by
      simp_rw [← hC]

end LinearMap
