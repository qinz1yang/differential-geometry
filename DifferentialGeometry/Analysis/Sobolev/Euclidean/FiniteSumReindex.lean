import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section

open Filter MeasureTheory
open scoped BigOperators

namespace DifferentialGeometry.Analysis.Sobolev.Euclidean

theorem ae_eq_finite_sum_mul_reindex
    {P R ι κ : Type*} [MeasurableSpace P] [Fintype ι] [Fintype κ]
    [AddCommMonoid R] [Mul R] {μ : Measure P} {f : P → R}
    {A : ι → P → R} {Y : ι → P → R} (e : ι ≃ κ)
    (h : f =ᵐ[μ] fun p => ∑ i, A i p * Y i p) :
    f =ᵐ[μ] fun p => ∑ j, A (e.symm j) p * Y (e.symm j) p := by
  filter_upwards [h] with p hp
  rw [hp]
  apply Fintype.sum_equiv e
  intro i
  simp

end DifferentialGeometry.Analysis.Sobolev.Euclidean
