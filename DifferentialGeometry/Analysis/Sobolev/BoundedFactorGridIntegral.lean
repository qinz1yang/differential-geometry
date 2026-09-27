import DifferentialGeometry.Analysis.Sobolev.BoundedFactorProductGrid
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace DifferentialGeometry
namespace Combinatorics

variable {X : Type*} [TopologicalSpace X] [MeasurableSpace X] [OpensMeasurableSpace X]
  [CompactSpace X] {μ : Measure X} [IsFiniteMeasure μ]

omit [OpensMeasurableSpace X] [CompactSpace X] in
private theorem finOnCpt (μ : Measure X) [IsFiniteMeasure μ] :
    IsFiniteMeasureOnCompacts μ :=
  ⟨fun K _ => MeasureTheory.measure_lt_top μ K⟩

theorem boundedFactorCell_integrable (b : X → ℕ → ℝ) (hcont : ∀ l : ℕ, Continuous fun x => b x l)
    (n : ℕ) (e : Fin n → ℕ) :
    Integrable (fun x => ∏ m : Fin n, b x (e m)) μ := by
  have := finOnCpt (X := X) μ
  exact (continuous_finsetProd _ (fun m _ => hcont (e m))).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

omit [MeasurableSpace X] [OpensMeasurableSpace X] [CompactSpace X] in
theorem boundedFactorGrid_continuous (b : X → ℕ → ℝ) (hcont : ∀ l : ℕ, Continuous fun x => b x l)
    (K k : ℕ) :
    Continuous fun x => boundedFactorGrid (b x) K k := by
  simp only [boundedFactorGrid]
  refine continuous_finsetSum _ (fun n _ => ?_)
  refine continuous_finsetSum _ (fun e _ => ?_)
  exact continuous_finsetProd _ (fun m _ => hcont (e m))

theorem boundedFactorGrid_integrable (b : X → ℕ → ℝ) (hcont : ∀ l : ℕ, Continuous fun x => b x l)
    (K k : ℕ) :
    Integrable (fun x => boundedFactorGrid (b x) K k) μ := by
  have := finOnCpt (X := X) μ
  exact (boundedFactorGrid_continuous b hcont K k).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem integral_boundedFactorGrid (b : X → ℕ → ℝ) (hcont : ∀ l : ℕ, Continuous fun x => b x l)
    (K k : ℕ) :
    (∫ x, boundedFactorGrid (b x) K k ∂μ) =
      ∑ n ∈ Finset.range (k + 1),
        ∑ e ∈ (Finset.Nat.antidiagonalTuple n k).filter (fun e => ∀ m, e m ≤ K),
          ∫ x, ∏ m : Fin n, b x (e m) ∂μ := by
  have h1 : (fun x => boundedFactorGrid (b x) K k) =
      (fun x => ∑ n ∈ Finset.range (k + 1),
        ∑ e ∈ (Finset.Nat.antidiagonalTuple n k).filter (fun e => ∀ m, e m ≤ K),
          ∏ m : Fin n, b x (e m)) := rfl
  rw [h1, MeasureTheory.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n _
    rw [MeasureTheory.integral_finsetSum]
    intro e _; exact boundedFactorCell_integrable b hcont n e
  · intro n _
    apply MeasureTheory.integrable_finsetSum
    intro e _; exact boundedFactorCell_integrable b hcont n e

end Combinatorics
end DifferentialGeometry

end
