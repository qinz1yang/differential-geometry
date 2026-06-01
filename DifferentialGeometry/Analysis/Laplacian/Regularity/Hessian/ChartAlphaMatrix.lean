import DifferentialGeometry.Analysis.Laplacian.Regularity.Hessian.ChartInvariance
import DifferentialGeometry.Integral.Connection.ChartBridge.Hessian

/-!
# Unconditional discharge of the chart-α matrix identity and swap auxiliary

This module wraps the chart-α matrix identity `chartAlphaMatrixIdentity` (defined
in `HessianChartInvariance`) and discharges it unconditionally by invoking the
chart-α matrix identity at general chart-α good-set points
(`chartAlphaMatrixIdentity_holds`) from `Integral/Connection/ChartBridge/Hessian.lean`.

It also discharges the symmetry-swap auxiliary used in the polarization identity
for the chart-α Frobenius pairing.

## Main results

* `chartAlphaMatrixIdentity_holds_chartSource` — the chart-α matrix identity
  in the `chartAlphaMatrixIdentity` Prop form, unconditional on the chart-α
  source.

* `chartAlpha_swap_aux_holds` — the unconditional symmetry-swap identity for
  smooth `f, f'` at a chart-α source point.
-/

noncomputable section

open Bundle Manifold Set MeasureTheory Filter Topology Function FiberBundle
open scoped Manifold Topology ContDiff Matrix InnerProductSpace BigOperators
  RealInnerProductSpace ENNReal NNReal

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace HessianChartAlphaMatrix

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Analysis.Laplacian.HessianChartInvariance

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

variable [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- **Discharge of `chartAlphaMatrixIdentity` on the chart-α source.** For a
smooth scalar `f : M → ℝ`, a chart base point `α : M`, and a manifold point
`x ∈ (chartAt H α).source`, the chart-α matrix identity Prop holds.

This packages `chartAlphaMatrixIdentity_holds` (from
`Integral.Connection.ChartBridge.Hessian`) into the `chartAlphaMatrixIdentity`
Prop form expected by the chart-invariance bridge. -/
theorem chartAlphaMatrixIdentity_holds_chartSource
    (g : SmoothRiemannianMetric I M) (α : M)
    {f : M → ℝ} (hf : ContMDiff I 𝓘(ℝ) ∞ f) {x : M}
    (hx : x ∈ (chartAt H α).source) :
    chartAlphaMatrixIdentity (I := I) (M := M) g α f x := by
  classical
  intro i j
  exact chartAlphaMatrixIdentity_holds (I := I) g α hf hx i j

/-- **The chart-α symmetry-swap auxiliary, unconditional.** For smooth `f, f'`
and `x ∈ (chartAt H α).source`, the swap identity holds. -/
theorem chartAlpha_swap_aux_holds
    (g : SmoothRiemannianMetric I M) (α : M)
    (f f' : M → ℝ) (x : M) :
    ∑ i : Fin (Module.finrank ℝ E), ∑ j, ∑ k, ∑ l,
      2 * (chartInvGramMatrix (I := I) g α x i k *
        chartInvGramMatrix (I := I) g α x j l *
        chartHessianTensor (I := I) g α f' i j x *
        chartHessianTensor (I := I) g α f k l x) =
    ∑ i : Fin (Module.finrank ℝ E), ∑ j, ∑ k, ∑ l,
      2 * (chartInvGramMatrix (I := I) g α x i k *
        chartInvGramMatrix (I := I) g α x j l *
        chartHessianTensor (I := I) g α f i j x *
        chartHessianTensor (I := I) g α f' k l x) := by
  classical
  set n := Module.finrank ℝ E
  set G : Fin n → Fin n → ℝ :=
    fun i k => chartInvGramMatrix (I := I) g α x i k with hG_def
  set Hf : Fin n → Fin n → ℝ :=
    fun i j => chartHessianTensor (I := I) g α f i j x with hHf_def
  set Hf' : Fin n → Fin n → ℝ :=
    fun i j => chartHessianTensor (I := I) g α f' i j x with hHf'_def
  have h_Gsymm : ∀ i k : Fin n, G i k = G k i := by
    intro i k
    change chartInvGramMatrix (I := I) g α x i k = chartInvGramMatrix (I := I) g α x k i
    have hHerm : (chartGramMatrix (I := I) g α x).IsHermitian :=
      chartGramMatrix_isHermitian (I := I) g α x
    have hHermInv : (chartInvGramMatrix (I := I) g α x).IsHermitian := by
      unfold chartInvGramMatrix
      exact hHerm.inv
    have h_apply := hHermInv.apply i k
    rw [star_trivial] at h_apply
    exact h_apply.symm
  have h_LHS_abbr :
      (∑ i : Fin n, ∑ j, ∑ k, ∑ l,
        2 * (chartInvGramMatrix (I := I) g α x i k *
          chartInvGramMatrix (I := I) g α x j l *
          chartHessianTensor (I := I) g α f' i j x *
          chartHessianTensor (I := I) g α f k l x)) =
      ∑ i : Fin n, ∑ j, ∑ k, ∑ l,
        2 * (G i k * G j l * Hf' i j * Hf k l) := rfl
  have h_RHS_abbr :
      (∑ i : Fin n, ∑ j, ∑ k, ∑ l,
        2 * (chartInvGramMatrix (I := I) g α x i k *
          chartInvGramMatrix (I := I) g α x j l *
          chartHessianTensor (I := I) g α f i j x *
          chartHessianTensor (I := I) g α f' k l x)) =
      ∑ i : Fin n, ∑ j, ∑ k, ∑ l,
        2 * (G i k * G j l * Hf i j * Hf' k l) := rfl
  rw [h_LHS_abbr, h_RHS_abbr]
  have h_LHS_reorder1 :
      (∑ i : Fin n, ∑ j, ∑ k, ∑ l,
        2 * (G i k * G j l * Hf' i j * Hf k l)) =
      (∑ i : Fin n, ∑ j, ∑ l, ∑ k,
        2 * (G i k * G j l * Hf' i j * Hf k l)) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [Finset.sum_comm]
  have h_LHS_reorder2 :
      (∑ i : Fin n, ∑ j, ∑ l, ∑ k,
        2 * (G i k * G j l * Hf' i j * Hf k l)) =
      (∑ i : Fin n, ∑ l, ∑ j, ∑ k,
        2 * (G i k * G j l * Hf' i j * Hf k l)) := by
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.sum_comm]
  have h_LHS_reorder3 :
      (∑ i : Fin n, ∑ l, ∑ j, ∑ k,
        2 * (G i k * G j l * Hf' i j * Hf k l)) =
      (∑ l : Fin n, ∑ i, ∑ j, ∑ k,
        2 * (G i k * G j l * Hf' i j * Hf k l)) := by
    rw [Finset.sum_comm]
  have h_LHS_reorder4 :
      (∑ l : Fin n, ∑ i, ∑ j, ∑ k,
        2 * (G i k * G j l * Hf' i j * Hf k l)) =
      (∑ l : Fin n, ∑ i, ∑ k, ∑ j,
        2 * (G i k * G j l * Hf' i j * Hf k l)) := by
    refine Finset.sum_congr rfl ?_
    intro l _
    refine Finset.sum_congr rfl ?_
    intro i _
    rw [Finset.sum_comm]
  have h_LHS_reorder5 :
      (∑ l : Fin n, ∑ i, ∑ k, ∑ j,
        2 * (G i k * G j l * Hf' i j * Hf k l)) =
      (∑ l : Fin n, ∑ k, ∑ i, ∑ j,
        2 * (G i k * G j l * Hf' i j * Hf k l)) := by
    refine Finset.sum_congr rfl ?_
    intro l _
    rw [Finset.sum_comm]
  have h_LHS_reorder6 :
      (∑ l : Fin n, ∑ k, ∑ i, ∑ j,
        2 * (G i k * G j l * Hf' i j * Hf k l)) =
      (∑ k : Fin n, ∑ l, ∑ i, ∑ j,
        2 * (G i k * G j l * Hf' i j * Hf k l)) := by
    rw [Finset.sum_comm]
  rw [h_LHS_reorder1, h_LHS_reorder2, h_LHS_reorder3, h_LHS_reorder4, h_LHS_reorder5, h_LHS_reorder6]
  refine Finset.sum_congr rfl ?_
  intro i _
  refine Finset.sum_congr rfl ?_
  intro j _
  refine Finset.sum_congr rfl ?_
  intro k _
  refine Finset.sum_congr rfl ?_
  intro l _
  rw [h_Gsymm k i, h_Gsymm l j]
  ring

end HessianChartAlphaMatrix
end Laplacian
end Analysis
end DifferentialGeometry

end
