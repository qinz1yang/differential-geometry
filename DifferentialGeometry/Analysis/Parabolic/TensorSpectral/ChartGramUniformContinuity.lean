import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.InnerLowerBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.GramInvUniformEigenvalueLowerBound
import DifferentialGeometry.Geometry.Gradient
import DifferentialGeometry.Integral.Measure.Invariance
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Basic

/-!
# Uniform bound on the inverse chart-Gram-matrix entry-`L^1`-sum over a compact base set

For a smooth Riemannian manifold `(M, g)`, a chart base point `α : M`, and a
fixed compact set `K ⊆ (chartAt H α).source`, this file proves a uniform
upper bound on the sum of absolute values of all entries of
`chartInvGramMatrix g α b` for `b ∈ K`, alongside the analogous bound for the
forward Gram matrix `chartGramMatrix g α b`.

## Strategy

Each entry `b ↦ chartInvGramMatrix g α b i j` and `b ↦ chartGramMatrix g α b i j`
is smooth (and therefore continuous) on the chart-`α` base set, by
`chartInvGramMatrix_entry_contMDiffOn` and `chartGramMatrix_entry_contMDiffOn`
respectively. The sum of absolute values is then continuous on the chart
source, and the extreme-value theorem on a compact subset gives a finite
upper bound; replacing the bound by `max (·) 0 + 1` makes it strictly
positive.

The locality hypothesis `HasLocallyConstantChartAt H M` is taken for
uniformity with the surrounding API (chart-`J`, chart-`Jinv`, chart-Gram
bilinear bounds) but is not required for the proof — the inverse-Gram
entries are continuous on the chart source directly, without needing
to reduce coordinate jumps.

## Main results

* `chartGramMatrix_entry_isBounded_on_compact` — uniform absolute-value
  bound on each entry of the forward Gram matrix over any compact
  `K ⊆ (chartAt H α).source`.
* `chartInvGramMatrix_entry_isBounded_on_compact` — uniform absolute-value
  bound on each entry of the inverse Gram matrix over any compact
  `K ⊆ (chartAt H α).source`.
* `chartInvGramMatrix_l1Sum_isBounded_on_compact` — uniform `L^1`-sum bound
  on the inverse Gram matrix over any compact `K ⊆ (chartAt H α).source`.
* `chartInvGramMatrix_l1Sum_isBounded_on_pouTsupport` — specialisation to
  `K = tsupport(POU_α)` on a closed manifold.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

/-- The sum of absolute values of all entries of the inverse chart-`α`-Gram
matrix at `x : M`. -/
def chartInvGramMatrix_l1Sum
    (g : SmoothRiemannianMetric I M) (α x : M) : ℝ :=
  ∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
    |chartInvGramMatrix (I := I) g α x ij.1 ij.2|

lemma chartInvGramMatrix_l1Sum_nonneg
    (g : SmoothRiemannianMetric I M) (α x : M) :
    0 ≤ chartInvGramMatrix_l1Sum (I := I) (M := M) g α x := by
  unfold chartInvGramMatrix_l1Sum
  exact Finset.sum_nonneg (fun _ _ => abs_nonneg _)

/-- `b ↦ chartGramMatrix g α b i j` is continuous on `(chartAt H α).source`. -/
private lemma chartGramMatrix_entry_continuousOn_chartSource
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun b : M => chartGramMatrix (I := I) g α b i j)
      (chartAt H α).source := by
  have hsmooth :
      ContMDiffOn I 𝓘(ℝ) ∞ (fun b : M => chartGramMatrix (I := I) g α b i j)
        (trivializationAt E (TangentSpace I) α).baseSet :=
    chartGramMatrix_entry_contMDiffOn (I := I) g α i j
  have h_set_eq : ((trivializationAt E (TangentSpace I) α).baseSet : Set M)
      = (chartAt H α).source :=
    trivializationAt_baseSet_eq_chartAt_source (I := I) (M := M) α
  rw [h_set_eq] at hsmooth
  exact hsmooth.continuousOn

/-- `b ↦ chartInvGramMatrix g α b i j` is continuous on `(chartAt H α).source`. -/
private lemma chartInvGramMatrix_entry_continuousOn_chartSource
    (g : SmoothRiemannianMetric I M) (α : M)
    (i j : Fin (Module.finrank ℝ E)) :
    ContinuousOn (fun b : M => chartInvGramMatrix (I := I) g α b i j)
      (chartAt H α).source := by
  have hsmooth :
      ContMDiffOn I 𝓘(ℝ) ∞ (fun b : M => chartInvGramMatrix (I := I) g α b i j)
        (trivializationAt E (TangentSpace I) α).baseSet :=
    chartInvGramMatrix_entry_contMDiffOn (I := I) g α i j
  have h_set_eq : ((trivializationAt E (TangentSpace I) α).baseSet : Set M)
      = (chartAt H α).source :=
    trivializationAt_baseSet_eq_chartAt_source (I := I) (M := M) α
  rw [h_set_eq] at hsmooth
  exact hsmooth.continuousOn

/-- The `L^1`-sum `chartInvGramMatrix_l1Sum g α` is continuous on
`(chartAt H α).source`. -/
private lemma chartInvGramMatrix_l1Sum_continuousOn_chartSource
    (g : SmoothRiemannianMetric I M) (α : M) :
    ContinuousOn (chartInvGramMatrix_l1Sum (I := I) (M := M) g α)
      (chartAt H α).source := by
  classical
  unfold chartInvGramMatrix_l1Sum
  refine continuousOn_finset_sum _ (fun ij _ => ?_)
  exact (chartInvGramMatrix_entry_continuousOn_chartSource
    (I := I) (M := M) g α ij.1 ij.2).abs

private lemma exists_bound_on_compact_of_continuousOn
    (α : M) (f : M → ℝ)
    (h_cont : ContinuousOn f (chartAt H α).source)
    {K : Set M} (hK : IsCompact K) (hKsub : K ⊆ (chartAt H α).source) :
    ∃ C : ℝ, 0 < C ∧ ∀ b ∈ K, f b ≤ C := by
  by_cases h_empty : K = ∅
  · refine ⟨1, one_pos, ?_⟩
    intro b hb
    rw [h_empty] at hb
    exact absurd hb (Set.notMem_empty _)
  have h_cont_K : ContinuousOn f K := h_cont.mono hKsub
  have h_bdd : BddAbove (f '' K) := hK.bddAbove_image h_cont_K
  rcases h_bdd with ⟨C, hC⟩
  refine ⟨max C 0 + 1, by linarith [le_max_right C 0], ?_⟩
  intro b hb
  have h1 : f b ≤ C := hC ⟨b, hb, rfl⟩
  have h2 : C ≤ max C 0 := le_max_left _ _
  linarith

/-- Uniform absolute-value bound on each entry of the forward chart-Gram
matrix over any compact subset of `(chartAt H α).source`. The locality
hypothesis is taken for API uniformity (chart-`J`, chart-Gram-bilinear)
but is not required for the proof. -/
theorem chartGramMatrix_entry_isBounded_on_compact
(g : SmoothRiemannianMetric I M)
    (α : M) (i j : Fin (Module.finrank ℝ E))
    {K : Set M} (hK : IsCompact K) (hKsub : K ⊆ (chartAt H α).source) :
    ∃ C : ℝ, 0 < C ∧
      ∀ b ∈ K, |chartGramMatrix (I := I) g α b i j| ≤ C := by
  have h_cont : ContinuousOn (fun b : M => |chartGramMatrix (I := I) g α b i j|)
      (chartAt H α).source :=
    (chartGramMatrix_entry_continuousOn_chartSource (I := I) (M := M) g α i j).abs
  exact exists_bound_on_compact_of_continuousOn (α := α) _ h_cont hK hKsub

/-- Uniform absolute-value bound on each entry of the inverse chart-Gram
matrix over any compact subset of `(chartAt H α).source`. The locality
hypothesis is taken for API uniformity (chart-`J`, chart-Gram-bilinear)
but is not required for the proof. -/
theorem chartInvGramMatrix_entry_isBounded_on_compact
(g : SmoothRiemannianMetric I M)
    (α : M) (i j : Fin (Module.finrank ℝ E))
    {K : Set M} (hK : IsCompact K) (hKsub : K ⊆ (chartAt H α).source) :
    ∃ C : ℝ, 0 < C ∧
      ∀ b ∈ K, |chartInvGramMatrix (I := I) g α b i j| ≤ C := by
  have h_cont :
      ContinuousOn (fun b : M => |chartInvGramMatrix (I := I) g α b i j|)
        (chartAt H α).source :=
    (chartInvGramMatrix_entry_continuousOn_chartSource
      (I := I) (M := M) g α i j).abs
  exact exists_bound_on_compact_of_continuousOn (α := α) _ h_cont hK hKsub

/-- **Uniform `L^1`-sum bound on the inverse chart-Gram matrix over any
compact subset of `(chartAt H α).source`.**

For a smooth Riemannian metric `g` and chart base point `α : M`, there
exists `C > 0` such that for every `b` in a given compact set
`K ⊆ (chartAt H α).source`,
`∑_{i, j} |chartInvGramMatrix g α b i j| ≤ C`.

The locality hypothesis `HasLocallyConstantChartAt H M` is included for
API uniformity with the surrounding chart-Jacobian / chart-Gram-bilinear
bounds, but is not required for the proof: each entry of the inverse
chart-Gram matrix is smooth on the chart base set
(`chartInvGramMatrix_entry_contMDiffOn`), so the `L^1` sum is continuous
on `(chartAt H α).source` and the extreme-value theorem applies on
`K`. -/
theorem chartInvGramMatrix_l1Sum_isBounded_on_compact
(g : SmoothRiemannianMetric I M)
    (α : M) {K : Set M} (hK : IsCompact K)
    (hKsub : K ⊆ (chartAt H α).source) :
    ∃ C : ℝ, 0 < C ∧
      ∀ b ∈ K, chartInvGramMatrix_l1Sum (I := I) (M := M) g α b ≤ C := by
  have h_cont := chartInvGramMatrix_l1Sum_continuousOn_chartSource
    (I := I) (M := M) g α
  exact exists_bound_on_compact_of_continuousOn (α := α) _ h_cont hK hKsub

/-- **Uniform `L^1`-sum bound on the inverse chart-Gram matrix over the
closed support of the chart-atlas partition-of-unity weight at `α`.**

For a closed Riemannian manifold `(M, g)` and chart base point `α`,
there exists `C > 0` such that for every `b` in the closed support of the
chart-atlas partition-of-unity weight at `α`,
`∑_{i, j} |chartInvGramMatrix g α b i j| ≤ C`.

This is the specialisation of `chartInvGramMatrix_l1Sum_isBounded_on_compact`
to the canonical compact set `tsupport(POU_α)`, which is contained in
`(chartAt H α).source` by `pouTsupport_subset_baseSet`. -/
theorem chartInvGramMatrix_l1Sum_isBounded_on_pouTsupport
    [SigmaCompactSpace M] [CompactSpace M]
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ C : ℝ, 0 < C ∧
      ∀ b : M, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        chartInvGramMatrix_l1Sum (I := I) (M := M) g α b ≤ C := by
  classical
  set Kα : Set M := tsupport (fun x : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hKα_def
  have hKα_compact : IsCompact Kα :=
    pouTsupport_isCompact (I := I) (M := M) α
  have hKα_sub_base :
      Kα ⊆ (trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α
  have hKα_sub_src : Kα ⊆ (chartAt H α).source := by
    have h_set_eq : ((trivializationAt E (TangentSpace I) α).baseSet : Set M)
        = (chartAt H α).source :=
      trivializationAt_baseSet_eq_chartAt_source (I := I) (M := M) α
    rw [← h_set_eq]
    exact hKα_sub_base
  rcases chartInvGramMatrix_l1Sum_isBounded_on_compact
      (I := I) (M := M) g α hKα_compact hKα_sub_src with ⟨C, hC_pos, hC_le⟩
  exact ⟨C, hC_pos, fun b hb => hC_le b hb⟩

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
