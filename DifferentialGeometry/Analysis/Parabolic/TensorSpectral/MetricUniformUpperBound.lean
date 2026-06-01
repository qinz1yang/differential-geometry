import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.InnerBridge
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.LowerAllUpperIndices
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.JinvContinuity
import DifferentialGeometry.Analysis.Laplacian.MetricBounds
import DifferentialGeometry.Integral.Measure.ChartDensity
import DifferentialGeometry.Integral.Measure.Invariance
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian
import Mathlib.Analysis.SpecialFunctions.Pow.NNReal
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Separation.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-!
# Uniform upper bound on the chart-Gram quadratic form over a compact base set

For a smooth manifold `M` modelled on `(E, H)` carrying a smooth Riemannian
metric `g : SmoothRiemannianMetric I M`, this file proves a uniform
pointwise upper bound on the chart-Gram quadratic form
`chartGramBilin g α b v v` for `b` ranging over a compact subset of one chart
source and `v` ranging over the model fibre `E`. Through the always-true bridge
identity `chartGramBilin_eq_innerJinv`, this equivalently bounds the
`chartJinv α b`-pullback `g.inner b (chartJinv α b v) (chartJinv α b v)` of the
bundle metric.

## Strategy

The bundle metric `g.inner b v v` (for `v : E ≡ TangentSpace I b`) is, by
itself, not jointly continuous in `(b, v)` because the chart trivialisation
of the tangent bundle jumps between chart sources. We therefore work with the
chart-Gram form centred at a single chart base point `α`. The function
`b ↦ chartGramBilin g α b` is continuous on the chart source `(chartAt H α).source`
(a finite sum of `(b ↦ chartGramMatrix g α b j k)` times constant CLMs, each
entry being smooth on the chart base set by `chartGramMatrix_entry_contMDiffOn`).
Consequently `b ↦ ‖chartGramBilin g α b‖` is continuous on the chart source
and, on any compact subset of it, bounded above by the extreme-value theorem.

On a compact `K_base ⊆ (chartAt H α).source` the operator-norm bound gives
`chartGramBilin g α b v v ≤ C · ‖v‖²`, and taking `K := √C + 1` (strictly
positive) yields the bound `√(chartGramBilin g α b v v) ≤ K · ‖v‖`.

## Main results

* `g_inner_sqrt_uniform_upper_bound_on_compact` — for any chart
  base point `α` and any compact `K_base ⊆ (chartAt H α).source`, there is
  `K > 0` with `√(chartGramBilin g α b v v) ≤ K · ‖v‖` for all `b ∈ K_base`
  and all `v : E`.
* `g_inner_chartJinv_sqrt_uniform_upper_bound_on_compact_unconditional` — the
  same bound transported through `chartGramBilin_eq_innerJinv` onto the
  `chartJinv α b`-pullback of the bundle metric.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap Filter
open scoped Manifold Topology Bundle ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Tensor
open DifferentialGeometry.Tensor.Tensor0SRiemannian
open DifferentialGeometry.Analysis.Laplacian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E] [InnerProductSpace ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M]

private lemma achart_eq_of_chartAt_eq {b b₀ : M}
    (h_chart : chartAt H b = chartAt H b₀) :
    achart H b = achart H b₀ := by
  apply Subtype.ext
  exact h_chart

/-- When the chart at `b` agrees with the chart at `b₀`, the inverse
chart-Jacobian `chartJinv b₀ b : E →L[ℝ] E` is the identity (the core
coordinate change with equal endpoints is the identity). -/
private lemma chartJinv_eq_id_of_chartAt_eq
    {b b₀ : M} (h_chart : chartAt H b = chartAt H b₀)
    (hb : b ∈ (chartAt H b₀).source) :
    chartJinv (I := I) (M := M) b₀ b = (1 : E →L[ℝ] E) := by
  unfold chartJinv
  rw [TangentBundle.symmL_trivializationAt_eq_core (𝕜 := ℝ) (I := I)
    (b₀ := b₀) (b := b) hb]
  rw [achart_eq_of_chartAt_eq (H := H) (M := M) h_chart]
  ext v
  apply (tangentBundleCore I M).coordChange_self (achart H b₀) b
  rw [tangentBundleCore_baseSet, coe_achart]
  exact hb

/-- On the locality neighbourhood, the bundle metric quadratic form coincides
with the chart-Gram bilinear quadratic form centred at `b₀`. -/
private lemma g_inner_eq_chartGramBilin_of_chartAt_eq
    (g : SmoothRiemannianMetric I M) {b b₀ : M}
    (h_chart : chartAt H b = chartAt H b₀)
    (hb : b ∈ (chartAt H b₀).source) (v : E) :
    g.inner b v v =
      chartGramBilin (I := I) (M := M) g b₀ b v v := by
  rw [chartGramBilin_eq_innerJinv (I := I) (M := M) g b₀ b v v]
  rw [chartJinv_eq_id_of_chartAt_eq (I := I) (M := M) h_chart hb]
  rfl

private lemma chartGramBilin_continuousOn_chartSource
    (g : SmoothRiemannianMetric I M) (b₀ : M) :
    ContinuousOn (fun b : M => chartGramBilin (I := I) (M := M) g b₀ b)
      (chartAt H b₀).source := by
  classical
  have h_eq : ∀ b : M,
      chartGramBilin (I := I) (M := M) g b₀ b =
        ∑ j : Fin (Module.finrank ℝ E),
          ∑ k : Fin (Module.finrank ℝ E),
            chartGramMatrix g b₀ b j k •
              (chartCoordCLM E j).smulRight (chartCoordCLM E k) := by
    intro b; rfl
  refine ContinuousOn.congr ?_ (fun b _ => (h_eq b).symm)
  refine continuousOn_finset_sum _ (fun j _ => ?_)
  refine continuousOn_finset_sum _ (fun k _ => ?_)
  have h_entry : ContinuousOn (fun b : M => chartGramMatrix g b₀ b j k)
      (chartAt H b₀).source := by
    have hsmooth := chartGramMatrix_entry_contMDiffOn (I := I) g b₀ j k
    have h_set_eq : ((trivializationAt E (TangentSpace I) b₀).baseSet
        : Set M) = (chartAt H b₀).source :=
      trivializationAt_baseSet_eq_chartAt_source (I := I) (M := M) b₀
    rw [h_set_eq] at hsmooth
    exact hsmooth.continuousOn
  exact h_entry.smul continuousOn_const

private lemma chartGramBilin_norm_continuousOn
    (g : SmoothRiemannianMetric I M) (b₀ : M) :
    ContinuousOn (fun b : M => ‖chartGramBilin (I := I) (M := M) g b₀ b‖)
      (chartAt H b₀).source :=
  continuous_norm.comp_continuousOn
    (chartGramBilin_continuousOn_chartSource (I := I) (M := M) g b₀)

private lemma g_inner_le_chartGramBilin_norm_sq
    (g : SmoothRiemannianMetric I M) {b b₀ : M}
    (h_chart : chartAt H b = chartAt H b₀)
    (hb : b ∈ (chartAt H b₀).source) (v : E) :
    g.inner b v v ≤ ‖chartGramBilin (I := I) (M := M) g b₀ b‖ * ‖v‖ ^ 2 := by
  have h_eq : g.inner b v v =
      chartGramBilin (I := I) (M := M) g b₀ b v v :=
    g_inner_eq_chartGramBilin_of_chartAt_eq (I := I) (M := M) g h_chart hb v
  rw [h_eq]
  have h_abs_le :
      |chartGramBilin (I := I) (M := M) g b₀ b v v| ≤
        ‖chartGramBilin (I := I) (M := M) g b₀ b‖ * ‖v‖ * ‖v‖ := by
    have h := (chartGramBilin (I := I) (M := M) g b₀ b).le_opNorm₂ v v
    simpa [Real.norm_eq_abs] using h
  calc chartGramBilin (I := I) (M := M) g b₀ b v v
      ≤ |chartGramBilin (I := I) (M := M) g b₀ b v v| := le_abs_self _
    _ ≤ ‖chartGramBilin (I := I) (M := M) g b₀ b‖ * ‖v‖ * ‖v‖ := h_abs_le
    _ = ‖chartGramBilin (I := I) (M := M) g b₀ b‖ * ‖v‖ ^ 2 := by ring

private lemma exists_norm_bound_on_compact_subset_of_chartSource
    (g : SmoothRiemannianMetric I M) (b₀ : M)
    {K : Set M} (hK : IsCompact K) (hKsub : K ⊆ (chartAt H b₀).source) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b ∈ K,
      ‖chartGramBilin (I := I) (M := M) g b₀ b‖ ≤ C := by
  by_cases h_empty : K = ∅
  · refine ⟨0, le_refl 0, ?_⟩
    intro b hb
    rw [h_empty] at hb
    exact absurd hb (Set.notMem_empty _)
  have h_cont : ContinuousOn
      (fun b : M => ‖chartGramBilin (I := I) (M := M) g b₀ b‖) K :=
    (chartGramBilin_norm_continuousOn (I := I) (M := M) g b₀).mono hKsub
  have h_bdd : BddAbove
      ((fun b : M => ‖chartGramBilin (I := I) (M := M) g b₀ b‖) '' K) :=
    hK.bddAbove_image h_cont
  rcases h_bdd with ⟨C, hC⟩
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro b hb
  have h1 : ‖chartGramBilin (I := I) (M := M) g b₀ b‖ ≤ C :=
    hC ⟨b, hb, rfl⟩
  exact h1.trans (le_max_left _ _)

/-- The chart-Gram quadratic form is non-negative: it is the
`chartJinv α b`-pullback of the bundle metric, which is non-negative by
positive semi-definiteness of the Riemannian metric. -/
private lemma chartGramBilin_self_nonneg
    (g : SmoothRiemannianMetric I M) (α b : M) (v : E) :
    0 ≤ chartGramBilin (I := I) (M := M) g α b v v := by
  rw [chartGramBilin_eq_innerJinv (I := I) (M := M) g α b v v]
  exact metric_inner_self_nonneg (I := I) (M := M) g b
    (chartJinv (I := I) (M := M) α b v)

/-- Pointwise upper bound on the chart-Gram quadratic form by the operator
norm of the chart-Gram bilinear form. Holds unconditionally for every `b`
and every `v : E`. -/
private lemma chartGramBilin_self_le_norm_sq
    (g : SmoothRiemannianMetric I M) (α b : M) (v : E) :
    chartGramBilin (I := I) (M := M) g α b v v ≤
      ‖chartGramBilin (I := I) (M := M) g α b‖ * ‖v‖ ^ 2 := by
  have h_abs_le :
      |chartGramBilin (I := I) (M := M) g α b v v| ≤
        ‖chartGramBilin (I := I) (M := M) g α b‖ * ‖v‖ * ‖v‖ := by
    have h := (chartGramBilin (I := I) (M := M) g α b).le_opNorm₂ v v
    simpa [Real.norm_eq_abs] using h
  calc chartGramBilin (I := I) (M := M) g α b v v
      ≤ |chartGramBilin (I := I) (M := M) g α b v v| := le_abs_self _
    _ ≤ ‖chartGramBilin (I := I) (M := M) g α b‖ * ‖v‖ * ‖v‖ := h_abs_le
    _ = ‖chartGramBilin (I := I) (M := M) g α b‖ * ‖v‖ ^ 2 := by ring

/-- **Locality-free uniform upper bound on the chart-Gram quadratic form over a
compact base set.**

For any chart base point `α` and any compact `K_base ⊆ (chartAt H α).source`,
there is `K > 0` with
`√(chartGramBilin g α b v v) ≤ K · ‖v‖` for all `b ∈ K_base` and all `v : E`.

Where `chartJinv α b = id`, the chart-Gram quadratic form coincides with
`g.inner b v v`, so this recovers a bound `√(g.inner b v v) ≤ K · ‖v‖` there.
The chart-Gram form is, by `chartGramBilin_eq_innerJinv`, the
`chartJinv α b`-pullback of the bundle metric `g.inner b`. -/
theorem g_inner_sqrt_uniform_upper_bound_on_compact
    (g : SmoothRiemannianMetric I M) (α : M)
    {K_base : Set M} (hK_base : IsCompact K_base)
    (hK_sub : K_base ⊆ (chartAt H α).source) :
    ∃ K : ℝ, 0 < K ∧ ∀ b ∈ K_base, ∀ v : E,
      Real.sqrt (chartGramBilin (I := I) (M := M) g α b v v) ≤ K * ‖v‖ := by
  classical
  obtain ⟨C, hC_nn, h_norm_bound⟩ :=
    exists_norm_bound_on_compact_subset_of_chartSource
      (I := I) (M := M) g α hK_base hK_sub
  refine ⟨Real.sqrt C + 1, ?_, ?_⟩
  · have h_sqrt_nn : 0 ≤ Real.sqrt C := Real.sqrt_nonneg _
    linarith
  intro b hb v
  have h_norm_le : ‖chartGramBilin (I := I) (M := M) g α b‖ ≤ C :=
    h_norm_bound b hb
  have h_norm_sq_nn : 0 ≤ ‖v‖ ^ 2 := sq_nonneg _
  have h_sq_bound :
      chartGramBilin (I := I) (M := M) g α b v v ≤ C * ‖v‖ ^ 2 := by
    refine (chartGramBilin_self_le_norm_sq (I := I) (M := M) g α b v).trans ?_
    exact mul_le_mul_of_nonneg_right h_norm_le h_norm_sq_nn
  have h_norm_nn : 0 ≤ ‖v‖ := norm_nonneg _
  have h_sqrt_le :
      Real.sqrt (chartGramBilin (I := I) (M := M) g α b v v) ≤
        Real.sqrt (C * ‖v‖ ^ 2) :=
    Real.sqrt_le_sqrt h_sq_bound
  have h_sqrt_prod : Real.sqrt (C * ‖v‖ ^ 2) = Real.sqrt C * ‖v‖ := by
    rw [Real.sqrt_mul hC_nn, Real.sqrt_sq h_norm_nn]
  rw [h_sqrt_prod] at h_sqrt_le
  have h_step : Real.sqrt C * ‖v‖ ≤ (Real.sqrt C + 1) * ‖v‖ := by
    have h_sqrt_nn : 0 ≤ Real.sqrt C := Real.sqrt_nonneg _
    nlinarith [h_norm_nn]
  linarith

/-- **Locality-free uniform upper bound on the bundle metric quadratic form
over a compact base set, in the chart frame.**

Reformulation of `g_inner_sqrt_uniform_upper_bound_on_compact`
through the always-true bridge identity `chartGramBilin_eq_innerJinv`:
for any chart base point `α` and any compact `K_base ⊆ (chartAt H α).source`,
there is `K > 0` with
`√(g.inner b (chartJinv α b v) (chartJinv α b v)) ≤ K · ‖v‖`
for all `b ∈ K_base` and all `v : E`. Where `chartJinv α b = id` this is
exactly the bound `√(g.inner b v v) ≤ K · ‖v‖`. -/
theorem g_inner_chartJinv_sqrt_uniform_upper_bound_on_compact_unconditional
    (g : SmoothRiemannianMetric I M) (α : M)
    {K_base : Set M} (hK_base : IsCompact K_base)
    (hK_sub : K_base ⊆ (chartAt H α).source) :
    ∃ K : ℝ, 0 < K ∧ ∀ b ∈ K_base, ∀ v : E,
      Real.sqrt (g.inner b
          (chartJinv (I := I) (M := M) α b v)
          (chartJinv (I := I) (M := M) α b v)) ≤ K * ‖v‖ := by
  obtain ⟨K, hK_pos, h⟩ :=
    g_inner_sqrt_uniform_upper_bound_on_compact
      (I := I) (M := M) g α hK_base hK_sub
  refine ⟨K, hK_pos, ?_⟩
  intro b hb v
  rw [← chartGramBilin_eq_innerJinv (I := I) (M := M) g α b v v]
  exact h b hb v

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
