import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.Inner
import DifferentialGeometry.Tensor.RSTensor.Tensor0SRiemannian
import DifferentialGeometry.Integral.L2.PointwiseInner.Defs
import DifferentialGeometry.Integral.L2.PointwiseInner.DualMetric

/-!
# Bridge identity for the chart-frame `(r, s)`-inner product

This file establishes the pointwise algebraic identity that connects the
chart-frame `(r, s)`-inner product (`chartTensorInnerPointwise_rs_model`,
defined in `ChartTensorInner.lean`) with the bundle-fibre `(0, n)`-inner
product (`tensorInnerPointwise_0s`, defined on the model fibre in
`PointwiseInner/Defs.lean`), at a fixed base point `b` in the chart base
set.

The bridge proceeds via the existing `(0, s)`-bridge
`tensorInnerPointwise_0s_bridge_identity`. At arity `r + s`, the chart-frame
`(0, n)`-inner product on a pair of `(0, n)`-tensors equals the bundle-fibre
`(0, n)`-inner product of the same tensors after slot-wise composition with
`chartJ α b`. Specialising this identity to the two
`chartLowerAllUpperIndices_model`-lowered tensors yields the bridge for the
`(r, s)`-inner product.

## Main results

* `chartGramBilin_eq_innerJinv` — the chart-Gram bilinear form on `E × E`
  equals the bundle metric pulled back along `chartJinv α b` in both
  arguments.
* `chartGramBilin_chartJ_chartJ` — on the chart base set, the chart-Gram
  bilinear form applied to two `chartJ`-images of vectors recovers the
  bundle metric on the original vectors.
* `chartSeparableFormAt_chartJ_compose` — on the chart base set,
  `chartSeparableFormAt g α b r (chartJ ∘ v_first) =
   (separableFormAt g b r v_first).compContinuousLinearMap chartJinv`.
* `chartTensorInnerPointwise_0s_eq_tensorInnerPointwise_0s_chartJ` —
  reverse direction of `tensorInnerPointwise_0s_bridge_identity`: on the
  chart base set, the chart-frame `(0, n)`-inner product on `A`, `B` equals
  the bundle-fibre `(0, n)`-inner product on `A`, `B` after slot-wise
  composition with `chartJ`.
* `chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise_0s_compChartJ`
  — the main bridge identity in its directly usable form: the chart-frame
  `(r, s)`-inner product equals the bundle-fibre `(0, r + s)`-inner product
  on the chart-frame lowered tensors after slot-wise composition with
  `chartJ`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 800000

open Bundle Set IsManifold ContinuousLinearMap
open scoped Manifold Topology Bundle ContDiff BigOperators Matrix

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Tensor
open Tensor0SBundle
open DifferentialGeometry.Tensor.Tensor0SRiemannian

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The chart-Gram bilinear form is the `chartJinv α b`-pullback of the
bundle metric in both arguments. -/
lemma chartGramBilin_eq_innerJinv
    (g : SmoothRiemannianMetric I M) (α b : M) (u w : E) :
    chartGramBilin (I := I) (M := M) g α b u w =
      g.inner b
        (chartJinv (I := I) (M := M) α b u)
        (chartJinv (I := I) (M := M) α b w) := by
  classical
  rw [chartGramBilin_apply]
  have hrewrite :
      (∑ j : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          chartGramMatrix g α b j k *
            (chartModelBasis E).equivFun u j *
            (chartModelBasis E).equivFun w k)
        = ∑ j : Fin (Module.finrank ℝ E),
            ∑ k : Fin (Module.finrank ℝ E),
              (chartModelBasis E).equivFun u j *
                (chartModelBasis E).equivFun w k *
                g.inner b
                  (chartJinv (I := I) (M := M) α b ((chartModelBasis E) j))
                  (chartJinv (I := I) (M := M) α b ((chartModelBasis E) k)) := by
    refine Finset.sum_congr rfl ?_
    intro j _
    refine Finset.sum_congr rfl ?_
    intro k _
    rw [chartGramMatrix_eq_innerJinv (I := I) (M := M) g α b j k]
    ring
  rw [hrewrite]
  have hcollapse_inner : ∀ j : Fin (Module.finrank ℝ E),
      (∑ k : Fin (Module.finrank ℝ E),
          (chartModelBasis E).equivFun u j *
            (chartModelBasis E).equivFun w k *
            g.inner b
              (chartJinv (I := I) (M := M) α b ((chartModelBasis E) j))
              (chartJinv (I := I) (M := M) α b ((chartModelBasis E) k)))
        = (chartModelBasis E).equivFun u j *
            g.inner b
              (chartJinv (I := I) (M := M) α b ((chartModelBasis E) j))
              (∑ k : Fin (Module.finrank ℝ E),
                (chartModelBasis E).equivFun w k •
                  chartJinv (I := I) (M := M) α b
                    ((chartModelBasis E) k)) := by
    intro j
    have hRHS_unfold :
        ((g.inner b (chartJinv (I := I) (M := M) α b ((chartModelBasis E) j)))
            (∑ k : Fin (Module.finrank ℝ E),
              (chartModelBasis E).equivFun w k •
                chartJinv (I := I) (M := M) α b ((chartModelBasis E) k)))
          = ∑ k : Fin (Module.finrank ℝ E),
              (chartModelBasis E).equivFun w k *
                g.inner b
                  (chartJinv (I := I) (M := M) α b ((chartModelBasis E) j))
                  (chartJinv (I := I) (M := M) α b ((chartModelBasis E) k)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [ContinuousLinearMap.map_smul, smul_eq_mul]
    rw [hRHS_unfold]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro k _
    ring
  rw [show (∑ j : Fin (Module.finrank ℝ E),
        ∑ k : Fin (Module.finrank ℝ E),
          (chartModelBasis E).equivFun u j *
            (chartModelBasis E).equivFun w k *
            g.inner b
              (chartJinv (I := I) (M := M) α b ((chartModelBasis E) j))
              (chartJinv (I := I) (M := M) α b ((chartModelBasis E) k)))
        = ∑ j : Fin (Module.finrank ℝ E),
            (chartModelBasis E).equivFun u j *
              g.inner b
                (chartJinv (I := I) (M := M) α b ((chartModelBasis E) j))
                (∑ k : Fin (Module.finrank ℝ E),
                  (chartModelBasis E).equivFun w k •
                    chartJinv (I := I) (M := M) α b
                      ((chartModelBasis E) k)) from
      Finset.sum_congr rfl (fun j _ => hcollapse_inner j)]
  have hwsum :
      (∑ k : Fin (Module.finrank ℝ E),
          (chartModelBasis E).equivFun w k •
            chartJinv (I := I) (M := M) α b ((chartModelBasis E) k)) =
        chartJinv (I := I) (M := M) α b w := by
    have hsum_eq :
        (∑ k : Fin (Module.finrank ℝ E),
            (chartModelBasis E).equivFun w k •
              chartJinv (I := I) (M := M) α b ((chartModelBasis E) k))
          = chartJinv (I := I) (M := M) α b
              (∑ k : Fin (Module.finrank ℝ E),
                (chartModelBasis E).equivFun w k • (chartModelBasis E) k) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [ContinuousLinearMap.map_smul]
    rw [hsum_eq, (chartModelBasis E).sum_equivFun w]
  rw [hwsum]
  have hcollapse_outer :
      (∑ j : Fin (Module.finrank ℝ E),
          (chartModelBasis E).equivFun u j *
            g.inner b
              (chartJinv (I := I) (M := M) α b ((chartModelBasis E) j))
              (chartJinv (I := I) (M := M) α b w))
        = g.inner b
            (∑ j : Fin (Module.finrank ℝ E),
              (chartModelBasis E).equivFun u j •
                chartJinv (I := I) (M := M) α b ((chartModelBasis E) j))
            (chartJinv (I := I) (M := M) α b w) := by
    rw [map_sum]
    rw [ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl ?_
    intro j _
    rw [ContinuousLinearMap.map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hcollapse_outer]
  have husum :
      (∑ j : Fin (Module.finrank ℝ E),
          (chartModelBasis E).equivFun u j •
            chartJinv (I := I) (M := M) α b ((chartModelBasis E) j))
        = chartJinv (I := I) (M := M) α b u := by
    have hsum_eq :
        (∑ j : Fin (Module.finrank ℝ E),
            (chartModelBasis E).equivFun u j •
              chartJinv (I := I) (M := M) α b ((chartModelBasis E) j))
          = chartJinv (I := I) (M := M) α b
              (∑ j : Fin (Module.finrank ℝ E),
                (chartModelBasis E).equivFun u j • (chartModelBasis E) j) := by
      rw [map_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      rw [ContinuousLinearMap.map_smul]
    rw [hsum_eq, (chartModelBasis E).sum_equivFun u]
  rw [husum]

lemma chartGramBilin_chartJ_chartJ
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet) (u w : E) :
    chartGramBilin (I := I) (M := M) g α b
        (chartJ (I := I) (M := M) α b u)
        (chartJ (I := I) (M := M) α b w) =
      g.inner b u w := by
  rw [chartGramBilin_eq_innerJinv (I := I) (M := M) g α b]
  rw [chartJinv_chartJ_self (I := I) (M := M) α hb u]
  rw [chartJinv_chartJ_self (I := I) (M := M) α hb w]

lemma chartSeparableFormAt_chartJ_compose
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (r : ℕ) (v_first : Fin r → E) :
    chartSeparableFormAt (I := I) (M := M) g α b r
        (fun k : Fin r => chartJ (I := I) (M := M) α b (v_first k))
      = (separableFormAt (I := I) (M := M) g b r v_first).compContinuousLinearMap
          (fun _ : Fin r => chartJinv (I := I) (M := M) α b) := by
  classical
  refine ContinuousMultilinearMap.ext ?_
  intro w
  rw [chartSeparableFormAt_apply]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply, separableFormAt_apply]
  refine Finset.prod_congr rfl ?_
  intro k _
  rw [chartGramBilin_eq_innerJinv (I := I) (M := M) g α b]
  rw [chartJinv_chartJ_self (I := I) (M := M) α hb (v_first k)]

/-- On the chart base set, the chart-frame `(0, s)`-inner product on tensors
`A, B` equals the bundle-fibre `(0, s)`-inner product on the
`chartJ`-pulled-back tensors. -/
theorem chartTensorInnerPointwise_0s_eq_tensorInnerPointwise_0s_chartJ
    (g : SmoothRiemannianMetric I M) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (s : ℕ) (A B : Tensor0SModel s ℝ E) :
    chartTensorInnerPointwise_0s (I := I) (M := M) s g α b A B =
      tensorInnerPointwise_0s (I := I) (M := M) s g b
        (A.compContinuousLinearMap
          (fun _ : Fin s => chartJ (I := I) (M := M) α b))
        (B.compContinuousLinearMap
          (fun _ : Fin s => chartJ (I := I) (M := M) α b)) := by
  classical
  have hbridge :=
    tensorInnerPointwise_0s_bridge_identity (I := I) (M := M) g α s hb
      (A.compContinuousLinearMap
        (fun _ : Fin s => chartJ (I := I) (M := M) α b))
      (B.compContinuousLinearMap
        (fun _ : Fin s => chartJ (I := I) (M := M) α b))
  have hAcompose :
      (A.compContinuousLinearMap
          (fun _ : Fin s => chartJ (I := I) (M := M) α b)).compContinuousLinearMap
        (fun _ : Fin s => chartJinv (I := I) (M := M) α b) = A := by
    refine ContinuousMultilinearMap.ext ?_
    intro m
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext k
    exact chartJ_chartJinv (I := I) (M := M) α hb (m k)
  have hBcompose :
      (B.compContinuousLinearMap
          (fun _ : Fin s => chartJ (I := I) (M := M) α b)).compContinuousLinearMap
        (fun _ : Fin s => chartJinv (I := I) (M := M) α b) = B := by
    refine ContinuousMultilinearMap.ext ?_
    intro m
    rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
      ContinuousMultilinearMap.compContinuousLinearMap_apply]
    congr 1
    funext k
    exact chartJ_chartJinv (I := I) (M := M) α hb (m k)
  rw [hAcompose, hBcompose] at hbridge
  exact hbridge.symm

/-- **Main bridge identity (chart-frame to bundle-fibre, via `(0, n)`-inner
product on `chartJ`-composed lowered tensors)**.

On the chart base set, the chart-frame `(r, s)`-inner product on two model
tensors `T₀, T₁` equals the bundle-fibre `(0, r + s)`-inner product on the
two chart-frame-lowered tensors after slot-wise composition with
`chartJ α b`. -/
theorem chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise_0s_compChartJ
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (T₀ T₁ : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b T₀ T₁ =
      tensorInnerPointwise_0s (I := I) (M := M) (r + s) g b
        ((chartLowerAllUpperIndices_model (I := I) (M := M) r s g α b T₀).compContinuousLinearMap
          (fun _ : Fin (r + s) => chartJ (I := I) (M := M) α b))
        ((chartLowerAllUpperIndices_model (I := I) (M := M) r s g α b T₁).compContinuousLinearMap
          (fun _ : Fin (r + s) => chartJ (I := I) (M := M) α b)) := by
  rw [chartTensorInnerPointwise_rs_model_def]
  exact chartTensorInnerPointwise_0s_eq_tensorInnerPointwise_0s_chartJ
    (I := I) (M := M) g α hb (r + s) _ _

/-- The chart-`(α, b)`-twist of a mixed model tensor: pre-compose the
input on the `r`-block with `chartJinv α b`, and post-compose the output on
the `s`-block with `chartJ α b`. Equivalently, for `α' : Tensor0SModel r ℝ E`,
the value is `(T (α'.compCLM (fun _ => chartJinv α b))).compCLM (fun _ => chartJ α b)`.

For `b` in the chart base set, the twist is invertible and the round-trip
recovers `T` via `chartJ ∘ chartJinv = id`. -/
noncomputable def chartRSTwist
    (α : M) (b : M) (r s : ℕ) (T : TensorRSModel r s ℝ E) :
    TensorRSModel r s ℝ E :=
  (ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ : Fin s => chartJ (I := I) (M := M) α b)).comp <|
    T.comp
      ((ContinuousMultilinearMap.compContinuousLinearMapL
        (fun _ : Fin r => chartJinv (I := I) (M := M) α b)))

@[simp]
lemma chartRSTwist_apply
    (α b : M) (r s : ℕ) (T : TensorRSModel r s ℝ E)
    (α' : Tensor0SModel r ℝ E) :
    chartRSTwist (I := I) (M := M) α b r s T α' =
      (T (α'.compContinuousLinearMap
            (fun _ : Fin r => chartJinv (I := I) (M := M) α b))).compContinuousLinearMap
        (fun _ : Fin s => chartJ (I := I) (M := M) α b) := by
  rfl

/-- The chart-`(α, b)`-twist intertwines the chart-frame lowering map with
the bundle-fibre lowering map: on the chart base set,
`(chartLowerAllUpperIndices_model r s g α b T).compCLM chartJ =
  lowerAllUpperIndices g r s b (chartRSTwist α b r s T)`. -/
lemma chartLowerAllUpperIndices_model_compChartJ
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (T : TensorRSModel r s ℝ E) :
    (chartLowerAllUpperIndices_model (I := I) (M := M) r s g α b T).compContinuousLinearMap
        (fun _ : Fin (r + s) => chartJ (I := I) (M := M) α b)
      = lowerAllUpperIndices (I := I) (M := M) g r s b
          (chartRSTwist (I := I) (M := M) α b r s T) := by
  classical
  refine ContinuousMultilinearMap.ext ?_
  intro v
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply,
    chartLowerAllUpperIndices_model_apply]
  rw [lowerAllUpperIndices_apply]
  rw [chartRSTwist_apply]
  have hsep :
      chartSeparableFormAt (I := I) (M := M) g α b r
          (fun i : Fin r => chartJ (I := I) (M := M) α b
            (v (Fin.castAdd s i)))
        = (separableFormAt (I := I) (M := M) g b r
            (fun i : Fin r => v (Fin.castAdd s i))).compContinuousLinearMap
            (fun _ : Fin r => chartJinv (I := I) (M := M) α b) := by
    have := chartSeparableFormAt_chartJ_compose (I := I) (M := M) g α hb r
      (fun i : Fin r => v (Fin.castAdd s i))
    exact this
  rw [hsep]
  rw [ContinuousMultilinearMap.compContinuousLinearMap_apply]

/-- **Bridge identity, `tensorInnerPointwise` form**: on the chart base set,
the chart-frame `(r, s)`-inner product equals the bundle-fibre
`(r, s)`-inner product on the chart-`(α, b)`-twisted tensors. -/
theorem chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) {b : M}
    (hb : b ∈ (trivializationAt E (TangentSpace I) α).baseSet)
    (T₀ T₁ : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b T₀ T₁ =
      tensorInnerPointwise (I := I) (M := M) g r s b
        (chartRSTwist (I := I) (M := M) α b r s T₀)
        (chartRSTwist (I := I) (M := M) α b r s T₁) := by
  rw [chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise_0s_compChartJ
    (I := I) (M := M) g r s α hb T₀ T₁]
  rw [chartLowerAllUpperIndices_model_compChartJ
    (I := I) (M := M) g r s α hb T₀]
  rw [chartLowerAllUpperIndices_model_compChartJ
    (I := I) (M := M) g r s α hb T₁]
  rfl

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
