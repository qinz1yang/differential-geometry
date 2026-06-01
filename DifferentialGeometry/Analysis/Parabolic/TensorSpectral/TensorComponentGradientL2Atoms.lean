import DifferentialGeometry.Analysis.Sobolev.Tensor.ChartComponents
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.GoodSetMeasure
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Estimates.ChristoffelL2BoundFromH1
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Estimates.ComponentL2BoundUniform
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Estimates.CovL2BoundFromH1
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.H1Compl
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.PreHilbert
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SlotChartSourceContMDiff
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.SlotUniformBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.Estimates.ChristoffelBound
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TrivProj.Bridge
import DifferentialGeometry.Integral.Connection.ChartTensorRSCovariantDerivativeAgreement
import DifferentialGeometry.Integral.Connection.SlotCorrectionChartKernel
import DifferentialGeometry.Integral.Connection.TensorRSChartFiberFromModelOpNormUnconditional
import DifferentialGeometry.Integral.Connection.TensorRSChartFiberToModelOpNormUnconditional
import DifferentialGeometry.Integral.Measure.ChartDensity
import Mathlib.MeasureTheory.Integral.IntegrableOn

/-!
# Per-`α` gradient `L²` atom bounds and measurability companions

Consolidated `L²` bounds (and the `AEStronglyMeasurable` companion lemmas)
for the per-`α` partition-of-unity-weighted gradient atom integrands that
appear in the chart-frame scalar-component gradient `L²` assembly on a
closed Riemannian manifold `(M, g)`. The atoms covered are:

1. **Chart-source continuity for the covariant-derivative atom** —
   `aestronglyMeasurable_pou_mul_sqrt_sum_triv_chart_cov`.
2. **`L²` bound on the covariant-derivative atom sum** —
   `exists_eLpNorm_sq_pou_mul_sum_triv_chart_cov_le_const_mul_h1NormSq`.
3. **`L²` bound on the `raw²`-indicator atom over POU support** —
   `exists_integral_indicator_tsupp_raw_sq_le_const_mul_h1NormSq`.
4. **Unconditional `L²` bound on the Christoffel slot-correction sum** —
   `exists_eLpNorm_sq_pou_mul_sqrt_sum_christoffel_correction_le_const_mul_h1NormSq`.
5. **`AEStronglyMeasurable` of the per-`α` `raw²`-indicator atom** —
   `aestronglyMeasurable_indicator_tsupp_abs_raw`.
6. **`AEStronglyMeasurable` of the per-direction Christoffel slot-correction
   atom integrand** — `aestronglyMeasurable_pou_mul_sqrt_sum_christoffel_correction`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Connection

section CovariantAtomsChartSource

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The closed support of the chart-atlas partition-of-unity weight at `α`
is measurable in the Borel σ-algebra on `M`. -/
private lemma pouTsupport_measurableSet (α : M) :
    MeasurableSet (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
  (isClosed_tsupport _).measurableSet

private lemma chartTensorRSCovariantDerivative_eq_of_eq_at
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (X Y : Π b' : M, TangentSpace I b') {b : M} (hb : X b = Y b) :
    chartTensorRSCovariantDerivative (I := I) r s g α T X b =
      chartTensorRSCovariantDerivative (I := I) r s g α T Y b := by
  classical
  rw [chartTensorRSCovariantDerivative_def, chartTensorRSCovariantDerivative_def]
  rw [show tensorRSIntrinsicChartCLM (I := I) r s α T b (X b) =
      tensorRSIntrinsicChartCLM (I := I) r s α T b (Y b) from by rw [hb]]
  have hPara :
      chartLeviCivitaParallelCLM (I := I) g α b X =
        chartLeviCivitaParallelCLM (I := I) g α b Y := by
    unfold chartLeviCivitaParallelCLM
    rw [hb]
  have hInput : ∀ k : Fin r,
      chartTensorRSInputSlotCorrection (I := I) r s g α T X b k =
        chartTensorRSInputSlotCorrection (I := I) r s g α T Y b k := by
    intro k
    unfold chartTensorRSInputSlotCorrection
    rw [hPara]
  have hOutput : ∀ l : Fin s,
      chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l =
        chartTensorRSOutputSlotCorrection (I := I) r s g α T Y b l := by
    intro l
    unfold chartTensorRSOutputSlotCorrection
    rw [hPara]
  rw [Finset.sum_congr rfl (fun k _ => hInput k)]
  rw [Finset.sum_congr rfl (fun l _ => hOutput l)]

lemma chartTensorRSCovariantDerivative_eq_tensorCovDerivAt_at
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) (X : Π b' : M, TangentSpace I b')
    {b : M} (hb : b ∈ (chartAt H α).source) :
    chartTensorRSCovariantDerivative (I := I) r s g α
        (fun b' => S.toSection b') X b =
      tensorCovDerivAt (I := I) (M := M) g r s S b (X b) := by
  classical
  obtain ⟨Y, hYb⟩ :=
    ContMDiffSection.exists_eq_at (I := I) (F := E) (n := (⊤ : ℕ∞))
      (V := (TangentSpace I : M → Type _)) b (X b)
  have hswap :
      chartTensorRSCovariantDerivative (I := I) r s g α
          (fun b' => S.toSection b') X b =
        chartTensorRSCovariantDerivative (I := I) r s g α
          (fun b' => S.toSection b') Y.toFun b :=
    chartTensorRSCovariantDerivative_eq_of_eq_at
      (I := I) g r s α (fun b' => S.toSection b') X Y.toFun hYb.symm
  rw [hswap]
  have hb_goodSet : b ∈ chartLeviCivitaGoodSet (I := I) α := by
    rw [chartLeviCivitaGoodSet_eq_extChartAt_source (I := I) α,
        extChartAt_source_eq_chartAt_source (I := I)]
    exact hb
  have hagree :=
    chartTensorRSCovariantDerivative_eq_abstract_on_chartLeviCivitaGoodSet
      (I := I) (M := M) g r s α S.toSection Y hb_goodSet
  change chartTensorRSCovariantDerivative (I := I) r s g α
      (fun b' => S.toSection b') Y.toFun b =
    TensorRSNabla.tensorRSCovariantDerivative I M r s
      (LeviCivita (I := I) g) (fun b' => S.toSection b') b (X b)
  have hagree' :
      chartTensorRSCovariantDerivative (I := I) r s g α
          (fun b' => S.toSection b') Y.toFun b =
        TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g) (fun b' => S.toSection b') b (Y.toFun b) :=
    hagree
  rw [hagree']
  have hYb' : Y.toFun b = X b := hYb
  rw [hYb']

/-- On the chart-`α` source, the trivialisation-`α` `continuousLinearMapAt ℝ b`
applied to the chart-frame covariant derivative
`chartTensorRSCovariantDerivative r s g α S.toSection (chartBasisVecFiber α k) b`
equals the trivialisation `.2`-component of the bundled directional covariant
derivative `tensorCovDerivAt g r s S b (chartBasisVecFiber α k b)`. -/
private lemma triv_continuousLinearMapAt_chartTensorRSCovariantDerivative_eq_triv_snd
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) {b : M}
    (hb : b ∈ (chartAt H α).source)
    (k : Fin (Module.finrank ℝ E)) :
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
      (chartTensorRSCovariantDerivative (I := I) r s g α
        (fun b' => S.toSection b') (chartBasisVecFiber (I := I) α k) b) =
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α
        ⟨b, tensorCovDerivAt (I := I) (M := M) g r s S b
          (chartBasisVecFiber (I := I) α k b)⟩).2 := by
  classical
  have hcov_eq :=
    chartTensorRSCovariantDerivative_eq_tensorCovDerivAt_at
      (I := I) (M := M) g r s α S (chartBasisVecFiber (I := I) α k) hb
  rw [hcov_eq]
  have hbaseRS : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    change b ∈ (trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet ∩
      (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).baseSet
    refine ⟨?_, ?_⟩
    all_goals
      change b ∈ (trivializationAt E (TangentSpace I) α).baseSet
      exact hb
  have hcoe := (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).coe_linearMapAt_of_mem
    (R := ℝ) hbaseRS
  change ((trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ b)
      (tensorCovDerivAt (I := I) (M := M) g r s S b
        (chartBasisVecFiber (I := I) α k b)) = _
  exact congrFun hcoe _

/-- On the chart-`α` source, the trivialisation-projected chart-frame
covariant-derivative atom `b ↦ triv.continuousLinearMapAt b
  (chartTensorRSCovariantDerivative ... b)` is continuous as a function
valued in `TensorRSModel r s ℝ E`. -/
private lemma triv_chartTensorRSCovariantDerivative_continuousOn_chart_source
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) (k : Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun b : M =>
        (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSCovariantDerivative (I := I) r s g α
            (fun b' => S.toSection b') (chartBasisVecFiber (I := I) α k) b))
      ((chartAt H α).source) := by
  classical
  have hbase :
      ContinuousOn
        (fun b : M =>
          (trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α
            ⟨b, tensorCovDerivAt (I := I) (M := M) g r s S b
              (chartBasisVecFiber (I := I) α k b)⟩).2)
        (trivializationAt E (TangentSpace I) α).baseSet :=
    (tensorCovDeriv_chartBasis_trivImage_contMDiffOn
      (I := I) (M := M) g r s S α k).continuousOn
  have hbase_eq :
      (trivializationAt E (TangentSpace I) α).baseSet =
        (chartAt H α).source :=
    DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source α
  rw [hbase_eq] at hbase
  refine hbase.congr ?_
  intro b hb_chart
  exact triv_continuousLinearMapAt_chartTensorRSCovariantDerivative_eq_triv_snd
    (I := I) (M := M) g r s α S hb_chart k

private lemma norm_sq_sum_triv_chartTensorRSCovariantDerivative_continuousOn_chart_source
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) :
    ContinuousOn
      (fun b : M =>
        ∑ k : Fin (Module.finrank ℝ E),
          ‖(trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (chartTensorRSCovariantDerivative (I := I) r s g α
              (fun b' => S.toSection b') (chartBasisVecFiber (I := I) α k) b)‖
            ^ 2)
      ((chartAt H α).source) := by
  classical
  refine continuousOn_finset_sum _ (fun k _ => ?_)
  have h_proj := triv_chartTensorRSCovariantDerivative_continuousOn_chart_source
    (I := I) (M := M) g r s α S k
  have h_norm : ContinuousOn
      (fun b : M =>
        ‖(trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
          (chartTensorRSCovariantDerivative (I := I) r s g α
            (fun b' => S.toSection b') (chartBasisVecFiber (I := I) α k) b)‖)
      ((chartAt H α).source) := h_proj.norm
  exact h_norm.pow 2

private lemma pou_mul_sqrt_sum_continuousOn_chart_source
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) :
    ContinuousOn
      (fun b : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
          Real.sqrt
            (∑ k : Fin (Module.finrank ℝ E),
              ‖(trivializationAt (TensorRSModel r s ℝ E)
                  (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                    ℝ b
                (chartTensorRSCovariantDerivative (I := I) r s g α
                  (fun b' => S.toSection b')
                  (chartBasisVecFiber (I := I) α k) b)‖ ^ 2))
      ((chartAt H α).source) := by
  classical
  have h_pou_cont : Continuous
      (fun b : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b) :=
    ((chartAtlasPOU I M α).contMDiff.continuous)
  have h_pou_on : ContinuousOn
      (fun b : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b)
      ((chartAt H α).source) := h_pou_cont.continuousOn
  have h_sumsq :=
    norm_sq_sum_triv_chartTensorRSCovariantDerivative_continuousOn_chart_source
      (I := I) (M := M) g r s α S
  have h_sqrt : ContinuousOn
      (fun b : M =>
        Real.sqrt
          (∑ k : Fin (Module.finrank ℝ E),
            ‖(trivializationAt (TensorRSModel r s ℝ E)
                (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                  ℝ b
              (chartTensorRSCovariantDerivative (I := I) r s g α
                (fun b' => S.toSection b')
                (chartBasisVecFiber (I := I) α k) b)‖ ^ 2))
      ((chartAt H α).source) :=
    Real.continuous_sqrt.comp_continuousOn h_sumsq
  exact h_pou_on.mul h_sqrt

private lemma pou_mul_sqrt_sum_continuousOn_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) :
    ContinuousOn
      (fun b : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
          Real.sqrt
            (∑ k : Fin (Module.finrank ℝ E),
              ‖(trivializationAt (TensorRSModel r s ℝ E)
                  (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                    ℝ b
                (chartTensorRSCovariantDerivative (I := I) r s g α
                  (fun b' => S.toSection b')
                  (chartBasisVecFiber (I := I) α k) b)‖ ^ 2))
      (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) := by
  classical
  refine (pou_mul_sqrt_sum_continuousOn_chart_source
    (I := I) (M := M) g r s α S).mono ?_
  intro b hb
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α hb
  exact hb_base

private lemma pou_mul_sqrt_sum_zero_outside_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) {b : M}
    (hb : b ∉ tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
        Real.sqrt
          (∑ k : Fin (Module.finrank ℝ E),
            ‖(trivializationAt (TensorRSModel r s ℝ E)
                (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                  ℝ b
              (chartTensorRSCovariantDerivative (I := I) r s g α
                (fun b' => S.toSection b')
                (chartBasisVecFiber (I := I) α k) b)‖ ^ 2) = 0 := by
  classical
  have hρ_zero : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b = 0 := by
    by_contra hne
    exact hb (subset_tsupport _ hne)
  rw [hρ_zero, zero_mul]

private lemma pou_mul_sqrt_sum_eq_indicator
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) :
    (fun b : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
          Real.sqrt
            (∑ k : Fin (Module.finrank ℝ E),
              ‖(trivializationAt (TensorRSModel r s ℝ E)
                  (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                    ℝ b
                (chartTensorRSCovariantDerivative (I := I) r s g α
                  (fun b' => S.toSection b')
                  (chartBasisVecFiber (I := I) α k) b)‖ ^ 2)) =
      (tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
        (fun b : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            Real.sqrt
              (∑ k : Fin (Module.finrank ℝ E),
                ‖(trivializationAt (TensorRSModel r s ℝ E)
                    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                      ℝ b
                  (chartTensorRSCovariantDerivative (I := I) r s g α
                    (fun b' => S.toSection b')
                    (chartBasisVecFiber (I := I) α k) b)‖ ^ 2)) := by
  classical
  funext b
  by_cases hb : b ∈ tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
  · rw [Set.indicator_of_mem hb]
  · rw [Set.indicator_of_notMem hb]
    exact pou_mul_sqrt_sum_zero_outside_pouTsupport
      (I := I) (M := M) g r s α S hb

private lemma pou_mul_sqrt_sum_aestronglyMeasurable_restrict_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) :
    AEStronglyMeasurable
      (fun b : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
          Real.sqrt
            (∑ k : Fin (Module.finrank ℝ E),
              ‖(trivializationAt (TensorRSModel r s ℝ E)
                  (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                    ℝ b
                (chartTensorRSCovariantDerivative (I := I) r s g α
                  (fun b' => S.toSection b')
                  (chartBasisVecFiber (I := I) α k) b)‖ ^ 2))
      ((riemannianVolumeMeasure (I := I) (M := M) g).restrict
        (tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))) := by
  classical
  exact ContinuousOn.aestronglyMeasurable_of_isCompact
    (pou_mul_sqrt_sum_continuousOn_pouTsupport
      (I := I) (M := M) g r s α S)
    (pouTsupport_isCompact (I := I) (M := M) α)
    (pouTsupport_measurableSet (I := I) (M := M) α)

/-- **`AEStronglyMeasurable` of the per-`α` chart-frame covariant-derivative
atom integrand.** For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`,
a chart base point `α : M`, and a smooth compactly-supported `H^1` tensor
section `S : SmoothCcTensorH1 g r s`, the function

```
b ↦ ρ_α(b) * √(∑ k, ‖triv.continuousLinearMapAt b
                    (chartTensorRSCovariantDerivative r s g α
                      S.toSection (chartBasisVecFiber α k) b)‖²)
```

is `AEStronglyMeasurable` with respect to `riemannianVolumeMeasure g`. -/
theorem aestronglyMeasurable_pou_mul_sqrt_sum_triv_chart_cov
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensorH1 g r s) :
    AEStronglyMeasurable
      (fun b : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
          Real.sqrt
            (∑ k : Fin (Module.finrank ℝ E),
              ‖(trivializationAt (TensorRSModel r s ℝ E)
                  (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                    ℝ b
                (chartTensorRSCovariantDerivative (I := I) r s g α
                  (fun b' => S.toCcTensor.toSection b')
                  (chartBasisVecFiber (I := I) α k) b)‖ ^ 2))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  rw [pou_mul_sqrt_sum_eq_indicator (I := I) (M := M) g r s α S.toCcTensor]
  rw [aestronglyMeasurable_indicator_iff
    (pouTsupport_measurableSet (I := I) (M := M) α)]
  exact pou_mul_sqrt_sum_aestronglyMeasurable_restrict_pouTsupport
    (I := I) (M := M) g r s α S.toCcTensor

private lemma triv_continuousLinearMapAt_chart_cov_eq_chartRSTwistInv
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) {b : M} (hb : b ∈ (chartAt H α).source)
    (k : Fin (Module.finrank ℝ E)) :
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
      (chartTensorRSCovariantDerivative (I := I) r s g α
        (fun b' => S.toSection b') (chartBasisVecFiber (I := I) α k) b) =
      chartRSTwistInv (I := I) (M := M) α b r s
        (TensorRSSpace.toModel
          (tensorCovDerivAt (I := I) (M := M) g r s S b
            (chartBasisVecFiber (I := I) α k b))) := by
  classical
  have hcov_eq :=
    chartTensorRSCovariantDerivative_eq_tensorCovDerivAt_at
      (I := I) (M := M) g r s α S (chartBasisVecFiber (I := I) α k) hb
  rw [hcov_eq]
  exact triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel
    (I := I) (M := M) r s α (b := b) hb
    (tensorCovDerivAt (I := I) (M := M) g r s S b
      (chartBasisVecFiber (I := I) α k b))

private lemma pou_mul_sqrt_sum_triv_chart_cov_eq_pou_mul_sqrt_sum_chartRSTwistInv
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s) (b : M) :
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
        Real.sqrt
          (∑ k : Fin (Module.finrank ℝ E),
            ‖(trivializationAt (TensorRSModel r s ℝ E)
                (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
              (chartTensorRSCovariantDerivative (I := I) r s g α
                (fun b' => S.toSection b')
                (chartBasisVecFiber (I := I) α k) b)‖ ^ 2) =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
        Real.sqrt
          (∑ k : Fin (Module.finrank ℝ E),
            ‖chartRSTwistInv (I := I) (M := M) α b r s
                (TensorRSSpace.toModel
                  (tensorCovDerivAt (I := I) (M := M) g r s S b
                    (chartBasisVecFiber (I := I) α k b)))‖ ^ 2) := by
  classical
  by_cases hb : b ∈ tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
  · have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
      pouTsupport_subset_baseSet (I := I) (M := M) α hb
    have hb_chart : b ∈ (chartAt H α).source := hb_base
    have hsumeq :
        (∑ k : Fin (Module.finrank ℝ E),
          ‖(trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (chartTensorRSCovariantDerivative (I := I) r s g α
              (fun b' => S.toSection b')
              (chartBasisVecFiber (I := I) α k) b)‖ ^ 2) =
          ∑ k : Fin (Module.finrank ℝ E),
            ‖chartRSTwistInv (I := I) (M := M) α b r s
                (TensorRSSpace.toModel
                  (tensorCovDerivAt (I := I) (M := M) g r s S b
                    (chartBasisVecFiber (I := I) α k b)))‖ ^ 2 := by
      refine Finset.sum_congr rfl ?_
      intro k _
      rw [triv_continuousLinearMapAt_chart_cov_eq_chartRSTwistInv
        (I := I) (M := M) g r s α S hb_chart k]
    rw [hsumeq]
  · have hρ_zero : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b = 0 := by
      by_contra hne
      exact hb (subset_tsupport _ hne)
    rw [hρ_zero]
    ring

/-- **Per-`α` `L²` bound on the covariant-derivative atom sum.** For a closed
Riemannian manifold `(M, g)`, ranks `(r, s)`, and a chart base point `α : M`,
there is a non-negative real constant `C` (depending only on `(g, r, s, α)`)
such that for every smooth compactly-supported `H¹` tensor section
`S : SmoothCcTensorH1 g r s`,

```
eLpNorm
    (fun b ↦ ρ_α(b) *
      √ (∑ k, ‖triv.continuousLinearMapAt b
              (chartTensorRSCovariantDerivative r s g α S.toSection
                (chartBasisVecFiber α k) b)‖²))
    2 (riemannianVolumeMeasure g) ≤
  ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞),
```

where `ρ_α` is the chart-atlas partition-of-unity weight at `α`. The constant
`C` is independent of `S`. -/
theorem exists_eLpNorm_sq_pou_mul_sum_triv_chart_cov_le_const_mul_h1NormSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s),
        eLpNorm
            (fun b : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
                Real.sqrt
                  (∑ k : Fin (Module.finrank ℝ E),
                    ‖(trivializationAt (TensorRSModel r s ℝ E)
                        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                          ℝ b
                      (chartTensorRSCovariantDerivative (I := I) r s g α
                        (fun b' => S.toCcTensor.toSection b')
                        (chartBasisVecFiber (I := I) α k) b)‖ ^ 2))
            2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  obtain ⟨C, hC_nn, h_eL⟩ :=
    exists_eLpNorm_chartPou_mul_sqrt_sum_chartRSTwistInv_cov_norm_sq_le_const_mul_h1Norm
      (I := I) (M := M) g r s α
  refine ⟨C, hC_nn, ?_⟩
  intro S
  have h_pt :
      (fun b : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            Real.sqrt
              (∑ k : Fin (Module.finrank ℝ E),
                ‖(trivializationAt (TensorRSModel r s ℝ E)
                    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                      ℝ b
                  (chartTensorRSCovariantDerivative (I := I) r s g α
                    (fun b' => S.toCcTensor.toSection b')
                    (chartBasisVecFiber (I := I) α k) b)‖ ^ 2)) =
        (fun b : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
            Real.sqrt
              (∑ k : Fin (Module.finrank ℝ E),
                ‖chartRSTwistInv (I := I) (M := M) α b r s
                    (TensorRSSpace.toModel
                      (tensorCovDerivAt (I := I) (M := M) g r s
                        S.toCcTensor b
                        (chartBasisVecFiber (I := I) α k b)))‖ ^ 2)) := by
    funext b
    exact pou_mul_sqrt_sum_triv_chart_cov_eq_pou_mul_sqrt_sum_chartRSTwistInv
      (I := I) (M := M) g r s α S.toCcTensor b
  rw [h_pt]
  exact h_eL S

end CovariantAtomsChartSource

section RawAtoms

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

private lemma scalarOnE_raw_eq_raw_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M} (hb : b ∈ tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :
    scalarOnE (I := I) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
        (extChartAt I α b) =
      tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b := by
  classical
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α hb
  have hb_chart : b ∈ (chartAt H α).source := hb_base
  have hb_ext : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hb_chart
  exact scalarOnE_extChartAt (I := I) α
    (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) hb_ext

/-- **Pointwise quadratic upper bound on the chart-pullback raw scalar.** -/
private lemma scalarOnE_raw_sq_le_const_mul_tensorInner_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E))
        {b : M}, b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
          (scalarOnE (I := I) α
              (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
              (extChartAt I α b)) ^ 2 ≤
            C * tensorInnerPointwise (I := I) (M := M) g r s b
              (S.toFun b) (S.toFun b) := by
  classical
  obtain ⟨K, hK_nn, h_norm⟩ :=
    tensorTrivProj_norm_sq_le_const_mul_tensorInner
      (I := I) (M := M) (E := E) g r s α
  set C_proj : ℝ := chartComponentProjectionUniformBound (E := E) r s
  have hC_proj_nn : 0 ≤ C_proj :=
    chartComponentProjectionUniformBound_nonneg (E := E) r s
  refine ⟨C_proj ^ 2 * K, mul_nonneg (sq_nonneg _) hK_nn, ?_⟩
  intro S Idx Jdx b hb
  rw [scalarOnE_raw_eq_raw_on_pouTsupport (I := I) (M := M) g r s α S Idx Jdx hb]
  unfold tensorChartComponentRaw
  set T : TensorRSModel r s ℝ E :=
    tensorTrivProj (I := I) (M := M) g r s S α b
  set P_IJ : TensorRSModel r s ℝ E →L[ℝ] ℝ :=
    tensorChartComponentProjection (E := E) r s Idx Jdx
  have h_proj_le : ‖P_IJ T‖ ≤ C_proj * ‖T‖ :=
    (ContinuousLinearMap.le_opNorm _ _).trans
      (mul_le_mul_of_nonneg_right
        (tensorChartComponentProjection_norm_le_uniform (E := E) r s Idx Jdx)
        (norm_nonneg _))
  have h_proj_sq_le : (P_IJ T) ^ 2 ≤ C_proj ^ 2 * ‖T‖ ^ 2 := by
    have h_abs : (P_IJ T) ^ 2 = ‖P_IJ T‖ ^ 2 := by
      rw [Real.norm_eq_abs, sq_abs]
    rw [h_abs]
    have hsq := mul_self_le_mul_self (norm_nonneg _) h_proj_le
    have h_rhs : (C_proj * ‖T‖) * (C_proj * ‖T‖) = C_proj ^ 2 * ‖T‖ ^ 2 := by
      ring
    have h_lhs : ‖P_IJ T‖ * ‖P_IJ T‖ = ‖P_IJ T‖ ^ 2 := by rw [sq]
    linarith [hsq, h_lhs.symm.le, h_rhs.symm.le, h_lhs.le, h_rhs.le]
  have h_triv_sq_le : ‖T‖ ^ 2 ≤ K *
      tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b) := h_norm S b hb
  have hC_proj_sq_nn : 0 ≤ C_proj ^ 2 := sq_nonneg _
  have h_chain_sq : (P_IJ T) ^ 2 ≤
      C_proj ^ 2 *
        (K * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b)) := by
    have h_mul := mul_le_mul_of_nonneg_left h_triv_sq_le hC_proj_sq_nn
    exact h_proj_sq_le.trans h_mul
  have h_reassoc :
      C_proj ^ 2 *
        (K * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b)) =
        C_proj ^ 2 * K *
          tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b) := by ring
  linarith [h_chain_sq, h_reassoc.le, h_reassoc.symm.le]

private lemma indicator_scalarOnE_raw_sq_le_const_mul_tensorInner
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E))
        (b : M),
          ((tsupport (fun x : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
            (fun b' : M => scalarOnE (I := I) α
              (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
              (extChartAt I α b')) b) ^ 2 ≤
            C * tensorInnerPointwise (I := I) (M := M) g r s b
              (S.toFun b) (S.toFun b) := by
  classical
  obtain ⟨C, hC_nn, h_pt⟩ :=
    scalarOnE_raw_sq_le_const_mul_tensorInner_on_pouTsupport
      (I := I) (M := M) (E := E) g r s α
  refine ⟨C, hC_nn, ?_⟩
  intro S Idx Jdx b
  set ρSet : Set M := tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
  set F : M → ℝ := fun b' : M => scalarOnE (I := I) α
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
      (extChartAt I α b')
  by_cases hb : b ∈ ρSet
  · have h_ind_eq : ρSet.indicator F b = F b := Set.indicator_of_mem hb _
    rw [h_ind_eq]
    exact h_pt S Idx Jdx hb
  · have h_ind_eq : ρSet.indicator F b = 0 := Set.indicator_of_notMem hb _
    rw [h_ind_eq]
    have hQ_nn : 0 ≤ tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b) :=
      tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _
    have h_RHS_nn : 0 ≤ C * tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b) := mul_nonneg hC_nn hQ_nn
    have hzero_sq : (0 : ℝ) ^ 2 = 0 := by ring
    rw [hzero_sq]
    exact h_RHS_nn

lemma sq_eLpNorm_two_eq_lintegral_enorm_sq
    {α : Type*} [MeasurableSpace α] (μ : Measure α) (f : α → ℝ) :
    (eLpNorm f 2 μ) ^ 2 = ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
  classical
  have h2_ne_zero : (2 : ℝ≥0∞) ≠ 0 := by norm_num
  have h2_ne_top : (2 : ℝ≥0∞) ≠ (⊤ : ℝ≥0∞) := by norm_num
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (μ := μ) h2_ne_zero h2_ne_top]
  have h2_toReal : ((2 : ℝ≥0∞)).toReal = 2 := by show ENNReal.toReal 2 = 2; rfl
  rw [h2_toReal]
  have h_inner_eq : ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ (2 : ℝ) ∂μ =
      ∫⁻ x, (‖f x‖ₑ : ℝ≥0∞) ^ 2 ∂μ := by
    refine lintegral_congr_ae ?_
    filter_upwards with x
    rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) from by norm_num, ENNReal.rpow_natCast]
  rw [h_inner_eq, ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

lemma le_sqrt_of_sq_le {x y : ℝ≥0∞} (h : x ^ 2 ≤ y) :
    x ≤ y ^ ((1 : ℝ) / 2) := by
  have h_xpow : x = (x ^ 2) ^ ((1 : ℝ) / 2) := by
    rw [← ENNReal.rpow_natCast x 2, ← ENNReal.rpow_mul]
    norm_num
  conv_lhs => rw [h_xpow]
  exact ENNReal.rpow_le_rpow h (by norm_num)

lemma sqrt_ofReal_eq_ofReal_sqrt {S : ℝ} (hS : 0 ≤ S) :
    (ENNReal.ofReal S) ^ ((1 : ℝ) / 2) = ENNReal.ofReal (Real.sqrt S) := by
  rw [show S = Real.sqrt S * Real.sqrt S from (Real.mul_self_sqrt hS).symm,
    ENNReal.ofReal_mul (Real.sqrt_nonneg _),
    show (ENNReal.ofReal (Real.sqrt S)) * (ENNReal.ofReal (Real.sqrt S)) =
      (ENNReal.ofReal (Real.sqrt S)) ^ 2 from by ring,
    ← ENNReal.rpow_natCast _ 2, ← ENNReal.rpow_mul]
  norm_num

lemma eLpNorm_two_le_ofReal_sqrt
    {α : Type*} [MeasurableSpace α] {μ : Measure α} {f : α → ℝ}
    {S : ℝ} (hS : 0 ≤ S)
    (h_sq : (eLpNorm f 2 μ) ^ 2 ≤ ENNReal.ofReal S) :
    eLpNorm f 2 μ ≤ ENNReal.ofReal (Real.sqrt S) := by
  have h_pow := le_sqrt_of_sq_le h_sq
  rw [sqrt_ofReal_eq_ofReal_sqrt hS] at h_pow
  exact h_pow

private lemma sq_eLpNorm_indicator_raw_le_const_mul_tensorL2Inner
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        (eLpNorm (fun b : M =>
            (tsupport (fun x : M =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
              (fun b' : M => scalarOnE (I := I) α
                (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
                (extChartAt I α b')) b) 2
            (riemannianVolumeMeasure (I := I) (M := M) g)) ^ 2 ≤
          ENNReal.ofReal (C *
            tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun) := by
  classical
  obtain ⟨C, hC_nn, h_pt⟩ :=
    indicator_scalarOnE_raw_sq_le_const_mul_tensorInner
      (I := I) (M := M) (E := E) g r s α
  refine ⟨C, hC_nn, ?_⟩
  intro S Idx Jdx
  set f : M → ℝ := fun b : M =>
    (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
      (fun b' : M => scalarOnE (I := I) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
        (extChartAt I α b')) b
  set μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g
  have h_pt_enn : ∀ b : M,
      (‖f b‖ₑ : ℝ≥0∞) ^ 2 ≤
        ENNReal.ofReal (C * tensorInnerPointwise (I := I) (M := M)
          g r s b (S.toFun b) (S.toFun b)) := by
    intro b
    rw [show (‖f b‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal ((f b) ^ 2) by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2,
        sq_abs]]
    exact ENNReal.ofReal_le_ofReal (h_pt S Idx Jdx b)
  have h_inner_int := SmoothCcTensor.integrable_inner_cross
    (I := I) (M := M) (g := g) (r := r) (s := s) S S
  have h_C_smul_int :
      Integrable (fun b : M => C *
        tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toFun b) (S.toFun b)) μ :=
    h_inner_int.const_mul C
  have h_C_smul_nn :
      0 ≤ᵐ[μ] (fun b : M => C * tensorInnerPointwise
        (I := I) (M := M) g r s b (S.toFun b) (S.toFun b)) := by
    refine Filter.Eventually.of_forall ?_
    intro b
    exact mul_nonneg hC_nn
      (tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _)
  rw [sq_eLpNorm_two_eq_lintegral_enorm_sq μ f]
  have h_lint_le :
      ∫⁻ b, (‖f b‖ₑ : ℝ≥0∞) ^ 2 ∂μ ≤
        ∫⁻ b, ENNReal.ofReal (C * tensorInnerPointwise
          (I := I) (M := M) g r s b (S.toFun b) (S.toFun b)) ∂μ := by
    refine lintegral_mono_ae ?_
    filter_upwards with b using h_pt_enn b
  have h_lint_eq :
      ∫⁻ b, ENNReal.ofReal (C * tensorInnerPointwise
        (I := I) (M := M) g r s b (S.toFun b) (S.toFun b)) ∂μ =
        ENNReal.ofReal (∫ b, C * tensorInnerPointwise
          (I := I) (M := M) g r s b (S.toFun b) (S.toFun b) ∂μ) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
      h_C_smul_int h_C_smul_nn).symm
  rw [h_lint_eq] at h_lint_le
  have h_int_const_mul :
      ∫ b, C * tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toFun b) (S.toFun b) ∂μ =
        C * tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun := by
    unfold tensorL2Inner
    rw [integral_const_mul]
  rw [h_int_const_mul] at h_lint_le
  exact h_lint_le

private theorem indicator_eLpNorm_raw_le_const_mul_tensorL2Norm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensor g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm (fun b : M =>
            (tsupport (fun x : M =>
                ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
              (fun b' : M => scalarOnE (I := I) α
                (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
                (extChartAt I α b')) b) 2
            (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C *
            ENNReal.ofReal
              (tensorL2Norm (I := I) (M := M) g r s S.toFun) := by
  classical
  obtain ⟨C, hC_nn, h_sq⟩ :=
    sq_eLpNorm_indicator_raw_le_const_mul_tensorL2Inner
      (I := I) (M := M) (E := E) g r s α
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, ?_⟩
  intro S Idx Jdx
  have h_inner_nn :
      0 ≤ tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun := by
    unfold tensorL2Inner
    refine integral_nonneg ?_
    intro b
    exact tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _
  have h_norm_sq :
      tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun =
        (tensorL2Norm (I := I) (M := M) g r s S.toFun) ^ 2 := by
    unfold tensorL2Norm
    rw [sq, Real.mul_self_sqrt h_inner_nn]
  set S_total : ℝ := C *
    tensorL2Inner (I := I) (M := M) g r s S.toFun S.toFun with hS_total_def
  have hS_total_nn : 0 ≤ S_total := mul_nonneg hC_nn h_inner_nn
  have h_eLpNorm_le :=
    eLpNorm_two_le_ofReal_sqrt hS_total_nn (h_sq S Idx Jdx)
  have h_sqrt_factor :
      Real.sqrt S_total = Real.sqrt C *
        tensorL2Norm (I := I) (M := M) g r s S.toFun := by
    rw [hS_total_def, h_norm_sq, Real.sqrt_mul hC_nn,
      show (tensorL2Norm (I := I) (M := M) g r s S.toFun) ^ 2 =
        tensorL2Norm (I := I) (M := M) g r s S.toFun *
          tensorL2Norm (I := I) (M := M) g r s S.toFun from by ring,
      Real.sqrt_mul_self
        (tensorL2Norm_nonneg (I := I) (M := M) g r s S.toFun)]
  rw [h_sqrt_factor,
    ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at h_eLpNorm_le
  exact h_eLpNorm_le

private lemma tensorL2Norm_eq_norm_toCcTensor
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun =
      ‖S.toCcTensor‖ := by
  have h_sq := SmoothCcTensor.norm_sq_eq_inner_self
    (I := I) (M := M) (g := g) (r := r) (s := s) S.toCcTensor
  have h_l2_nn :
      0 ≤ tensorL2Inner (I := I) (M := M) g r s
        S.toCcTensor.toFun S.toCcTensor.toFun := by
    unfold tensorL2Inner
    refine MeasureTheory.integral_nonneg ?_
    intro x
    exact tensorInnerPointwise_nonneg (I := I) (M := M) g r s x _
  have h_norm_nn : 0 ≤ ‖S.toCcTensor‖ := norm_nonneg _
  have h_lhs :
      tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun =
        Real.sqrt (tensorL2Inner (I := I) (M := M) g r s
          S.toCcTensor.toFun S.toCcTensor.toFun) := rfl
  rw [h_lhs]
  have h_rhs :
      ‖S.toCcTensor‖ = Real.sqrt
        (tensorL2Inner (I := I) (M := M) g r s
          S.toCcTensor.toFun S.toCcTensor.toFun) := by
    rw [← Real.sqrt_sq h_norm_nn, h_sq]
  rw [h_rhs]

private lemma coe_nnnorm_eq_ofReal_norm {X : Type*} [SeminormedAddCommGroup X]
    (x : X) :
    (‖x‖₊ : ℝ≥0∞) = ENNReal.ofReal ‖x‖ := by
  rw [show ((‖x‖₊ : ℝ≥0∞)) = ‖x‖ₑ from (enorm_eq_nnnorm x).symm,
    ← ofReal_norm_eq_enorm x]

private lemma ofReal_tensorL2Norm_le_norm_ennreal
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensorH1 g r s) :
    ENNReal.ofReal
        (tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun) ≤
      (‖S‖₊ : ℝ≥0∞) := by
  rw [tensorL2Norm_eq_norm_toCcTensor (I := I) (M := M) g r s S]
  have h_l2_le_h1 :
      ‖S.toCcTensor‖ ≤ ‖S‖ :=
    SmoothCcTensorH1.l2Norm_le_h1Norm (I := I) (M := M) S
  rw [coe_nnnorm_eq_ofReal_norm S]
  exact ENNReal.ofReal_le_ofReal h_l2_le_h1

/-- **Per-`α` `L²` bound on the `raw²` chart-component indicator over POU
support.** -/
theorem exists_integral_indicator_tsupp_raw_sq_le_const_mul_h1NormSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s)
        (Idx : Fin r → Fin (Module.finrank ℝ E))
        (Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm
          (fun b : M => (tsupport (fun x : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
            (fun b' : M =>
              scalarOnE (I := I) α
                (tensorChartComponentRaw (I := I) (M := M)
                  g r s S.toCcTensor α Idx Jdx)
                (extChartAt I α b')) b) 2
            (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  obtain ⟨C, hC_nn, h_smoothCc⟩ :=
    indicator_eLpNorm_raw_le_const_mul_tensorL2Norm
      (I := I) (M := M) (E := E) g r s α
  refine ⟨C, hC_nn, ?_⟩
  intro S Idx Jdx
  have h_smoothCc' :
      eLpNorm (fun b : M =>
          (tsupport (fun x : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
            (fun b' : M => scalarOnE (I := I) α
              (tensorChartComponentRaw (I := I) (M := M)
                g r s S.toCcTensor α Idx Jdx)
              (extChartAt I α b')) b) 2
        (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal C *
          ENNReal.ofReal
            (tensorL2Norm (I := I) (M := M) g r s
              S.toCcTensor.toFun) :=
    h_smoothCc S.toCcTensor Idx Jdx
  have h_rhs_le :
      ENNReal.ofReal C *
        ENNReal.ofReal
          (tensorL2Norm (I := I) (M := M) g r s S.toCcTensor.toFun) ≤
        ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) :=
    mul_le_mul_of_nonneg_left
      (ofReal_tensorL2Norm_le_norm_ennreal (I := I) (M := M) g r s S)
      (by exact zero_le _)
  exact h_smoothCc'.trans h_rhs_le

end RawAtoms

section AtomMeasurability

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The closed support of the chart-atlas partition-of-unity weight at `α`
is measurable in the Borel σ-algebra on `M`. -/
private lemma pouTsupport_measurableSet_meas (α : M) :
    MeasurableSet (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
  (isClosed_tsupport _).measurableSet

private lemma scalarOnE_raw_eq_raw_on_pouTsupport_meas
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E))
    {b : M} (hb : b ∈ tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :
    scalarOnE (I := I) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
        (extChartAt I α b) =
      tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b := by
  classical
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α hb
  have hb_chart : b ∈ (chartAt H α).source := hb_base
  have hb_ext : b ∈ (extChartAt I α).source := by
    rw [extChartAt_source_eq_chartAt_source (I := I)]
    exact hb_chart
  exact scalarOnE_extChartAt (I := I) α
    (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx) hb_ext

private lemma tensorChartComponentRaw_continuousOn_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
      (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) := by
  classical
  have h_on : ContinuousOn
      (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
      ((chartAt H α).source) :=
    (tensorChartComponentRaw_contMDiffOn_chart_source
      (I := I) (M := M) g r s S α Idx Jdx).continuousOn
  refine h_on.mono ?_
  intro b hb
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet :=
    pouTsupport_subset_baseSet (I := I) (M := M) α hb
  exact hb_base

private lemma scalarOnE_raw_continuousOn_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun b : M => scalarOnE (I := I) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
        (extChartAt I α b))
      (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) := by
  classical
  have h_raw_on :=
    tensorChartComponentRaw_continuousOn_pouTsupport
      (I := I) (M := M) g r s α S Idx Jdx
  refine h_raw_on.congr ?_
  intro b hb
  exact scalarOnE_raw_eq_raw_on_pouTsupport_meas
    (I := I) (M := M) g r s α S Idx Jdx hb

private lemma abs_scalarOnE_raw_continuousOn_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    ContinuousOn
      (fun b : M => |scalarOnE (I := I) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
        (extChartAt I α b)|)
      (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) := by
  classical
  have h_inner := scalarOnE_raw_continuousOn_pouTsupport
    (I := I) (M := M) g r s α S Idx Jdx
  exact _root_.continuous_abs.comp_continuousOn h_inner

private lemma abs_scalarOnE_raw_aestronglyMeasurable_restrict_pouTsupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensor g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    AEStronglyMeasurable
      (fun b : M => |scalarOnE (I := I) α
        (tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx)
        (extChartAt I α b)|)
      ((riemannianVolumeMeasure (I := I) (M := M) g).restrict
        (tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))) := by
  classical
  exact ContinuousOn.aestronglyMeasurable_of_isCompact
    (abs_scalarOnE_raw_continuousOn_pouTsupport
      (I := I) (M := M) g r s α S Idx Jdx)
    (pouTsupport_isCompact (I := I) (M := M) α)
    (pouTsupport_measurableSet_meas (I := I) (M := M) α)

/-- **`AEStronglyMeasurable` of the per-`α` `raw²`-indicator atom.** -/
theorem aestronglyMeasurable_indicator_tsupp_abs_raw
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (S : SmoothCcTensorH1 g r s)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    AEStronglyMeasurable
      (fun b : M =>
        (tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
          (fun b' : M => |scalarOnE (I := I) α
            (tensorChartComponentRaw (I := I) (M := M)
              g r s S.toCcTensor α Idx Jdx)
            (extChartAt I α b')|) b)
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  set ρSet : Set M := tsupport (fun x : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) with hρSet_def
  have hρSet_meas : MeasurableSet ρSet :=
    pouTsupport_measurableSet_meas (I := I) (M := M) α
  rw [aestronglyMeasurable_indicator_iff hρSet_meas]
  exact abs_scalarOnE_raw_aestronglyMeasurable_restrict_pouTsupport
    (I := I) (M := M) g r s α S.toCcTensor Idx Jdx

section ChristoffelAtomMeasurability

variable (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
  (j : Fin (Module.finrank ℝ E))

private def trivInput
    (T : Π b' : M, TensorRSSpace r s I b') (b : M) (k : Fin r) :
    TensorRSModel r s ℝ E :=
  (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
    (chartTensorRSInputSlotCorrection (I := I) r s g α
      (fun b' => T b') (chartBasisVecFiber (I := I) α j) b k)

private def trivOutput
    (T : Π b' : M, TensorRSSpace r s I b') (b : M) (l : Fin s) :
    TensorRSModel r s ℝ E :=
  (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
    (chartTensorRSOutputSlotCorrection (I := I) r s g α
      (fun b' => T b') (chartBasisVecFiber (I := I) α j) b l)

private def christoffelAtomIntegrand
    (T : Π b' : M, TensorRSSpace r s I b') (b : M) : ℝ :=
  ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
    Real.sqrt
      ((∑ k : Fin r, ‖trivInput (I := I) g r s α j T b k‖ ^ 2) +
       (∑ l : Fin s, ‖trivOutput (I := I) g r s α j T b l‖ ^ 2))

private lemma triv_continuousLinearMapAt_eq_triv_snd
    {b : M} (hb : b ∈ (chartAt H α).source) (v : TensorRSSpace r s I b) :
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b v =
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α ⟨b, v⟩).2 := by
  classical
  have hbaseRS : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    change b ∈ (trivializationAt (Tensor0SModel r ℝ E)
        (fun y : M => Tensor0SSpace r I y) α).baseSet ∩
      (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).baseSet
    refine ⟨?_, ?_⟩
    all_goals
      change b ∈ (trivializationAt E (TangentSpace I) α).baseSet
      exact hb
  have hcoe := (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).coe_linearMapAt_of_mem
    (R := ℝ) hbaseRS
  change ((trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).linearMapAt ℝ b) v = _
  exact congrFun hcoe _

variable {g r s α j} in
private lemma trivInput_continuousOn_chartSource (S : SmoothCcTensor g r s)
    (k : Fin r) :
    ContinuousOn (fun b : M => trivInput (I := I) g r s α j S.toSection b k)
      ((chartAt H α).source) := by
  classical
  have h_trivImage :=
    (chartTensorRSInputSlotCorrection_chartBasisVec_trivImage_contMDiffOn_chartSource
      (I := I) (M := M) g r s α
      (fun b' : M => S.toSection b') S.toSection.contMDiff j k).continuousOn
  refine h_trivImage.congr ?_
  intro b hb
  exact triv_continuousLinearMapAt_eq_triv_snd (I := I) (r := r) (s := s)
    (α := α) (b := b) hb
    (chartTensorRSInputSlotCorrection (I := I) r s g α
      (fun b' => S.toSection b') (chartBasisVecFiber (I := I) α j) b k)

variable {g r s α j} in
private lemma trivOutput_continuousOn_chartSource (S : SmoothCcTensor g r s)
    (l : Fin s) :
    ContinuousOn (fun b : M => trivOutput (I := I) g r s α j S.toSection b l)
      ((chartAt H α).source) := by
  classical
  have h_trivImage :=
    (chartTensorRSOutputSlotCorrection_chartBasisVec_trivImage_contMDiffOn_chartSource
      (I := I) (M := M) g r s α
      (fun b' : M => S.toSection b') S.toSection.contMDiff j l).continuousOn
  refine h_trivImage.congr ?_
  intro b hb
  exact triv_continuousLinearMapAt_eq_triv_snd (I := I) (r := r) (s := s)
    (α := α) (b := b) hb
    (chartTensorRSOutputSlotCorrection (I := I) r s g α
      (fun b' => S.toSection b') (chartBasisVecFiber (I := I) α j) b l)

variable {g r s α j} in
private lemma christoffelAtomIntegrand_continuousOn_chartSource
    (S : SmoothCcTensor g r s) :
    ContinuousOn (christoffelAtomIntegrand (I := I) g r s α j S.toSection)
      ((chartAt H α).source) := by
  classical
  have h_pou : ContinuousOn
      (fun b : M => ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b)
      ((chartAt H α).source) :=
    ((chartAtlasPOU I M α).contMDiff.continuous).continuousOn
  have h_input : ContinuousOn
      (fun b : M => ∑ k : Fin r, ‖trivInput (I := I) g r s α j S.toSection b k‖ ^ 2)
      ((chartAt H α).source) :=
    continuousOn_finset_sum _ (fun k _ =>
      (trivInput_continuousOn_chartSource (I := I) S k).norm.pow 2)
  have h_output : ContinuousOn
      (fun b : M => ∑ l : Fin s, ‖trivOutput (I := I) g r s α j S.toSection b l‖ ^ 2)
      ((chartAt H α).source) :=
    continuousOn_finset_sum _ (fun l _ =>
      (trivOutput_continuousOn_chartSource (I := I) S l).norm.pow 2)
  have h_sumsq := h_input.add h_output
  have h_sqrt := Real.continuous_sqrt.comp_continuousOn h_sumsq
  exact h_pou.mul h_sqrt

variable {g r s α j} in
private lemma christoffelAtomIntegrand_continuousOn_pouTsupport
    (S : SmoothCcTensor g r s) :
    ContinuousOn (christoffelAtomIntegrand (I := I) g r s α j S.toSection)
      (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) := by
  classical
  refine (christoffelAtomIntegrand_continuousOn_chartSource (I := I) S).mono ?_
  intro b hb
  exact pouTsupport_subset_baseSet (I := I) (M := M) α hb

variable {g r s α j} in
private lemma christoffelAtomIntegrand_zero_outside_pouTsupport
    (T : Π b' : M, TensorRSSpace r s I b') {b : M}
    (hb : b ∉ tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :
    christoffelAtomIntegrand (I := I) g r s α j T b = 0 := by
  classical
  have hρ_zero : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b = 0 := by
    by_contra hne
    exact hb (subset_tsupport _ hne)
  simp [christoffelAtomIntegrand, hρ_zero]

variable {g r s α j} in
private lemma christoffelAtomIntegrand_eq_indicator
    (T : Π b' : M, TensorRSSpace r s I b') :
    christoffelAtomIntegrand (I := I) g r s α j T =
      (tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)).indicator
        (christoffelAtomIntegrand (I := I) g r s α j T) := by
  classical
  funext b
  by_cases hb : b ∈ tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
  · rw [Set.indicator_of_mem hb]
  · rw [Set.indicator_of_notMem hb]
    exact christoffelAtomIntegrand_zero_outside_pouTsupport (I := I) T hb

variable {g r s α j} in
private lemma christoffelAtomIntegrand_aestronglyMeasurable_restrict_pouTsupport
    (S : SmoothCcTensor g r s) :
    AEStronglyMeasurable
      (christoffelAtomIntegrand (I := I) g r s α j S.toSection)
      ((riemannianVolumeMeasure (I := I) (M := M) g).restrict
        (tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x))) := by
  classical
  exact ContinuousOn.aestronglyMeasurable_of_isCompact
    (christoffelAtomIntegrand_continuousOn_pouTsupport (I := I) S)
    (pouTsupport_isCompact (I := I) (M := M) α)
    (pouTsupport_measurableSet_meas (I := I) (M := M) α)

end ChristoffelAtomMeasurability

/-- **`AEStronglyMeasurable` of the per-`α` per-direction Christoffel
slot-correction atom integrand.** -/
theorem aestronglyMeasurable_pou_mul_sqrt_sum_christoffel_correction
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (j : Fin (Module.finrank ℝ E))
    (S : SmoothCcTensorH1 g r s) :
    AEStronglyMeasurable
      (fun b : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
          Real.sqrt
            ((∑ k : Fin r,
                ‖(trivializationAt (TensorRSModel r s ℝ E)
                    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                      ℝ b
                  (chartTensorRSInputSlotCorrection (I := I) r s g α
                    (fun b' => S.toCcTensor.toSection b')
                    (chartBasisVecFiber (I := I) α j) b k)‖ ^ 2) +
              (∑ l : Fin s,
                ‖(trivializationAt (TensorRSModel r s ℝ E)
                    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                      ℝ b
                  (chartTensorRSOutputSlotCorrection (I := I) r s g α
                    (fun b' => S.toCcTensor.toSection b')
                    (chartBasisVecFiber (I := I) α j) b l)‖ ^ 2)))
      (riemannianVolumeMeasure (I := I) (M := M) g) := by
  classical
  change AEStronglyMeasurable
    (christoffelAtomIntegrand (I := I) g r s α j S.toCcTensor.toSection)
    (riemannianVolumeMeasure (I := I) (M := M) g)
  rw [christoffelAtomIntegrand_eq_indicator (I := I)
    (T := fun b' : M => S.toCcTensor.toSection b')]
  rw [aestronglyMeasurable_indicator_iff
    (pouTsupport_measurableSet_meas (I := I) (M := M) α)]
  exact christoffelAtomIntegrand_aestronglyMeasurable_restrict_pouTsupport
    (I := I) S.toCcTensor

end AtomMeasurability

section CovariantAtomsRiemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

/-- The `tsupport` of the chart-atlas partition-of-unity weight at `α` is
compact (closed in a compact ambient space). -/
private lemma covRiem_pouTsupport_isCompact (α : M) :
    IsCompact (tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
  (isClosed_tsupport _).isCompact

/-- The `tsupport` of the chart-atlas partition-of-unity weight at `α` is
contained in the chart-`α` source. -/
private lemma covRiem_pouTsupport_subset_chartSource (α : M) :
    tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
      (chartAt H α).source :=
  chartAtlasPOU_isSubordinate (I := I) (M := M) α

/-- Membership in the chart-`α` source upgrades to membership in the
chart-`(r, s)` trivialisation base set. -/
private lemma covRiem_mem_baseSet_of_mem_chartSource
    (r s : ℕ) (α : M) {b : M} (hb : b ∈ (chartAt H α).source) :
    b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
  change b ∈ (trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).baseSet ∩
    (trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) α).baseSet
  refine ⟨?_, ?_⟩
  all_goals
    change b ∈ (trivializationAt E (TangentSpace I) α).baseSet
    rw [DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source]
    exact hb

set_option synthInstance.maxHeartbeats 800000 in
attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **Per-`α` Riemannian-fibre-norm covariant-derivative atom `L²` bound
(HLCC-free).** For a closed Riemannian manifold `(M, g)`, ranks `(r, s)`, and a
chart base point `α`, there is a non-negative real constant `C` (depending only
on `(g, r, s, α)`) such that for every smooth compactly-supported `H¹` tensor
section `S : SmoothCcTensorH1 g r s` and all multi-indices `Idx, Jdx`,

```
eLpNorm
    (fun b ↦ ρ_α(b) · √(∑ₖ ‖∇^chart_k S(b)‖²_Riem))
    2 (riemannianVolumeMeasure g) ≤
  ENNReal.ofReal C · (‖S‖₊ : ℝ≥0∞),
```

where `ρ_α` is the chart-atlas partition-of-unity weight at `α` and the fibre
norm `‖·‖` on `TensorRSSpace r s I b` is the `g`-induced
`Bundle.RiemannianBundle` norm (installed via `letI`). The constant `C` is
independent of `S`, of the multi-indices, and of the base point. No
chart-locality predicate is required. -/
theorem exists_eLpNorm_pou_mul_sum_fiber_chart_cov_le_const_mul_h1Norm_unconditional
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s)
        (_Idx : Fin r → Fin (Module.finrank ℝ E))
        (_Jdx : Fin s → Fin (Module.finrank ℝ E)),
        eLpNorm
            (fun b : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
                Real.sqrt
                  (∑ k : Fin (Module.finrank ℝ E),
                    ‖chartTensorRSCovariantDerivative (I := I) r s g α
                        (fun b' => S.toCcTensor.toSection b')
                        (chartBasisVecFiber (I := I) α k) b‖ ^ 2))
            2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  obtain ⟨Cg2, hCg2_nn, hG2⟩ :=
    exists_eLpNorm_sq_pou_mul_sum_triv_chart_cov_le_const_mul_h1NormSq
      (I := I) (M := M) g r s α
  have hK_cpt :
      IsCompact (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
    covRiem_pouTsupport_isCompact (I := I) (M := M) α
  have hK_sub :
      tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆
        (chartAt H α).source :=
    covRiem_pouTsupport_subset_chartSource (I := I) (M := M) α
  obtain ⟨Cop, hCop_pos, hCop_bound⟩ :=
    tensorRSChartFiberFromModel_opNorm_isBounded_on_compact_unconditional
      (I := I) (M := M) g r s α hK_cpt hK_sub
  have hCop_nn : 0 ≤ Cop := le_of_lt hCop_pos
  refine ⟨Cop * Cg2, mul_nonneg hCop_nn hCg2_nn, ?_⟩
  intro S _Idx _Jdx
  set gF : M → ℝ := fun b : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
      Real.sqrt
        (∑ k : Fin (Module.finrank ℝ E),
          ‖chartTensorRSCovariantDerivative (I := I) r s g α
              (fun b' => S.toCcTensor.toSection b')
              (chartBasisVecFiber (I := I) α k) b‖ ^ 2)
    with hgF_def
  set gM : M → ℝ := fun b : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
      Real.sqrt
        (∑ k : Fin (Module.finrank ℝ E),
          ‖(trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (chartTensorRSCovariantDerivative (I := I) r s g α
              (fun b' => S.toCcTensor.toSection b')
              (chartBasisVecFiber (I := I) α k) b)‖ ^ 2)
    with hgM_def
  have h_ptwise : ∀ b : M, gF b ≤ Cop * gM b := by
    intro b
    by_cases hb : b ∈ tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
    · have hb_chart : b ∈ (chartAt H α).source := hK_sub hb
      have hb_base : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).baseSet :=
        covRiem_mem_baseSet_of_mem_chartSource (I := I) (M := M) r s α hb_chart
      have hρ_nn : 0 ≤ ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b :=
        (chartAtlasPOU I M).nonneg α b
      have h_per_k : ∀ k : Fin (Module.finrank ℝ E),
          ‖chartTensorRSCovariantDerivative (I := I) r s g α
              (fun b' => S.toCcTensor.toSection b')
              (chartBasisVecFiber (I := I) α k) b‖ ^ 2 ≤
            Cop ^ 2 *
              ‖(trivializationAt (TensorRSModel r s ℝ E)
                  (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
                (chartTensorRSCovariantDerivative (I := I) r s g α
                  (fun b' => S.toCcTensor.toSection b')
                  (chartBasisVecFiber (I := I) α k) b)‖ ^ 2 := by
        intro k
        set X : TensorRSSpace r s I b :=
          chartTensorRSCovariantDerivative (I := I) r s g α
            (fun b' => S.toCcTensor.toSection b')
            (chartBasisVecFiber (I := I) α k) b with hX_def
        set v : TensorRSModel r s ℝ E :=
          (trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b X
          with hv_def
        have h_roundtrip :
            ((trivializationAt (TensorRSModel r s ℝ E)
                (fun y : M => TensorRSSpace r s I y) α).symmL ℝ b v :
              TensorRSSpace r s I b) = X := by
          rw [hv_def]
          exact (trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).symmL_continuousLinearMapAt
            (R := ℝ) hb_base X
        have h_op : ‖((trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).symmL ℝ b v :
              TensorRSSpace r s I b)‖ ≤ Cop * ‖v‖ :=
          hCop_bound b hb v
        rw [h_roundtrip] at h_op
        have hX_nn : 0 ≤ ‖X‖ := norm_nonneg _
        have h_sq := mul_self_le_mul_self hX_nn h_op
        have h_lhs : ‖X‖ * ‖X‖ = ‖X‖ ^ 2 := by rw [sq]
        have h_rhs : (Cop * ‖v‖) * (Cop * ‖v‖) = Cop ^ 2 * ‖v‖ ^ 2 := by ring
        rw [hv_def] at h_sq ⊢
        nlinarith [h_sq, h_lhs, h_rhs]
      have h_sum_le :
          (∑ k : Fin (Module.finrank ℝ E),
            ‖chartTensorRSCovariantDerivative (I := I) r s g α
                (fun b' => S.toCcTensor.toSection b')
                (chartBasisVecFiber (I := I) α k) b‖ ^ 2) ≤
            Cop ^ 2 *
              (∑ k : Fin (Module.finrank ℝ E),
                ‖(trivializationAt (TensorRSModel r s ℝ E)
                    (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
                  (chartTensorRSCovariantDerivative (I := I) r s g α
                    (fun b' => S.toCcTensor.toSection b')
                    (chartBasisVecFiber (I := I) α k) b)‖ ^ 2) := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum (fun k _ => h_per_k k)
      have h_sumM_nn :
          0 ≤ ∑ k : Fin (Module.finrank ℝ E),
            ‖(trivializationAt (TensorRSModel r s ℝ E)
                (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
              (chartTensorRSCovariantDerivative (I := I) r s g α
                (fun b' => S.toCcTensor.toSection b')
                (chartBasisVecFiber (I := I) α k) b)‖ ^ 2 :=
        Finset.sum_nonneg (fun k _ => sq_nonneg _)
      have h_sqrt_le :
          Real.sqrt
              (∑ k : Fin (Module.finrank ℝ E),
                ‖chartTensorRSCovariantDerivative (I := I) r s g α
                    (fun b' => S.toCcTensor.toSection b')
                    (chartBasisVecFiber (I := I) α k) b‖ ^ 2) ≤
            Cop *
              Real.sqrt
                (∑ k : Fin (Module.finrank ℝ E),
                  ‖(trivializationAt (TensorRSModel r s ℝ E)
                      (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
                    (chartTensorRSCovariantDerivative (I := I) r s g α
                      (fun b' => S.toCcTensor.toSection b')
                      (chartBasisVecFiber (I := I) α k) b)‖ ^ 2) := by
        have h1 := Real.sqrt_le_sqrt h_sum_le
        rwa [Real.sqrt_mul (sq_nonneg Cop), Real.sqrt_sq hCop_nn] at h1
      have h_mul :=
        mul_le_mul_of_nonneg_left h_sqrt_le hρ_nn
      rw [hgF_def, hgM_def]
      calc ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
              Real.sqrt
                (∑ k : Fin (Module.finrank ℝ E),
                  ‖chartTensorRSCovariantDerivative (I := I) r s g α
                      (fun b' => S.toCcTensor.toSection b')
                      (chartBasisVecFiber (I := I) α k) b‖ ^ 2)
            ≤ ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
                (Cop *
                  Real.sqrt
                    (∑ k : Fin (Module.finrank ℝ E),
                      ‖(trivializationAt (TensorRSModel r s ℝ E)
                          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                            ℝ b
                        (chartTensorRSCovariantDerivative (I := I) r s g α
                          (fun b' => S.toCcTensor.toSection b')
                          (chartBasisVecFiber (I := I) α k) b)‖ ^ 2)) := h_mul
          _ = Cop *
                (((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
                  Real.sqrt
                    (∑ k : Fin (Module.finrank ℝ E),
                      ‖(trivializationAt (TensorRSModel r s ℝ E)
                          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt
                            ℝ b
                        (chartTensorRSCovariantDerivative (I := I) r s g α
                          (fun b' => S.toCcTensor.toSection b')
                          (chartBasisVecFiber (I := I) α k) b)‖ ^ 2)) := by ring
    · have hρ_zero : ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b = 0 := by
        by_contra hne
        exact hb (subset_tsupport _ hne)
      simp only [hgF_def, hgM_def, hρ_zero, zero_mul, mul_zero, le_refl]
  have hgF_nn : ∀ b : M, 0 ≤ gF b := by
    intro b
    rw [hgF_def]
    exact mul_nonneg ((chartAtlasPOU I M).nonneg α b)
      (Real.sqrt_nonneg _)
  have h_mono :
      eLpNorm gF 2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        eLpNorm (Cop • gM) 2 (riemannianVolumeMeasure (I := I) (M := M) g) := by
    refine eLpNorm_mono_real (fun b => ?_)
    rw [Real.norm_of_nonneg (hgF_nn b)]
    simpa [Pi.smul_apply, smul_eq_mul] using h_ptwise b
  have h_smul :
      eLpNorm (Cop • gM) 2 (riemannianVolumeMeasure (I := I) (M := M) g) =
        ENNReal.ofReal Cop *
          eLpNorm gM 2 (riemannianVolumeMeasure (I := I) (M := M) g) := by
    rw [eLpNorm_const_smul Cop gM, Real.enorm_eq_ofReal hCop_nn]
  have hG2' :
      eLpNorm gM 2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
        ENNReal.ofReal Cg2 * (‖S‖₊ : ℝ≥0∞) := by
    rw [hgM_def]; exact hG2 S
  calc eLpNorm gF 2 (riemannianVolumeMeasure (I := I) (M := M) g)
      ≤ eLpNorm (Cop • gM) 2 (riemannianVolumeMeasure (I := I) (M := M) g) := h_mono
    _ = ENNReal.ofReal Cop *
          eLpNorm gM 2 (riemannianVolumeMeasure (I := I) (M := M) g) := h_smul
    _ ≤ ENNReal.ofReal Cop * (ENNReal.ofReal Cg2 * (‖S‖₊ : ℝ≥0∞)) :=
        mul_le_mul_of_nonneg_left hG2' (zero_le _)
    _ = ENNReal.ofReal (Cop * Cg2) * (‖S‖₊ : ℝ≥0∞) := by
        rw [ENNReal.ofReal_mul hCop_nn, mul_assoc]

end CovariantAtomsRiemannian

section ChristoffelAtomsRiemannian

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [Module.Finite ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

open DifferentialGeometry.Tensor.Tensor0SRiemannian

private noncomputable def chrRiemBasisCoordSup : ℝ :=
  (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sup'
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩)
    (fun i => ‖((chartModelBasis E).coord i).toContinuousLinearMap‖)

private noncomputable def chrRiemBasisVecSup : ℝ :=
  (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sup'
    (Finset.univ_nonempty_iff.mpr ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩)
    (fun k => ‖(chartModelBasis E) k‖)

private lemma chrRiemBasisCoordSup_nonneg : 0 ≤ chrRiemBasisCoordSup (E := E) := by
  unfold chrRiemBasisCoordSup
  set i₀ : Fin (Module.finrank ℝ E) := ⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩
  calc (0 : ℝ) ≤ ‖((chartModelBasis E).coord i₀).toContinuousLinearMap‖ := norm_nonneg _
    _ ≤ _ := Finset.le_sup' (f := fun i =>
        ‖((chartModelBasis E).coord i).toContinuousLinearMap‖) (Finset.mem_univ i₀)

private lemma chrRiemBasisVecSup_nonneg : 0 ≤ chrRiemBasisVecSup (E := E) := by
  unfold chrRiemBasisVecSup
  have hne : (Finset.univ : Finset (Fin (Module.finrank ℝ E))).Nonempty :=
    Finset.univ_nonempty_iff.mpr ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩
  obtain ⟨k₀, hk₀⟩ := hne
  exact le_trans (norm_nonneg _)
    (Finset.le_sup' (f := fun k => ‖(chartModelBasis E) k‖) hk₀)

private lemma chrRiem_repr_coord_abs_le (x : E) (i : Fin (Module.finrank ℝ E)) :
    |((chartModelBasis E).repr x) i| ≤ chrRiemBasisCoordSup (E := E) * ‖x‖ := by
  have h_eq : (chartModelBasis E).repr x i =
      ((chartModelBasis E).coord i).toContinuousLinearMap x := rfl
  rw [h_eq, ← Real.norm_eq_abs]
  calc ‖((chartModelBasis E).coord i).toContinuousLinearMap x‖
      ≤ ‖((chartModelBasis E).coord i).toContinuousLinearMap‖ * ‖x‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ chrRiemBasisCoordSup (E := E) * ‖x‖ := by
        apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
        exact Finset.le_sup'
          (f := fun i => ‖((chartModelBasis E).coord i).toContinuousLinearMap‖)
          (Finset.mem_univ _)

private lemma chrRiem_basis_vec_norm_le (k : Fin (Module.finrank ℝ E)) :
    ‖(chartModelBasis E) k‖ ≤ chrRiemBasisVecSup (E := E) :=
  Finset.le_sup' (f := fun k => ‖(chartModelBasis E) k‖) (Finset.mem_univ _)

/-- Honest model-space norm bound on `christoffelCorrection g α b Y v`,
controlled by `C · ‖Y‖ · ‖trivToE α b v‖` uniformly on the chart-`α`
partition-of-unity `tsupport`. No chart-locality predicate is required. -/
private theorem christoffelCorrection_riem_norm_le_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ (Y : E) (v : TangentSpace I b),
          ‖christoffelCorrection (I := I) g α b Y v‖ ≤
            C * ‖Y‖ * ‖trivToE (I := I) α b v‖ := by
  classical
  obtain ⟨CΓ, hCΓ_nn, hCΓ_le⟩ :=
    chartChristoffel_bdd_on_pou_tsupport (I := I) (M := M) g α
  set n : ℕ := Module.finrank ℝ E
  set Cc := chrRiemBasisCoordSup (E := E)
  set Cv := chrRiemBasisVecSup (E := E)
  refine ⟨(n : ℝ) ^ 3 * Cc ^ 2 * Cv * CΓ,
    mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (Nat.cast_nonneg _) 3)
      (sq_nonneg _)) (chrRiemBasisVecSup_nonneg (E := E))) hCΓ_nn, ?_⟩
  intro b hb Y v
  have hb_image : extChartAt I α b ∈ (extChartAt I α) ''
      (tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
    ⟨b, hb, rfl⟩
  rw [christoffelCorrection_apply]
  set w : E := trivToE (I := I) α b v
  have h_step1 :
      ‖∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          (((chartModelBasis E).repr w) i *
            ((chartModelBasis E).repr Y) j *
            chartChristoffel (I := I) g α i j k (extChartAt I α b)) •
            (chartModelBasis E) k‖ ≤
        ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          |((chartModelBasis E).repr w) i| *
          |((chartModelBasis E).repr Y) j| *
          |chartChristoffel (I := I) g α i j k (extChartAt I α b)| * Cv := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_mul]
    exact mul_le_mul_of_nonneg_left (chrRiem_basis_vec_norm_le k)
      (mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _)) (abs_nonneg _))
  have h_step2 :
      ∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
        |((chartModelBasis E).repr w) i| *
        |((chartModelBasis E).repr Y) j| *
        |chartChristoffel (I := I) g α i j k (extChartAt I α b)| * Cv ≤
      ∑ i : Fin n, ∑ j : Fin n, ∑ _k : Fin n,
        |((chartModelBasis E).repr w) i| *
        |((chartModelBasis E).repr Y) j| * CΓ * Cv :=
    Finset.sum_le_sum fun i _ =>
      Finset.sum_le_sum fun j _ =>
        Finset.sum_le_sum fun k _ => by
          have h1 := hCΓ_le _ hb_image i j k
          have hCv_nn := chrRiemBasisVecSup_nonneg (E := E)
          have hwi := abs_nonneg (((chartModelBasis E).repr w) i)
          have hYj := abs_nonneg (((chartModelBasis E).repr Y) j)
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h1 (mul_nonneg hwi hYj)) hCv_nn
  have h_step3 :
      ∑ i : Fin n, ∑ j : Fin n, ∑ _k : Fin n,
        |((chartModelBasis E).repr w) i| *
        |((chartModelBasis E).repr Y) j| * CΓ * Cv =
      (n : ℝ) * CΓ * Cv *
        (∑ i : Fin n, |((chartModelBasis E).repr w) i|) *
        (∑ j : Fin n, |((chartModelBasis E).repr Y) j|) := by
    simp_rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    conv_lhs =>
      arg 2; ext i; arg 2; ext j
      rw [show (n : ℝ) * (|((chartModelBasis E).repr w) i| *
        |((chartModelBasis E).repr Y) j| * CΓ * Cv) =
        ((n : ℝ) * CΓ * Cv * |((chartModelBasis E).repr w) i|) *
        |((chartModelBasis E).repr Y) j| from by ring]
    simp_rw [← Finset.mul_sum]
    rw [← Finset.sum_mul, ← Finset.mul_sum]
  have h_w_bound :
      (∑ i : Fin n, |((chartModelBasis E).repr w) i|) ≤ (n : ℝ) * Cc * ‖w‖ := by
    calc ∑ i : Fin n, |((chartModelBasis E).repr w) i|
        ≤ ∑ _i : Fin n, Cc * ‖w‖ :=
          Finset.sum_le_sum fun i _ => chrRiem_repr_coord_abs_le w i
      _ = (n : ℝ) * Cc * ‖w‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  have h_Y_bound :
      (∑ j : Fin n, |((chartModelBasis E).repr Y) j|) ≤ (n : ℝ) * Cc * ‖Y‖ := by
    calc ∑ j : Fin n, |((chartModelBasis E).repr Y) j|
        ≤ ∑ _j : Fin n, Cc * ‖Y‖ :=
          Finset.sum_le_sum fun j _ => chrRiem_repr_coord_abs_le Y j
      _ = (n : ℝ) * Cc * ‖Y‖ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring
  calc ‖∑ i : Fin n, ∑ j : Fin n, ∑ k : Fin n,
          (((chartModelBasis E).repr w) i *
            ((chartModelBasis E).repr Y) j *
            chartChristoffel (I := I) g α i j k (extChartAt I α b)) •
            (chartModelBasis E) k‖
      ≤ (n : ℝ) * CΓ * Cv *
          (∑ i : Fin n, |((chartModelBasis E).repr w) i|) *
          (∑ j : Fin n, |((chartModelBasis E).repr Y) j|) := by
        linarith [h_step1, h_step2, h_step3.le]
    _ ≤ (n : ℝ) * CΓ * Cv * ((n : ℝ) * Cc * ‖w‖) * ((n : ℝ) * Cc * ‖Y‖) := by
        have hCv_nn := chrRiemBasisVecSup_nonneg (E := E)
        have hCc_nn := chrRiemBasisCoordSup_nonneg (E := E)
        have hn_nn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg _
        exact mul_le_mul
          (mul_le_mul_of_nonneg_left h_w_bound
            (mul_nonneg (mul_nonneg hn_nn hCΓ_nn) hCv_nn))
          h_Y_bound
          (Finset.sum_nonneg fun j _ => abs_nonneg _)
          (mul_nonneg (mul_nonneg (mul_nonneg hn_nn hCΓ_nn) hCv_nn)
            (mul_nonneg (mul_nonneg hn_nn hCc_nn) (norm_nonneg _)))
    _ = (n : ℝ) ^ 3 * Cc ^ 2 * Cv * CΓ * ‖Y‖ * ‖w‖ := by ring

private lemma chrRiem_slotConjFactor_self_apply
    (g : SmoothRiemannianMetric I M) (α : M)
    (X : Π b' : M, TangentSpace I b') {b : M}
    (hb : b ∈ (chartAt H α).source) (w : E) :
    (chartJ (I := I) (M := M) α b).comp
        ((chartLeviCivitaParallelCLM (I := I) g α b X).comp
          (chartJinv (I := I) (M := M) α b)) w =
      christoffelCorrection (I := I) g α b
        (trivToE (I := I) α b (X b))
        (trivFromE (I := I) α b w) := by
  classical
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := hb
  rw [ContinuousLinearMap.comp_apply]
  change chartJ (I := I) (M := M) α b
      ((chartLeviCivitaParallelCLM (I := I) g α b X)
        (chartJinv (I := I) (M := M) α b w)) = _
  rw [chartLeviCivitaParallelCLM_apply (I := I) g α b X
    (chartJinv (I := I) (M := M) α b w)]
  change trivToE (I := I) α b
      (trivFromE (I := I) α b
        (christoffelCorrection (I := I) g α b
          (trivToE (I := I) α b (X b))
          (trivFromE (I := I) α b w))) = _
  rw [trivToE_trivFromE (I := I) α hb_base]

private lemma chrRiem_slotConjFactor_basis_norm_le_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ (k : Fin (Module.finrank ℝ E)),
          ‖(chartJ (I := I) (M := M) α b).comp
              ((chartLeviCivitaParallelCLM (I := I) g α b
                  (chartBasisVecFiber (I := I) α k)).comp
                (chartJinv (I := I) (M := M) α b))‖ ≤ C := by
  classical
  obtain ⟨Cχ, hCχ_nn, hCχ_bound⟩ :=
    christoffelCorrection_riem_norm_le_on_pouTsupport (I := I) (M := M) g α
  set Cvec : ℝ :=
    (Finset.univ : Finset (Fin (Module.finrank ℝ E))).sup'
      (Finset.univ_nonempty_iff.mpr ⟨⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩⟩)
      (fun k => ‖(chartModelBasis E) k‖) with hCvec_def
  have hCvec_nn : 0 ≤ Cvec := by
    rw [hCvec_def]
    obtain ⟨k₀, hk₀⟩ :=
      (Finset.univ_nonempty_iff.mpr
        ⟨(⟨0, Nat.pos_of_ne_zero (NeZero.ne _)⟩ : Fin (Module.finrank ℝ E))⟩)
    exact le_trans (norm_nonneg _)
      (Finset.le_sup' (f := fun k => ‖(chartModelBasis E) k‖) hk₀)
  refine ⟨Cχ * Cvec, mul_nonneg hCχ_nn hCvec_nn, ?_⟩
  intro b hb k
  have hb_src : b ∈ (chartAt H α).source :=
    chartAtlasPOU_isSubordinate (I := I) (M := M) α hb
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := hb_src
  have hX_triv :
      trivToE (I := I) α b (chartBasisVecFiber (I := I) α k b) =
        (chartModelBasis E) k := by
    change trivToE (I := I) α b
        (trivFromE (I := I) α b ((chartModelBasis E) k)) = _
    exact trivToE_trivFromE (I := I) α hb_base ((chartModelBasis E) k)
  have h_basis_le : ‖(chartModelBasis E) k‖ ≤ Cvec := by
    rw [hCvec_def]
    exact Finset.le_sup' (f := fun k => ‖(chartModelBasis E) k‖) (Finset.mem_univ k)
  have hpt : ∀ w : E,
      ‖(chartJ (I := I) (M := M) α b).comp
          ((chartLeviCivitaParallelCLM (I := I) g α b
              (chartBasisVecFiber (I := I) α k)).comp
            (chartJinv (I := I) (M := M) α b)) w‖ ≤ Cχ * Cvec * ‖w‖ := by
    intro w
    rw [chrRiem_slotConjFactor_self_apply (I := I) (M := M) g α
      (chartBasisVecFiber (I := I) α k) hb_src w, hX_triv]
    have hround :
        trivToE (I := I) α b (trivFromE (I := I) α b w) = w :=
      trivToE_trivFromE (I := I) α hb_base w
    have hbound := hCχ_bound (b := b) hb ((chartModelBasis E) k)
      (trivFromE (I := I) α b w)
    rw [hround] at hbound
    calc ‖christoffelCorrection (I := I) g α b ((chartModelBasis E) k)
            (trivFromE (I := I) α b w)‖
        ≤ Cχ * ‖(chartModelBasis E) k‖ * ‖w‖ := hbound
      _ ≤ Cχ * Cvec * ‖w‖ :=
          mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left h_basis_le hCχ_nn) (norm_nonneg _)
  exact ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg hCχ_nn hCvec_nn) hpt

private lemma chrRiem_slotInputConjCLM_prod_norm_le_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (r : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ (k : Fin (Module.finrank ℝ E)) (i : Fin r),
          (∏ j : Fin r,
            ‖slotInputConjCLM (I := I) g r α
              (chartBasisVecFiber (I := I) α k) i b j‖) ≤ C := by
  classical
  obtain ⟨C₀, hC₀_nn, hC₀_bound⟩ :=
    chrRiem_slotConjFactor_basis_norm_le_on_pouTsupport (I := I) (M := M) g α
  refine ⟨(max C₀ 1) ^ r,
    pow_nonneg (le_trans zero_le_one (le_max_right _ _)) r, ?_⟩
  intro b hb k i
  have h_factor_le : ∀ j : Fin r,
      ‖slotInputConjCLM (I := I) g r α
        (chartBasisVecFiber (I := I) α k) i b j‖ ≤ max C₀ 1 := by
    intro j
    by_cases hji : j = i
    · subst hji
      rw [slotInputConjCLM_self]
      exact le_trans (hC₀_bound hb k) (le_max_left _ _)
    · rw [slotInputConjCLM_other (I := I) g r α
        (chartBasisVecFiber (I := I) α k) i b hji]
      exact le_trans ContinuousLinearMap.norm_id_le (le_max_right _ _)
  calc (∏ j : Fin r,
        ‖slotInputConjCLM (I := I) g r α
          (chartBasisVecFiber (I := I) α k) i b j‖)
      ≤ ∏ _j : Fin r, max C₀ 1 :=
        Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => h_factor_le j)
    _ = (max C₀ 1) ^ r := by rw [Finset.prod_const]; simp

private lemma chrRiem_slotOutputConjCLM_prod_norm_le_on_pouTsupport
    (g : SmoothRiemannianMetric I M) (s : ℕ) (α : M) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {b : M}, b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ (k : Fin (Module.finrank ℝ E)) (l : Fin s),
          (∏ j : Fin s,
            ‖slotOutputConjCLM (I := I) g s α
              (chartBasisVecFiber (I := I) α k) l b j‖) ≤ C := by
  classical
  obtain ⟨C₀, hC₀_nn, hC₀_bound⟩ :=
    chrRiem_slotConjFactor_basis_norm_le_on_pouTsupport (I := I) (M := M) g α
  refine ⟨(max C₀ 1) ^ s,
    pow_nonneg (le_trans zero_le_one (le_max_right _ _)) s, ?_⟩
  intro b hb k l
  have h_factor_le : ∀ j : Fin s,
      ‖slotOutputConjCLM (I := I) g s α
        (chartBasisVecFiber (I := I) α k) l b j‖ ≤ max C₀ 1 := by
    intro j
    by_cases hjl : j = l
    · subst hjl
      rw [slotOutputConjCLM_self]
      exact le_trans (hC₀_bound hb k) (le_max_left _ _)
    · rw [slotOutputConjCLM_other (I := I) g s α
        (chartBasisVecFiber (I := I) α k) l b hjl]
      exact le_trans ContinuousLinearMap.norm_id_le (le_max_right _ _)
  calc (∏ j : Fin s,
        ‖slotOutputConjCLM (I := I) g s α
          (chartBasisVecFiber (I := I) α k) l b j‖)
      ≤ ∏ _j : Fin s, max C₀ 1 :=
        Finset.prod_le_prod (fun j _ => norm_nonneg _) (fun j _ => h_factor_le j)
    _ = (max C₀ 1) ^ s := by rw [Finset.prod_const]; simp

private lemma chrRiem_inputSlotChartKernel_apply_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (X : Π b' : M, TangentSpace I b') (i : Fin r) (b : M)
    (S : TensorRSModel r s ℝ E) :
    ‖inputSlotChartKernel (I := I) g r s α X i b S‖ ≤
      (∏ j : Fin r, ‖slotInputConjCLM (I := I) g r α X i b j‖) * ‖S‖ := by
  classical
  rw [inputSlotChartKernel_apply]
  calc ‖S.comp (inputSlotPrecompCLM (I := I) g r α X i b)‖
      ≤ ‖S‖ * ‖inputSlotPrecompCLM (I := I) g r α X i b‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ ‖S‖ * (∏ j : Fin r, ‖slotInputConjCLM (I := I) g r α X i b j‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        unfold inputSlotPrecompCLM
        exact ContinuousMultilinearMap.norm_compContinuousLinearMapL_le
          (𝕜 := ℝ) (E := fun _ : Fin r => E) ℝ
          (slotInputConjCLM (I := I) g r α X i b)
    _ = (∏ j : Fin r, ‖slotInputConjCLM (I := I) g r α X i b j‖) * ‖S‖ := by
        ring

private lemma chrRiem_outputSlotChartKernel_apply_norm_le
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (X : Π b' : M, TangentSpace I b') (l : Fin s) (b : M)
    (S : TensorRSModel r s ℝ E) :
    ‖outputSlotChartKernel (I := I) g r s α X l b S‖ ≤
      (∏ j : Fin s, ‖slotOutputConjCLM (I := I) g s α X l b j‖) * ‖S‖ := by
  classical
  rw [outputSlotChartKernel_apply]
  calc ‖(outputSlotPostcompCLM (I := I) g s α X l b).comp S‖
      ≤ ‖outputSlotPostcompCLM (I := I) g s α X l b‖ * ‖S‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ (∏ j : Fin s, ‖slotOutputConjCLM (I := I) g s α X l b j‖) * ‖S‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
        unfold outputSlotPostcompCLM
        exact ContinuousMultilinearMap.norm_compContinuousLinearMapL_le
          (𝕜 := ℝ) (E := fun _ : Fin s => E) ℝ
          (slotOutputConjCLM (I := I) g s α X l b)

private lemma chrRiem_tensorRSTriv_baseSet_eq_chartSource (r s : ℕ) (α : M) :
    (trivializationAt (TensorRSModel r s ℝ E)
        (fun y : M => TensorRSSpace r s I y) α).baseSet =
      (chartAt H α).source := by
  classical
  change (trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).baseSet ∩
      (trivializationAt (Tensor0SModel s ℝ E)
        (fun y : M => Tensor0SSpace s I y) α).baseSet = _
  have h_r : (trivializationAt (Tensor0SModel r ℝ E)
      (fun y : M => Tensor0SSpace r I y) α).baseSet =
        (trivializationAt E (TangentSpace I) α).baseSet := rfl
  have h_s : (trivializationAt (Tensor0SModel s ℝ E)
      (fun y : M => Tensor0SSpace s I y) α).baseSet =
        (trivializationAt E (TangentSpace I) α).baseSet := rfl
  rw [h_r, h_s, Set.inter_self,
    DifferentialGeometry.Integral.Measure.trivializationAt_baseSet_eq_chartAt_source]

set_option synthInstance.maxHeartbeats 800000 in
attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **Riemannian-norm uniform op-norm bound for the input-slot Christoffel
correction (HLCC-free).** On the chart-`α` partition-of-unity `tsupport`, the
Riemannian fibre norm of the input-slot Christoffel correction along the
chart-frame basis vector field is bounded by a constant times the Riemannian
fibre norm of the section value, uniformly in the section, the basis direction
`k`, the slot `i`, and the base point `b`. -/
theorem chartTensorRSInputSlotCorrection_riemannian_norm_le_on_pouTsupport_local
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ∃ M_F : ℝ, 0 ≤ M_F ∧
      ∀ (T : Π b' : M, TensorRSSpace r s I b') {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ (k : Fin (Module.finrank ℝ E)) (i : Fin r),
          ‖chartTensorRSInputSlotCorrection (I := I) r s g α T
              (chartBasisVecFiber (I := I) α k) b i‖ ≤
            M_F * ‖T b‖ := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  have hK_cpt : IsCompact (tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
    pouTsupport_isCompact (I := I) (M := M) α
  have hK_sub : tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆ (chartAt H α).source := by
    intro x hx; exact chartAtlasPOU_isSubordinate (I := I) (M := M) α hx
  obtain ⟨Cto, hCto_pos, hCto_bound⟩ :=
    tensorRSChartFiberToModel_opNorm_isBounded_on_compact_unconditional
      (I := I) (M := M) g r s α hK_cpt hK_sub
  obtain ⟨Cfrom, hCfrom_pos, hCfrom_bound⟩ :=
    tensorRSChartFiberFromModel_opNorm_isBounded_on_compact_unconditional
      (I := I) (M := M) g r s α hK_cpt hK_sub
  obtain ⟨Cprod, hCprod_nn, hCprod_bound⟩ :=
    chrRiem_slotInputConjCLM_prod_norm_le_on_pouTsupport (I := I) (M := M) g r α
  refine ⟨Cfrom * Cprod * Cto,
    mul_nonneg (mul_nonneg (le_of_lt hCfrom_pos) hCprod_nn) (le_of_lt hCto_pos), ?_⟩
  intro T b hb k i
  set Y : TensorRSSpace r s I b :=
    chartTensorRSInputSlotCorrection (I := I) r s g α T
      (chartBasisVecFiber (I := I) α k) b i with hY_def
  have hb_base : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    rw [chrRiem_tensorRSTriv_baseSet_eq_chartSource (I := I) (M := M) r s α]
    exact hK_sub hb
  have h_roundtrip :
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).symmL ℝ b
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y) = Y :=
    Trivialization.symmL_continuousLinearMapAt _ hb_base Y
  have h_from :
      ‖Y‖ ≤ Cfrom * ‖(trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y‖ := by
    have := hCfrom_bound b hb
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y)
    rwa [h_roundtrip] at this
  have h_fact :
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y =
        (inputSlotChartKernel (I := I) g r s α
            (chartBasisVecFiber (I := I) α k) i b)
          ((trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (T b)) :=
    chartTensorRSInputSlotCorrection_chart_kernel_factorization
      (I := I) (M := M) g r s α T (chartBasisVecFiber (I := I) α k)
      (hK_sub hb) i
  have h_kernel :
      ‖(trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y‖ ≤
        Cprod * ‖(trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b (T b)‖ := by
    rw [h_fact]
    refine le_trans (chrRiem_inputSlotChartKernel_apply_norm_le (I := I) (M := M)
      g r s α (chartBasisVecFiber (I := I) α k) i b _) ?_
    exact mul_le_mul_of_nonneg_right (hCprod_bound hb k i) (norm_nonneg _)
  have h_to :
      ‖(trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b (T b)‖ ≤
        Cto * ‖T b‖ :=
    hCto_bound b hb (T b)
  have hCto_nn : 0 ≤ Cto := le_of_lt hCto_pos
  have hCfrom_nn : 0 ≤ Cfrom := le_of_lt hCfrom_pos
  calc ‖Y‖
      ≤ Cfrom * ‖(trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y‖ := h_from
    _ ≤ Cfrom * (Cprod * ‖(trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b (T b)‖) :=
        mul_le_mul_of_nonneg_left h_kernel hCfrom_nn
    _ ≤ Cfrom * (Cprod * (Cto * ‖T b‖)) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h_to hCprod_nn) hCfrom_nn
    _ = Cfrom * Cprod * Cto * ‖T b‖ := by ring

set_option synthInstance.maxHeartbeats 800000 in
attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **Riemannian-norm uniform op-norm bound for the output-slot Christoffel
correction (HLCC-free).** Output twin of
`chartTensorRSInputSlotCorrection_riemannian_norm_le_on_pouTsupport_local`. -/
theorem chartTensorRSOutputSlotCorrection_riemannian_norm_le_on_pouTsupport_local
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ∃ M_F : ℝ, 0 ≤ M_F ∧
      ∀ (T : Π b' : M, TensorRSSpace r s I b') {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ (k : Fin (Module.finrank ℝ E)) (l : Fin s),
          ‖chartTensorRSOutputSlotCorrection (I := I) r s g α T
              (chartBasisVecFiber (I := I) α k) b l‖ ≤
            M_F * ‖T b‖ := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  have hK_cpt : IsCompact (tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)) :=
    pouTsupport_isCompact (I := I) (M := M) α
  have hK_sub : tsupport (fun x : M =>
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) ⊆ (chartAt H α).source := by
    intro x hx; exact chartAtlasPOU_isSubordinate (I := I) (M := M) α hx
  obtain ⟨Cto, hCto_pos, hCto_bound⟩ :=
    tensorRSChartFiberToModel_opNorm_isBounded_on_compact_unconditional
      (I := I) (M := M) g r s α hK_cpt hK_sub
  obtain ⟨Cfrom, hCfrom_pos, hCfrom_bound⟩ :=
    tensorRSChartFiberFromModel_opNorm_isBounded_on_compact_unconditional
      (I := I) (M := M) g r s α hK_cpt hK_sub
  obtain ⟨Cprod, hCprod_nn, hCprod_bound⟩ :=
    chrRiem_slotOutputConjCLM_prod_norm_le_on_pouTsupport (I := I) (M := M) g s α
  refine ⟨Cfrom * Cprod * Cto,
    mul_nonneg (mul_nonneg (le_of_lt hCfrom_pos) hCprod_nn) (le_of_lt hCto_pos), ?_⟩
  intro T b hb k l
  set Y : TensorRSSpace r s I b :=
    chartTensorRSOutputSlotCorrection (I := I) r s g α T
      (chartBasisVecFiber (I := I) α k) b l with hY_def
  have hb_base : b ∈ (trivializationAt (TensorRSModel r s ℝ E)
      (fun y : M => TensorRSSpace r s I y) α).baseSet := by
    rw [chrRiem_tensorRSTriv_baseSet_eq_chartSource (I := I) (M := M) r s α]
    exact hK_sub hb
  have h_roundtrip :
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).symmL ℝ b
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y) = Y :=
    Trivialization.symmL_continuousLinearMapAt _ hb_base Y
  have h_from :
      ‖Y‖ ≤ Cfrom * ‖(trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y‖ := by
    have := hCfrom_bound b hb
      ((trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y)
    rwa [h_roundtrip] at this
  have h_fact :
      (trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y =
        (outputSlotChartKernel (I := I) g r s α
            (chartBasisVecFiber (I := I) α k) l b)
          ((trivializationAt (TensorRSModel r s ℝ E)
              (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b
            (T b)) :=
    chartTensorRSOutputSlotCorrection_chart_kernel_factorization
      (I := I) (M := M) g r s α T (chartBasisVecFiber (I := I) α k)
      (hK_sub hb) l
  have h_kernel :
      ‖(trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y‖ ≤
        Cprod * ‖(trivializationAt (TensorRSModel r s ℝ E)
            (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b (T b)‖ := by
    rw [h_fact]
    refine le_trans (chrRiem_outputSlotChartKernel_apply_norm_le (I := I) (M := M)
      g r s α (chartBasisVecFiber (I := I) α k) l b _) ?_
    exact mul_le_mul_of_nonneg_right (hCprod_bound hb k l) (norm_nonneg _)
  have h_to :
      ‖(trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b (T b)‖ ≤
        Cto * ‖T b‖ :=
    hCto_bound b hb (T b)
  have hCto_nn : 0 ≤ Cto := le_of_lt hCto_pos
  have hCfrom_nn : 0 ≤ Cfrom := le_of_lt hCfrom_pos
  calc ‖Y‖
      ≤ Cfrom * ‖(trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b Y‖ := h_from
    _ ≤ Cfrom * (Cprod * ‖(trivializationAt (TensorRSModel r s ℝ E)
          (fun y : M => TensorRSSpace r s I y) α).continuousLinearMapAt ℝ b (T b)‖) :=
        mul_le_mul_of_nonneg_left h_kernel hCfrom_nn
    _ ≤ Cfrom * (Cprod * (Cto * ‖T b‖)) := by
        refine mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left h_to hCprod_nn) hCfrom_nn
    _ = Cfrom * Cprod * Cto * ‖T b‖ := by ring

set_option synthInstance.maxHeartbeats 800000 in
attribute [-instance] Bundle.continuousMultilinearMap.instNormedAddCommGroup
  Bundle.continuousMultilinearMap.instNormedSpace
  Tensor0SBundle.tensorRSSpace_normedAddCommGroup
  Tensor0SBundle.tensorRSSpace_normedSpace in
/-- **Unconditional Riemannian-fibre-norm Christoffel slot-correction atom `L²`
bound.** The per-`α` per-direction
`L²` norm of the partition-of-unity-weighted square-root of the Euclidean sum of
squared **Riemannian fibre norms** of the chart-frame input / output slot
Christoffel corrections is bounded by `ENNReal.ofReal C · ‖S‖₊`, with `C`
depending only on `(g, r, s, α, j)`. -/
theorem exists_eLpNorm_sq_pou_mul_sqrt_sum_christoffel_correction_le_const_mul_h1NormSq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (j : Fin (Module.finrank ℝ E)) :
    letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
      Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (S : SmoothCcTensorH1 g r s),
        eLpNorm
            (fun b : M =>
              ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
                Real.sqrt
                  ((∑ k : Fin r,
                      ‖chartTensorRSInputSlotCorrection (I := I) r s g α
                          (fun b' => S.toCcTensor.toSection b')
                          (chartBasisVecFiber (I := I) α j) b k‖ ^ 2) +
                    (∑ l : Fin s,
                      ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
                          (fun b' => S.toCcTensor.toSection b')
                          (chartBasisVecFiber (I := I) α j) b l‖ ^ 2)))
            2 (riemannianVolumeMeasure (I := I) (M := M) g) ≤
          ENNReal.ofReal C * (‖S‖₊ : ℝ≥0∞) := by
  classical
  letI : Bundle.RiemannianBundle (fun b : M => TensorRSSpace r s I b) :=
    Tensor0SBundle.tensorRS_riemannianBundle (I := I) (M := M) g r s
  obtain ⟨M_F_in, hM_F_in_nn, hM_F_in_le⟩ :=
    chartTensorRSInputSlotCorrection_riemannian_norm_le_on_pouTsupport_local
      (I := I) (M := M) g r s α
  obtain ⟨M_F_out, hM_F_out_nn, hM_F_out_le⟩ :=
    chartTensorRSOutputSlotCorrection_riemannian_norm_le_on_pouTsupport_local
      (I := I) (M := M) g r s α
  set M_F : ℝ := max M_F_in M_F_out with hM_F_def
  have hM_F_nn : 0 ≤ M_F := le_max_of_le_left hM_F_in_nn
  have hM_F_input :
      ∀ (S : SmoothCcTensor g r s) {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ k : Fin r,
          ‖chartTensorRSInputSlotCorrection (I := I) r s g α
              (fun b' => S.toSection b') (chartBasisVecFiber (I := I) α j) b k‖ ≤
            M_F * ‖S.toSection b‖ := by
    intro S b hb k
    have h_orig := hM_F_in_le (fun b' => S.toSection b') (b := b) hb j k
    exact h_orig.trans
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _))
  have hM_F_output :
      ∀ (S : SmoothCcTensor g r s) {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ∀ l : Fin s,
          ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
              (fun b' => S.toSection b') (chartBasisVecFiber (I := I) α j) b l‖ ≤
            M_F * ‖S.toSection b‖ := by
    intro S b hb l
    have h_orig := hM_F_out_le (fun b' => S.toSection b') (b := b) hb j l
    exact h_orig.trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  have hK_S_bound :
      ∀ (S : SmoothCcTensor g r s) {b : M},
        b ∈ tsupport (fun x : M =>
            ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
        ‖S.toSection b‖ ^ 2 ≤
          (1 : ℝ) * tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toFun b) (S.toFun b) := by
    intro S b _hb
    rw [one_mul]
    have h_inner : (⟪S.toSection b, S.toSection b⟫_ℝ : ℝ) =
        tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toFun b) (S.toFun b) := by
      change DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM
          (I := I) (M := M) g r s b (S.toSection b) (S.toSection b) = _
      rw [DifferentialGeometry.Tensor.TensorRSRiemannianBundle.tensorRSRiemannianInnerCLM_apply]
      rfl
    rw [← h_inner, real_inner_self_eq_norm_sq]
  set C : ℝ := ((r : ℝ) + (s : ℝ)) * M_F ^ 2 with hC_def
  have hC_nn : 0 ≤ C := by rw [hC_def]; positivity
  have h_pt : ∀ (T : SmoothCcTensor g r s) {b : M},
      b ∈ tsupport (fun x : M =>
          ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x) →
      ((∑ k : Fin r, ‖chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun b' => T.toSection b') (chartBasisVecFiber (I := I) α j) b k‖ ^ 2) +
        (∑ l : Fin s, ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun b' => T.toSection b') (chartBasisVecFiber (I := I) α j) b l‖ ^ 2)) ≤
        C * tensorInnerPointwise (I := I) (M := M) g r s b
          (T.toFun b) (T.toFun b) := by
    intro T b hb
    have h_sec : ‖T.toSection b‖ ^ 2 ≤
        (1 : ℝ) * tensorInnerPointwise (I := I) (M := M) g r s b
          (T.toFun b) (T.toFun b) := hK_S_bound T hb
    have h_in_each : ∀ k : Fin r,
        ‖chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun b' => T.toSection b') (chartBasisVecFiber (I := I) α j) b k‖ ^ 2 ≤
          M_F ^ 2 * ‖T.toSection b‖ ^ 2 := by
      intro k
      have hbnd := hM_F_input T hb k
      have hLHS_nn : 0 ≤ ‖chartTensorRSInputSlotCorrection (I := I) r s g α
          (fun b' => T.toSection b') (chartBasisVecFiber (I := I) α j) b k‖ :=
        norm_nonneg _
      have := mul_self_le_mul_self hLHS_nn hbnd
      nlinarith [this, sq_nonneg M_F, norm_nonneg (T.toSection b)]
    have h_out_each : ∀ l : Fin s,
        ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun b' => T.toSection b') (chartBasisVecFiber (I := I) α j) b l‖ ^ 2 ≤
          M_F ^ 2 * ‖T.toSection b‖ ^ 2 := by
      intro l
      have hbnd := hM_F_output T hb l
      have hLHS_nn : 0 ≤ ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
          (fun b' => T.toSection b') (chartBasisVecFiber (I := I) α j) b l‖ :=
        norm_nonneg _
      have := mul_self_le_mul_self hLHS_nn hbnd
      nlinarith [this, sq_nonneg M_F, norm_nonneg (T.toSection b)]
    have h_in_sum : (∑ k : Fin r,
          ‖chartTensorRSInputSlotCorrection (I := I) r s g α
              (fun b' => T.toSection b') (chartBasisVecFiber (I := I) α j) b k‖ ^ 2) ≤
        (r : ℝ) * (M_F ^ 2 * ‖T.toSection b‖ ^ 2) := by
      have h_le := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin r)))
        (fun k _ => h_in_each k)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h_le
      exact h_le
    have h_out_sum : (∑ l : Fin s,
          ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
              (fun b' => T.toSection b') (chartBasisVecFiber (I := I) α j) b l‖ ^ 2) ≤
        (s : ℝ) * (M_F ^ 2 * ‖T.toSection b‖ ^ 2) := by
      have h_le := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin s)))
        (fun l _ => h_out_each l)
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h_le
      exact h_le
    have hQ_nn : 0 ≤ tensorInnerPointwise (I := I) (M := M) g r s b
        (T.toFun b) (T.toFun b) :=
      tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _
    have h_secSq : ‖T.toSection b‖ ^ 2 ≤
        tensorInnerPointwise (I := I) (M := M) g r s b (T.toFun b) (T.toFun b) := by
      rw [one_mul] at h_sec; exact h_sec
    have h_MF_sq_nn : 0 ≤ M_F ^ 2 := sq_nonneg _
    have h_rs_nn : 0 ≤ (r : ℝ) + (s : ℝ) := by positivity
    calc (∑ k : Fin r,
            ‖chartTensorRSInputSlotCorrection (I := I) r s g α
                (fun b' => T.toSection b') (chartBasisVecFiber (I := I) α j) b k‖ ^ 2) +
          (∑ l : Fin s,
            ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
                (fun b' => T.toSection b') (chartBasisVecFiber (I := I) α j) b l‖ ^ 2)
        ≤ (r : ℝ) * (M_F ^ 2 * ‖T.toSection b‖ ^ 2) +
            (s : ℝ) * (M_F ^ 2 * ‖T.toSection b‖ ^ 2) :=
          add_le_add h_in_sum h_out_sum
      _ = ((r : ℝ) + (s : ℝ)) * M_F ^ 2 * ‖T.toSection b‖ ^ 2 := by ring
      _ ≤ ((r : ℝ) + (s : ℝ)) * M_F ^ 2 *
            tensorInnerPointwise (I := I) (M := M) g r s b (T.toFun b) (T.toFun b) :=
          mul_le_mul_of_nonneg_left h_secSq
            (mul_nonneg h_rs_nn h_MF_sq_nn)
      _ = C * tensorInnerPointwise (I := I) (M := M) g r s b
            (T.toFun b) (T.toFun b) := by rw [hC_def]
  refine ⟨Real.sqrt C, Real.sqrt_nonneg _, ?_⟩
  intro S
  set ρ : M → ℝ := fun x : M =>
    ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x with hρ_def
  set SumSq : M → ℝ := fun b : M =>
    (∑ k : Fin r,
        ‖chartTensorRSInputSlotCorrection (I := I) r s g α
            (fun b' => S.toCcTensor.toSection b')
            (chartBasisVecFiber (I := I) α j) b k‖ ^ 2) +
      (∑ l : Fin s,
        ‖chartTensorRSOutputSlotCorrection (I := I) r s g α
            (fun b' => S.toCcTensor.toSection b')
            (chartBasisVecFiber (I := I) α j) b l‖ ^ 2) with hSumSq_def
  set f : M → ℝ := fun b : M => ρ b * Real.sqrt (SumSq b) with hf_def
  set μ : Measure M := riemannianVolumeMeasure (I := I) (M := M) g with hμ_def
  have hSumSq_nn : ∀ b : M, 0 ≤ SumSq b := by
    intro b
    rw [hSumSq_def]
    exact add_nonneg
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
      (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  have h_pt_sq : ∀ b : M, (f b) ^ 2 ≤
      C * tensorInnerPointwise (I := I) (M := M) g r s b
        (S.toCcTensor.toFun b) (S.toCcTensor.toFun b) := by
    intro b
    by_cases hb : b ∈ tsupport (fun x : M =>
        ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) x)
    · have h_eq : (f b) ^ 2 = ρ b ^ 2 * SumSq b := by
        rw [hf_def, mul_pow,
          show Real.sqrt (SumSq b) ^ 2 = SumSq b from Real.sq_sqrt (hSumSq_nn b)]
      have h_rho_le_one : ρ b ≤ 1 := by
        rw [hρ_def]; exact (chartAtlasPOU I M).le_one α b
      have h_rho_nn : 0 ≤ ρ b := by rw [hρ_def]; exact (chartAtlasPOU I M).nonneg α b
      have h_rho_sq_le_one : ρ b ^ 2 ≤ 1 := by
        rw [sq]
        calc ρ b * ρ b ≤ 1 * 1 :=
              mul_le_mul h_rho_le_one h_rho_le_one h_rho_nn zero_le_one
          _ = 1 := by ring
      have h_sum_le : SumSq b ≤ C * tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toCcTensor.toFun b) (S.toCcTensor.toFun b) := h_pt S.toCcTensor hb
      rw [h_eq]
      calc ρ b ^ 2 * SumSq b
          ≤ 1 * SumSq b :=
            mul_le_mul_of_nonneg_right h_rho_sq_le_one (hSumSq_nn b)
        _ = SumSq b := by ring
        _ ≤ C * tensorInnerPointwise (I := I) (M := M) g r s b
              (S.toCcTensor.toFun b) (S.toCcTensor.toFun b) := h_sum_le
    · have h_rho_zero : ρ b = 0 := by
        rw [hρ_def]; by_contra hne; exact hb (subset_tsupport _ hne)
      have hzero : (f b) ^ 2 = 0 := by
        change (ρ b * Real.sqrt (SumSq b)) ^ 2 = 0
        rw [h_rho_zero]; ring
      rw [hzero]
      exact mul_nonneg hC_nn
        (tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _)
  have h_pt_enn : ∀ b : M,
      (‖f b‖ₑ : ℝ≥0∞) ^ 2 ≤
        ENNReal.ofReal (C * tensorInnerPointwise
          (I := I) (M := M) g r s b
            (S.toCcTensor.toFun b) (S.toCcTensor.toFun b)) := by
    intro b
    rw [show (‖f b‖ₑ : ℝ≥0∞) ^ 2 = ENNReal.ofReal ((f b) ^ 2) by
      rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _) 2,
        sq_abs]]
    exact ENNReal.ofReal_le_ofReal (h_pt_sq b)
  have h_inner_int :
      Integrable (fun b : M => tensorInnerPointwise
        (I := I) (M := M) g r s b
          (S.toCcTensor.toFun b) (S.toCcTensor.toFun b)) μ :=
    SmoothCcTensor.integrable_inner_cross (I := I) (M := M)
      S.toCcTensor S.toCcTensor
  have h_C_smul_int :
      Integrable (fun b : M => C *
        tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toCcTensor.toFun b) (S.toCcTensor.toFun b)) μ :=
    h_inner_int.const_mul C
  have h_C_smul_nn :
      0 ≤ᵐ[μ] (fun b : M => C *
        tensorInnerPointwise (I := I) (M := M) g r s b
          (S.toCcTensor.toFun b) (S.toCcTensor.toFun b)) :=
    Filter.Eventually.of_forall fun b => mul_nonneg hC_nn
      (tensorInnerPointwise_nonneg (I := I) (M := M) g r s b _)
  have h_int_le :
      ∫ b, tensorInnerPointwise
        (I := I) (M := M) g r s b
          (S.toCcTensor.toFun b) (S.toCcTensor.toFun b) ∂μ ≤
      ‖S‖ ^ 2 := by
    have h_l2_eq : ∫ b, tensorInnerPointwise
        (I := I) (M := M) g r s b
          (S.toCcTensor.toFun b) (S.toCcTensor.toFun b) ∂μ =
        ‖S.toCcTensor‖ ^ 2 := by
      rw [hμ_def]
      have h_eq : ∫ b,
          tensorInnerPointwise (I := I) (M := M) g r s b
            (S.toCcTensor.toFun b) (S.toCcTensor.toFun b)
          ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
        tensorL2Inner (I := I) (M := M) g r s
          S.toCcTensor.toFun S.toCcTensor.toFun := rfl
      rw [h_eq, ← SmoothCcTensor.norm_sq_eq_inner_self
        (I := I) (M := M) S.toCcTensor]
    rw [h_l2_eq]
    exact SmoothCcTensorH1.l2NormSq_le_h1NormSq S
  have h_sq : (eLpNorm f 2 μ) ^ 2 ≤ ENNReal.ofReal (C * ‖S‖ ^ 2) := by
    rw [sq_eLpNorm_two_eq_lintegral_enorm_sq μ f]
    calc ∫⁻ b, (‖f b‖ₑ : ℝ≥0∞) ^ 2 ∂μ
        ≤ ∫⁻ b, ENNReal.ofReal (C * tensorInnerPointwise
            (I := I) (M := M) g r s b
              (S.toCcTensor.toFun b) (S.toCcTensor.toFun b)) ∂μ := by
          refine lintegral_mono_ae ?_
          filter_upwards with b using h_pt_enn b
      _ = ENNReal.ofReal (∫ b, C * tensorInnerPointwise
            (I := I) (M := M) g r s b
              (S.toCcTensor.toFun b) (S.toCcTensor.toFun b) ∂μ) :=
          (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
            h_C_smul_int h_C_smul_nn).symm
      _ = ENNReal.ofReal (C *
            ∫ b, tensorInnerPointwise
              (I := I) (M := M) g r s b
                (S.toCcTensor.toFun b) (S.toCcTensor.toFun b) ∂μ) := by
          rw [integral_const_mul]
      _ ≤ ENNReal.ofReal (C * ‖S‖ ^ 2) :=
          ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left h_int_le hC_nn)
  set Tval : ℝ := C * ‖S‖ ^ 2 with hT_def
  have hT_nn : 0 ≤ Tval := mul_nonneg hC_nn (sq_nonneg _)
  have h_eLpNorm_le := eLpNorm_two_le_ofReal_sqrt hT_nn h_sq
  have hS_nn : 0 ≤ ‖S‖ := norm_nonneg _
  have h_sqrt_factor :
      Real.sqrt Tval = Real.sqrt C * ‖S‖ := by
    rw [hT_def, Real.sqrt_mul hC_nn,
      show ‖S‖ ^ 2 = ‖S‖ * ‖S‖ from by ring,
      Real.sqrt_mul_self hS_nn]
  rw [h_sqrt_factor,
    ENNReal.ofReal_mul (Real.sqrt_nonneg _)] at h_eLpNorm_le
  rw [show ENNReal.ofReal ‖S‖ = (‖S‖₊ : ℝ≥0∞) from
    (coe_nnnorm_eq_ofReal_norm S).symm] at h_eLpNorm_le
  exact h_eLpNorm_le

end ChristoffelAtomsRiemannian

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
