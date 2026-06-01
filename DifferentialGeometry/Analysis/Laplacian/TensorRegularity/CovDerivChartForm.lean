import DifferentialGeometry.Analysis.Laplacian.TensorRegularity.CovDerivComponentFormula
import DifferentialGeometry.Integral.Connection.ChartTensorRSCovariantDerivativeAgreement
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.TrivProj.Bridge
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.ChartTensor.InnerBridge
import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.PreHilbert

/-!
# Chart-coordinate principal part of the tensor `H^1` Dirichlet integrand

For a smooth, compactly-supported `(r, s)`-tensor section `S`, `T` over a closed
Riemannian manifold `(M, g)` and a chart center `α : M`, the pointwise integrand
of the `H^1` Dirichlet form

```
tensorCovDerivPointwiseInner g r s S T = ⟨∇S, ∇T⟩
```

decomposes, in chart-Euclidean coordinates, into a (component-coupled)
**principal part** plus a **lower-order remainder**. This file builds the
principal part.

The covariant-derivative chart-component formula
(`covDerivComponent_eq_euclidPartial_add_lowerOrder`) expresses the raw
chart-scalar component of the chart-coordinate covariant derivative as a plain
chart-Euclidean partial derivative `euclidPartial` plus a zeroth-order
Christoffel correction `covDerivLowerOrderTerm`. The integrand
`tensorCovDerivPointwiseInner` is, on the chart base set, the chart-`α`-frame
trace expression `chartTensorCovDerivPointwiseInner` (`PreHilbert.lean`); each
chart-frame tensor-metric pairing of two covariant-derivative values expands —
via the bridge `chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise` and
the chart-frame basis decomposition `tensorRSModel_eq_sum_basis` — into a finite
component-coupled sum, with the chart-frame tensor-metric Gram
`covChartMetricGram` coupling component pairs.

Substituting the component formula and separating the four product groups
`(∂S · ∂T)`, `(∂S · LO_T)`, `(LO_S · ∂T)`, `(LO_S · LO_T)`, the first group is
the principal part `covPrincipalIntegrand` and the remaining three are the
lower-order remainder (built in the companion file).

The principal part is **component-coupled**: the chart-frame tensor metric
`covChartMetricGram` is not diagonal. The honest headline is the coupled
identity `tensorCovDerivPointwiseInner_chart_eq`.

## Main definitions

* `covChartMetricGram g r s α P Q` — the chart-frame tensor-metric Gram on
  component multi-index pairs `P, Q`, a `C^∞` function on the Euclidean chart
  target.
* `covPrincipalIntegrand g r s S T α` — the component-coupled principal part of
  the chart-coordinate Dirichlet integrand: the `euclidPartial · euclidPartial`
  group, weighted by `covChartMetricGram` and the un-weighted inverse Gram
  `chartInvGramEuclid`.

## Main results

* `covChartMetricGram_symm` — symmetry of the chart-frame tensor-metric Gram.
* `covChartMetricGram_contDiffOn` — the chart-frame tensor-metric Gram is `C^∞`
  on the Euclidean chart target.
* `tensorCovDerivPointwiseInner_chart_eq` — the headline coupled identity: the
  chart-coordinate Dirichlet integrand is `covPrincipalIntegrand` plus the
  lower-order remainder `covLowerOrderIntegrand` (the latter defined in the
  companion file).
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 800000
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open Bundle Manifold Set Filter
open scoped Manifold Topology ContDiff BigOperators
open Tensor0SBundle

namespace DifferentialGeometry
namespace Analysis
namespace Laplacian
namespace TensorRegularity

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Parabolic.TensorSpectral
open DifferentialGeometry.Analysis.Sobolev.Chart

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

/-- The chart-frame tensor-metric Gram on component multi-index pairs `P, Q`:
the chart-`α`-frame `(r, s)`-inner product of the chart-frame basis elements
indexed by `P` and `Q`, viewed as a function on the Euclidean chart target. -/
noncomputable def covChartMetricGram
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P Q : (Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E))) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α
      ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
      (tensorChartBasisElement (E := E) r s P.1 P.2)
      (tensorChartBasisElement (E := E) r s Q.1 Q.2)

/-- Unfolding lemma for `covChartMetricGram`. -/
lemma covChartMetricGram_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P Q : (Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E)))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    covChartMetricGram (I := I) (M := M) g r s α P Q y =
      chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (tensorChartBasisElement (E := E) r s P.1 P.2)
        (tensorChartBasisElement (E := E) r s Q.1 Q.2) := rfl

/-- **Symmetry of the chart-frame tensor-metric Gram.** Swapping the two
component multi-index pairs leaves the chart-frame tensor-metric Gram unchanged
— a consequence of the symmetry of `chartTensorInnerPointwise_rs_model`. -/
theorem covChartMetricGram_symm
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P Q : (Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E)))
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    covChartMetricGram (I := I) (M := M) g r s α P Q y =
      covChartMetricGram (I := I) (M := M) g r s α Q P y := by
  rw [covChartMetricGram_def, covChartMetricGram_def]
  exact chartTensorInnerPointwise_rs_model_symm (I := I) (M := M) g r s α
    ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
    (tensorChartBasisElement (E := E) r s P.1 P.2)
    (tensorChartBasisElement (E := E) r s Q.1 Q.2)

/-- `(extChartAt I α).symm` maps the chart target into the chart-`α` base set
(the chart source). -/
private lemma extChartAt_symm_mapsTo_baseSet (α : M) :
    Set.MapsTo (extChartAt I α).symm (extChartAt I α).target
      (trivializationAt E (TangentSpace I) α).baseSet := by
  intro y hy
  rw [TangentBundle.trivializationAt_baseSet]
  have hsrc : (extChartAt I α).symm y ∈ (extChartAt I α).source :=
    (extChartAt I α).map_target hy
  rwa [extChartAt_source] at hsrc

/-- **The chart-frame tensor-metric Gram is `C^∞` on the Euclidean chart
target.** Transport of the chart-base-set smoothness of
`chartTensorInnerPointwise_rs_model` through `(extChartAt I α).symm` and the
linear isometry `toEuclidean.symm`. -/
theorem covChartMetricGram_contDiffOn
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (P Q : (Fin r → Fin (Module.finrank ℝ E)) ×
      (Fin s → Fin (Module.finrank ℝ E))) :
    ContDiffOn ℝ ∞ (covChartMetricGram (I := I) (M := M) g r s α P Q)
      (chartTargetEuclid (I := I) (M := M) α) := by
  classical
  have hbase : ContMDiffOn I 𝓘(ℝ) ∞
      (fun b : M =>
        chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b
          (tensorChartBasisElement (E := E) r s P.1 P.2)
          (tensorChartBasisElement (E := E) r s Q.1 Q.2))
      (trivializationAt E (TangentSpace I) α).baseSet :=
    chartTensorInnerPointwise_rs_model_contMDiffOn (I := I) (M := M) g r s α
      (tensorChartBasisElement (E := E) r s P.1 P.2)
      (tensorChartBasisElement (E := E) r s Q.1 Q.2)
  have hsymm : ContMDiffOn 𝓘(ℝ, E) I ∞ (extChartAt I α).symm
      (extChartAt I α).target := contMDiffOn_extChartAt_symm (I := I) α
  have hcomp_E : ContMDiffOn 𝓘(ℝ, E) 𝓘(ℝ) ∞
      ((fun b : M =>
          chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b
            (tensorChartBasisElement (E := E) r s P.1 P.2)
            (tensorChartBasisElement (E := E) r s Q.1 Q.2)) ∘
        (extChartAt I α).symm)
      (extChartAt I α).target :=
    hbase.comp hsymm (extChartAt_symm_mapsTo_baseSet (I := I) (M := M) α)
  have hcontDiff_E : ContDiffOn ℝ ∞
      ((fun b : M =>
          chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b
            (tensorChartBasisElement (E := E) r s P.1 P.2)
            (tensorChartBasisElement (E := E) r s Q.1 Q.2)) ∘
        (extChartAt I α).symm)
      (extChartAt I α).target :=
    hcomp_E.contDiffOn
  have hcomp_eucl : ContDiffOn ℝ ∞
      (((fun b : M =>
            chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b
              (tensorChartBasisElement (E := E) r s P.1 P.2)
              (tensorChartBasisElement (E := E) r s Q.1 Q.2)) ∘
          (extChartAt I α).symm) ∘
        (toEuclidean.symm :
          EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → E))
      (chartTargetEuclid (I := I) (M := M) α) := by
    refine hcontDiff_E.comp ?_ ?_
    · exact (toEuclidean (E := E)).symm.contDiff.contDiffOn
    · intro y hy
      rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
      exact hy
  exact hcomp_eucl

/-- The chart-frame `(r, s)`-inner product expands as a finite component-coupled
sum against the chart-frame component projections and the chart-frame
tensor-metric Gram on the chart-frame basis. -/
private lemma chartTensorInnerPointwise_rs_model_eq_component_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α b : M)
    (X Y : TensorRSModel r s ℝ E) :
    chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b X Y =
      ∑ P : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        ∑ Q : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b
              (tensorChartBasisElement (E := E) r s P.1 P.2)
              (tensorChartBasisElement (E := E) r s Q.1 Q.2) *
            (tensorChartComponentProjection (E := E) r s P.1 P.2 X *
              tensorChartComponentProjection (E := E) r s Q.1 Q.2 Y) := by
  classical
  have hX : X = ∑ P : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      tensorChartComponentProjection (E := E) r s P.1 P.2 X •
        tensorChartBasisElement (E := E) r s P.1 P.2 := by
    rw [Fintype.sum_prod_type
      (f := fun P : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)) =>
        tensorChartComponentProjection (E := E) r s P.1 P.2 X •
          tensorChartBasisElement (E := E) r s P.1 P.2)]
    exact tensorRSModel_eq_sum_basis (E := E) r s X
  have hY : Y = ∑ Q : (Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)),
      tensorChartComponentProjection (E := E) r s Q.1 Q.2 Y •
        tensorChartBasisElement (E := E) r s Q.1 Q.2 := by
    rw [Fintype.sum_prod_type
      (f := fun Q : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)) =>
        tensorChartComponentProjection (E := E) r s Q.1 Q.2 Y •
          tensorChartBasisElement (E := E) r s Q.1 Q.2)]
    exact tensorRSModel_eq_sum_basis (E := E) r s Y
  conv_lhs => rw [hX]
  rw [show chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b
        (∑ P : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          tensorChartComponentProjection (E := E) r s P.1 P.2 X •
            tensorChartBasisElement (E := E) r s P.1 P.2) Y =
      ∑ P : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        tensorChartComponentProjection (E := E) r s P.1 P.2 X *
          chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b
            (tensorChartBasisElement (E := E) r s P.1 P.2) Y from ?_]
  · refine Finset.sum_congr rfl (fun P _ => ?_)
    rw [show chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b
          (tensorChartBasisElement (E := E) r s P.1 P.2) Y =
        chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b
          (tensorChartBasisElement (E := E) r s P.1 P.2)
          (∑ Q : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
            tensorChartComponentProjection (E := E) r s Q.1 Q.2 Y •
              tensorChartBasisElement (E := E) r s Q.1 Q.2) from by rw [← hY]]
    rw [show chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b
          (tensorChartBasisElement (E := E) r s P.1 P.2)
          (∑ Q : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
            tensorChartComponentProjection (E := E) r s Q.1 Q.2 Y •
              tensorChartBasisElement (E := E) r s Q.1 Q.2) =
        ∑ Q : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          tensorChartComponentProjection (E := E) r s Q.1 Q.2 Y *
            chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b
              (tensorChartBasisElement (E := E) r s P.1 P.2)
              (tensorChartBasisElement (E := E) r s Q.1 Q.2) from ?_]
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun Q _ => ?_)
      ring
    · induction (Finset.univ : Finset ((Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)))) using Finset.induction with
      | empty =>
          rw [Finset.sum_empty, Finset.sum_empty]
          rw [show (0 : TensorRSModel r s ℝ E) =
              (0 : ℝ) • tensorChartBasisElement (E := E) r s P.1 P.2 from
            (zero_smul ℝ _).symm]
          rw [chartTensorInnerPointwise_rs_model_smul_right, zero_mul]
      | insert Q A hQ ih =>
          rw [Finset.sum_insert hQ, Finset.sum_insert hQ]
          rw [chartTensorInnerPointwise_rs_model_add_right,
            chartTensorInnerPointwise_rs_model_smul_right, ih]
  · induction (Finset.univ : Finset ((Fin r → Fin (Module.finrank ℝ E)) ×
        (Fin s → Fin (Module.finrank ℝ E)))) using Finset.induction with
    | empty =>
        rw [Finset.sum_empty, Finset.sum_empty]
        rw [show (0 : TensorRSModel r s ℝ E) =
            (0 : ℝ) • (0 : TensorRSModel r s ℝ E) from
          (smul_zero (0 : ℝ)).symm]
        rw [chartTensorInnerPointwise_rs_model_smul_left, zero_mul]
    | insert P A hP ih =>
        rw [Finset.sum_insert hP, Finset.sum_insert hP]
        rw [chartTensorInnerPointwise_rs_model_add_left,
          chartTensorInnerPointwise_rs_model_smul_left, ih]

/-- On the chart-`α` base set, the bundle-fibre tensor inner product of the
`toModel` images of two fibre elements `X`, `Y` equals the chart-`α`-frame
`(r, s)`-inner product of their `continuousLinearMapAt`-trivialised values. -/
private lemma tensorInnerPointwise_toModel_eq_chart
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) {b : M}
    (hb : b ∈ (chartAt H α).source)
    (X Y : TensorRSSpace r s I b) :
    tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel X) (TensorRSSpace.toModel Y) =
      chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ b X)
        ((trivializationAt (TensorRSModel r s ℝ E)
            (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ b
          Y) := by
  classical
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := hb
  rw [triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
    r s α hb X]
  rw [triv_continuousLinearMapAt_eq_chartRSTwistInv_toModel (I := I) (M := M)
    r s α hb Y]
  rw [chartTensorInnerPointwise_rs_model_eq_tensorInnerPointwise (I := I) (M := M)
    g r s α hb_base
    (chartRSTwistInv (I := I) (M := M) α b r s (TensorRSSpace.toModel X))
    (chartRSTwistInv (I := I) (M := M) α b r s (TensorRSSpace.toModel Y))]
  rw [chartRSTwist_chartRSTwistInv (I := I) (M := M) α hb_base r s
    (TensorRSSpace.toModel X)]
  rw [chartRSTwist_chartRSTwistInv (I := I) (M := M) α hb_base r s
    (TensorRSSpace.toModel Y)]

/-- The bundle-fibre tensor inner product of the `toModel` images of two fibre
elements expands as a finite component-coupled sum: the chart-frame
tensor-metric Gram on the chart-frame basis times the product of the wrapped
raw-component projections. -/
lemma tensorInnerPointwise_toModel_eq_component_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M) {b : M}
    (hb : b ∈ (chartAt H α).source)
    (X Y : TensorRSSpace r s I b) :
    tensorInnerPointwise (I := I) (M := M) g r s b
        (TensorRSSpace.toModel X) (TensorRSSpace.toModel Y) =
      ∑ P : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        ∑ Q : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b
              (tensorChartBasisElement (E := E) r s P.1 P.2)
              (tensorChartBasisElement (E := E) r s Q.1 Q.2) *
            (wrappedComponentProj (I := I) (M := M) r s α b P.1 P.2 X *
              wrappedComponentProj (I := I) (M := M) r s α b Q.1 Q.2 Y) := by
  classical
  rw [tensorInnerPointwise_toModel_eq_chart (I := I) (M := M) g r s α hb X Y]
  rw [chartTensorInnerPointwise_rs_model_eq_component_sum (I := I) (M := M)
    g r s α b
    ((trivializationAt (TensorRSModel r s ℝ E)
        (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ b X)
    ((trivializationAt (TensorRSModel r s ℝ E)
        (fun z : M => TensorRSSpace r s I z) α).continuousLinearMapAt ℝ b Y)]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  rw [wrappedComponentProj_apply, wrappedComponentProj_apply]

/-- The chart-coordinate covariant derivative depends on the directional vector
field `X` only through its value `X b` at the base point: the intrinsic chart
piece reads `X b` directly, and each Christoffel slot correction factors
through `chartLeviCivitaParallelCLM g α b X`, which depends on `X` only via
`X b`. -/
private lemma chartTensorRSCovariantDerivative_locality
    (r s : ℕ) (g : SmoothRiemannianMetric I M) (α : M)
    (T : Π b' : M, TensorRSSpace r s I b')
    (X Y : Π b' : M, TangentSpace I b') (b : M)
    (hXY : X b = Y b) :
    chartTensorRSCovariantDerivative (I := I) r s g α T X b =
      chartTensorRSCovariantDerivative (I := I) r s g α T Y b := by
  classical
  have hparallel : chartLeviCivitaParallelCLM (I := I) g α b X =
      chartLeviCivitaParallelCLM (I := I) g α b Y := by
    unfold chartLeviCivitaParallelCLM
    rw [hXY]
  rw [chartTensorRSCovariantDerivative_def, chartTensorRSCovariantDerivative_def,
    hXY]
  have hinput : (∑ k : Fin r,
        chartTensorRSInputSlotCorrection (I := I) r s g α T X b k) =
      ∑ k : Fin r,
        chartTensorRSInputSlotCorrection (I := I) r s g α T Y b k := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    unfold chartTensorRSInputSlotCorrection
    rw [hparallel]
  have houtput : (∑ l : Fin s,
        chartTensorRSOutputSlotCorrection (I := I) r s g α T X b l) =
      ∑ l : Fin s,
        chartTensorRSOutputSlotCorrection (I := I) r s g α T Y b l := by
    refine Finset.sum_congr rfl (fun l _ => ?_)
    unfold chartTensorRSOutputSlotCorrection
    rw [hparallel]
  rw [hinput, houtput]

/-- On the chart-`α` Levi-Civita good set, the abstract directional covariant
derivative `tensorCovDerivAt` of a smooth compactly-supported tensor section,
along the chart-coordinate basis direction `chartBasisVecFiber α m b`, equals
the chart-coordinate covariant derivative
`chartTensorRSCovariantDerivative r s g α S.toSection (chartBasisVecFiber α m)`
at `b`. -/
lemma tensorCovDerivAt_eq_chartTensorRSCovariantDerivative
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M)
    (m : Fin (Module.finrank ℝ E)) {b : M}
    (hb : b ∈ chartLeviCivitaGoodSet (I := I) α) :
    tensorCovDerivAt (I := I) (M := M) g r s S b
        (chartBasisVecFiber (I := I) α m b) =
      chartTensorRSCovariantDerivative (I := I) r s g α S.toSection
        (chartBasisVecFiber (I := I) α m) b := by
  classical
  obtain ⟨Xfield, hXfield⟩ :=
    ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) b
      (chartBasisVecFiber (I := I) α m b)
  have hXfield' : Xfield.toFun b = chartBasisVecFiber (I := I) α m b := hXfield
  have hagree := chartTensorRSCovariantDerivative_eq_abstract_on_chartLeviCivitaGoodSet (I := I) (M := M)
    g r s α S.toSection Xfield hb
  have hloc := chartTensorRSCovariantDerivative_locality (I := I) r s g α
    S.toSection Xfield.toFun (chartBasisVecFiber (I := I) α m) b hXfield'
  calc tensorCovDerivAt (I := I) (M := M) g r s S b
          (chartBasisVecFiber (I := I) α m b)
      = TensorRSNabla.tensorRSCovariantDerivative I M r s
          (LeviCivita (I := I) g) (fun y : M => S.toSection y) b
          (Xfield.toFun b) := by
        rw [tensorCovDerivAt_def, hXfield']
    _ = chartTensorRSCovariantDerivative (I := I) r s g α
          (fun y : M => S.toSection y) Xfield.toFun b := hagree.symm
    _ = chartTensorRSCovariantDerivative (I := I) r s g α
          (fun y : M => S.toSection y) (chartBasisVecFiber (I := I) α m) b :=
        hloc

/-- **The component-coupled principal part of the chart-coordinate Dirichlet
integrand.** A double sum over component multi-index pairs `P, Q` of the
chart-frame tensor-metric Gram `covChartMetricGram` times an inner double sum
over chart directions `k, l` of the un-weighted inverse Gram `chartInvGramEuclid`
times the product of the `k`-th chart-Euclidean partial derivative of the raw
component of `S` at `P` and the `l`-th chart-Euclidean partial derivative of
the raw component of `T` at `Q`. -/
noncomputable def covPrincipalIntegrand
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (α : M) :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) → ℝ :=
  fun y =>
    ∑ P : (Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E)),
      ∑ Q : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
          ∑ k : Fin (Module.finrank ℝ E),
            ∑ l : Fin (Module.finrank ℝ E),
              chartInvGramEuclid (I := I) g α k l y *
                euclidPartial (E := E) k
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M)
                      g r s S α P.1 P.2)) y *
                euclidPartial (E := E) l
                  (chartPushedRaw I α
                    (tensorChartComponentRaw (I := I) (M := M)
                      g r s T α Q.1 Q.2)) y

/-- Unfolding lemma for `covPrincipalIntegrand`. -/
lemma covPrincipalIntegrand_def
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (α : M)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    covPrincipalIntegrand (I := I) (M := M) g r s S T α y =
      ∑ P : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        ∑ Q : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                chartInvGramEuclid (I := I) g α k l y *
                  euclidPartial (E := E) k
                    (chartPushedRaw I α
                      (tensorChartComponentRaw (I := I) (M := M)
                        g r s S α P.1 P.2)) y *
                  euclidPartial (E := E) l
                    (chartPushedRaw I α
                      (tensorChartComponentRaw (I := I) (M := M)
                        g r s T α Q.1 Q.2)) y := rfl

/-- **Symmetry of the principal-part integrand under the `(S, T)` swap.**
Swapping `S` and `T` swaps the role of the two factors and the two component
multi-index pairs; the chart-frame tensor-metric Gram is symmetric and the
inverse Gram is symmetric, so the value is unchanged. -/
theorem covPrincipalIntegrand_symm
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (α : M)
    (y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))) :
    covPrincipalIntegrand (I := I) (M := M) g r s S T α y =
      covPrincipalIntegrand (I := I) (M := M) g r s T S α y := by
  classical
  rw [covPrincipalIntegrand_def, covPrincipalIntegrand_def]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun P _ => ?_)
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  rw [covChartMetricGram_symm (I := I) (M := M) g r s α Q P y]
  congr 1
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun k _ => ?_)
  refine Finset.sum_congr rfl (fun l _ => ?_)
  rw [show chartInvGramEuclid (I := I) g α l k y =
      chartInvGramEuclid (I := I) g α k l y from ?_]
  · ring
  · rw [chartInvGramEuclid_def, chartInvGramEuclid_def, chartInvGramOnE_def,
      chartInvGramOnE_def]
    have hHerm : (chartInvGramMatrix (I := I) g α
        ((extChartAt I α).symm (toEuclidean.symm y))).IsHermitian := by
      unfold chartInvGramMatrix
      exact (chartGramMatrix_isHermitian (I := I) g α
        ((extChartAt I α).symm (toEuclidean.symm y))).inv
    have hsymm := hHerm.apply k l
    rw [star_trivial] at hsymm
    exact hsymm

/-- **The chart-coordinate Dirichlet integrand as a component-coupled double
sum.** For `y` in the Euclidean chart target, set
`b := (extChartAt I α).symm (toEuclidean.symm y)`. The pointwise integrand
`tensorCovDerivPointwiseInner g r s S T b` equals the double sum over component
multi-index pairs `P, Q` of the chart-frame tensor-metric Gram
`covChartMetricGram` times the inner double sum over chart directions of the
un-weighted inverse Gram `chartInvGramEuclid` times the product of the
`(P, k)`-component of the chart-coordinate covariant derivative of `S` and the
`(Q, l)`-component of the chart-coordinate covariant derivative of `T` — each
component being `euclidPartial + covDerivLowerOrderTerm` by
`covDerivComponent_eq_euclidPartial_add_lowerOrder`. -/
theorem tensorCovDerivPointwiseInner_chart_eq_component_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S T : SmoothCcTensor g r s) (α : M)
    {y : EuclideanSpace ℝ (Fin (Module.finrank ℝ E))}
    (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorCovDerivPointwiseInner (I := I) (M := M) g r s S T
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)) =
      ∑ P : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        ∑ Q : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                chartInvGramEuclid (I := I) g α k l y *
                  (euclidPartial (E := E) k
                      (chartPushedRaw I α
                        (tensorChartComponentRaw (I := I) (M := M)
                          g r s S α P.1 P.2)) y +
                    covDerivLowerOrderTerm (I := I) (M := M)
                      g r s S α k P.1 P.2 y) *
                  (euclidPartial (E := E) l
                      (chartPushedRaw I α
                        (tensorChartComponentRaw (I := I) (M := M)
                          g r s T α Q.1 Q.2)) y +
                    covDerivLowerOrderTerm (I := I) (M := M)
                      g r s T α l Q.1 Q.2 y) := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hy_pre : (toEuclidean (E := E)).symm y ∈ (extChartAt I α).target := by
    rw [chartTargetEuclid_eq_preimage_symm (I := I) (M := M)] at hy
    exact hy
  have hb_chart : b ∈ (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  have hphi_b : extChartAt I α b = (toEuclidean (E := E)).symm y := by
    rw [hb_def]
    exact (extChartAt I α).right_inv hy_pre
  have hb_int :
      extChartAt I α b ∈ interior ((extChartAt I α).target : Set E) := by
    rw [hphi_b, (isOpen_extChartAt_target (I := I) α).interior_eq]
    exact hy_pre
  have hb_good : b ∈ chartLeviCivitaGoodSet (I := I) α := by
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [extChartAt_source]; exact hb_chart
    · rw [TangentBundle.trivializationAt_baseSet]; exact hb_chart
    · exact hb_int
  have hb_base : b ∈ (trivializationAt E (TangentSpace I) α).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hb_chart
  rw [← chartTensorCovDerivPointwiseInner_eq_tensorCovDerivPointwiseInner
    (I := I) (M := M) g α r s S T hb_base]
  unfold chartTensorCovDerivPointwiseInner
  have hcov_S : ∀ i : Fin (Module.finrank ℝ E),
      tensorCovDerivAt (I := I) (M := M) g r s S b
          (chartBasisVecFiber (I := I) α i b) =
        chartTensorRSCovariantDerivative (I := I) r s g α S.toSection
          (chartBasisVecFiber (I := I) α i) b := fun i =>
    tensorCovDerivAt_eq_chartTensorRSCovariantDerivative (I := I) (M := M)
      g r s S α i hb_good
  have hcov_T : ∀ j : Fin (Module.finrank ℝ E),
      tensorCovDerivAt (I := I) (M := M) g r s T b
          (chartBasisVecFiber (I := I) α j b) =
        chartTensorRSCovariantDerivative (I := I) r s g α T.toSection
          (chartBasisVecFiber (I := I) α j) b := fun j =>
    tensorCovDerivAt_eq_chartTensorRSCovariantDerivative (I := I) (M := M)
      g r s T α j hb_good
  have hG_entry : ∀ i j : Fin (Module.finrank ℝ E),
      (chartGramMatrix (I := I) g α b)⁻¹ i j =
        chartInvGramEuclid (I := I) g α i j y := by
    intro i j
    rw [chartInvGramEuclid_def, chartInvGramOnE_def]
    show (chartGramMatrix (I := I) g α b)⁻¹ i j =
      chartInvGramMatrix (I := I) g α
        ((extChartAt I α).symm (toEuclidean.symm y)) i j
    rw [chartInvGramMatrix]
  have hsum_rewrite :
      (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          (chartGramMatrix (I := I) g α b)⁻¹ i j *
            tensorInnerPointwise (I := I) (M := M) g r s b
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s S b
                  (chartBasisVecFiber (I := I) α i b)))
              (TensorRSSpace.toModel
                (tensorCovDerivAt (I := I) (M := M) g r s T b
                  (chartBasisVecFiber (I := I) α j b)))) =
        ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          chartInvGramEuclid (I := I) g α i j y *
            tensorInnerPointwise (I := I) (M := M) g r s b
              (TensorRSSpace.toModel
                (chartTensorRSCovariantDerivative (I := I) r s g α
                  S.toSection (chartBasisVecFiber (I := I) α i) b))
              (TensorRSSpace.toModel
                (chartTensorRSCovariantDerivative (I := I) r s g α
                  T.toSection (chartBasisVecFiber (I := I) α j) b)) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hcov_S i, hcov_T j, hG_entry i j]
  rw [hsum_rewrite]
  have hinner_expand : ∀ i j : Fin (Module.finrank ℝ E),
      tensorInnerPointwise (I := I) (M := M) g r s b
          (TensorRSSpace.toModel
            (chartTensorRSCovariantDerivative (I := I) r s g α
              S.toSection (chartBasisVecFiber (I := I) α i) b))
          (TensorRSSpace.toModel
            (chartTensorRSCovariantDerivative (I := I) r s g α
              T.toSection (chartBasisVecFiber (I := I) α j) b)) =
        ∑ P : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          ∑ Q : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
            chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b
                (tensorChartBasisElement (E := E) r s P.1 P.2)
                (tensorChartBasisElement (E := E) r s Q.1 Q.2) *
              ((euclidPartial (E := E) i
                    (chartPushedRaw I α
                      (tensorChartComponentRaw (I := I) (M := M)
                        g r s S α P.1 P.2)) y +
                  covDerivLowerOrderTerm (I := I) (M := M)
                    g r s S α i P.1 P.2 y) *
                (euclidPartial (E := E) j
                    (chartPushedRaw I α
                      (tensorChartComponentRaw (I := I) (M := M)
                        g r s T α Q.1 Q.2)) y +
                  covDerivLowerOrderTerm (I := I) (M := M)
                    g r s T α j Q.1 Q.2 y)) := by
    intro i j
    rw [tensorInnerPointwise_toModel_eq_component_sum (I := I) (M := M)
      g r s α hb_chart
      (chartTensorRSCovariantDerivative (I := I) r s g α
        S.toSection (chartBasisVecFiber (I := I) α i) b)
      (chartTensorRSCovariantDerivative (I := I) r s g α
        T.toSection (chartBasisVecFiber (I := I) α j) b)]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    have hSproj : wrappedComponentProj (I := I) (M := M) r s α b P.1 P.2
          (chartTensorRSCovariantDerivative (I := I) r s g α
            S.toSection (chartBasisVecFiber (I := I) α i) b) =
        euclidPartial (E := E) i
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M)
                g r s S α P.1 P.2)) y +
          covDerivLowerOrderTerm (I := I) (M := M) g r s S α i P.1 P.2 y := by
      rw [wrappedComponentProj_apply]
      exact covDerivComponent_eq_euclidPartial_add_lowerOrder (I := I) (M := M)
        g r s S α i P.1 P.2 hy
    have hTproj : wrappedComponentProj (I := I) (M := M) r s α b Q.1 Q.2
          (chartTensorRSCovariantDerivative (I := I) r s g α
            T.toSection (chartBasisVecFiber (I := I) α j) b) =
        euclidPartial (E := E) j
            (chartPushedRaw I α
              (tensorChartComponentRaw (I := I) (M := M)
                g r s T α Q.1 Q.2)) y +
          covDerivLowerOrderTerm (I := I) (M := M) g r s T α j Q.1 Q.2 y := by
      rw [wrappedComponentProj_apply]
      exact covDerivComponent_eq_euclidPartial_add_lowerOrder (I := I) (M := M)
        g r s T α j Q.1 Q.2 hy
    rw [hSproj, hTproj]
  have hLHS : (∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        chartInvGramEuclid (I := I) g α i j y *
          tensorInnerPointwise (I := I) (M := M) g r s b
            (TensorRSSpace.toModel
              (chartTensorRSCovariantDerivative (I := I) r s g α
                S.toSection (chartBasisVecFiber (I := I) α i) b))
            (TensorRSSpace.toModel
              (chartTensorRSCovariantDerivative (I := I) r s g α
                T.toSection (chartBasisVecFiber (I := I) α j) b))) =
      ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
        ∑ P : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          ∑ Q : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
            chartInvGramEuclid (I := I) g α i j y *
              chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b
                  (tensorChartBasisElement (E := E) r s P.1 P.2)
                  (tensorChartBasisElement (E := E) r s Q.1 Q.2) *
                ((euclidPartial (E := E) i
                      (chartPushedRaw I α
                        (tensorChartComponentRaw (I := I) (M := M)
                          g r s S α P.1 P.2)) y +
                    covDerivLowerOrderTerm (I := I) (M := M)
                      g r s S α i P.1 P.2 y) *
                  (euclidPartial (E := E) j
                      (chartPushedRaw I α
                        (tensorChartComponentRaw (I := I) (M := M)
                          g r s T α Q.1 Q.2)) y +
                    covDerivLowerOrderTerm (I := I) (M := M)
                      g r s T α j Q.1 Q.2 y)) := by
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [hinner_expand i j, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    ring
  rw [hLHS]
  have hRHS : (∑ P : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        ∑ Q : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            ∑ k : Fin (Module.finrank ℝ E),
              ∑ l : Fin (Module.finrank ℝ E),
                chartInvGramEuclid (I := I) g α k l y *
                  (euclidPartial (E := E) k
                      (chartPushedRaw I α
                        (tensorChartComponentRaw (I := I) (M := M)
                          g r s S α P.1 P.2)) y +
                    covDerivLowerOrderTerm (I := I) (M := M)
                      g r s S α k P.1 P.2 y) *
                  (euclidPartial (E := E) l
                      (chartPushedRaw I α
                        (tensorChartComponentRaw (I := I) (M := M)
                          g r s T α Q.1 Q.2)) y +
                    covDerivLowerOrderTerm (I := I) (M := M)
                      g r s T α l Q.1 Q.2 y)) =
      ∑ P : (Fin r → Fin (Module.finrank ℝ E)) ×
            (Fin s → Fin (Module.finrank ℝ E)),
        ∑ Q : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
            chartInvGramEuclid (I := I) g α i j y *
              chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b
                  (tensorChartBasisElement (E := E) r s P.1 P.2)
                  (tensorChartBasisElement (E := E) r s Q.1 Q.2) *
                ((euclidPartial (E := E) i
                      (chartPushedRaw I α
                        (tensorChartComponentRaw (I := I) (M := M)
                          g r s S α P.1 P.2)) y +
                    covDerivLowerOrderTerm (I := I) (M := M)
                      g r s S α i P.1 P.2 y) *
                  (euclidPartial (E := E) j
                      (chartPushedRaw I α
                        (tensorChartComponentRaw (I := I) (M := M)
                          g r s T α Q.1 Q.2)) y +
                    covDerivLowerOrderTerm (I := I) (M := M)
                      g r s T α j Q.1 Q.2 y)) := by
    refine Finset.sum_congr rfl (fun P _ => ?_)
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    rw [covChartMetricGram_def, ← hb_def, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    ring
  rw [hRHS]
  set termFun :
      (Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E)) →
        ((Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E))) ×
        ((Fin r → Fin (Module.finrank ℝ E)) ×
          (Fin s → Fin (Module.finrank ℝ E))) → ℝ :=
    fun ij PQ =>
      chartInvGramEuclid (I := I) g α ij.1 ij.2 y *
        chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b
            (tensorChartBasisElement (E := E) r s PQ.1.1 PQ.1.2)
            (tensorChartBasisElement (E := E) r s PQ.2.1 PQ.2.2) *
          ((euclidPartial (E := E) ij.1
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M)
                    g r s S α PQ.1.1 PQ.1.2)) y +
              covDerivLowerOrderTerm (I := I) (M := M)
                g r s S α ij.1 PQ.1.1 PQ.1.2 y) *
            (euclidPartial (E := E) ij.2
                (chartPushedRaw I α
                  (tensorChartComponentRaw (I := I) (M := M)
                    g r s T α PQ.2.1 PQ.2.2)) y +
              covDerivLowerOrderTerm (I := I) (M := M)
                g r s T α ij.2 PQ.2.1 PQ.2.2 y)) with htermFun_def
  have hLHS_prod :
      (∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
          ∑ PQ : ((Fin r → Fin (Module.finrank ℝ E)) ×
                    (Fin s → Fin (Module.finrank ℝ E))) ×
                  ((Fin r → Fin (Module.finrank ℝ E)) ×
                    (Fin s → Fin (Module.finrank ℝ E))),
            termFun ij PQ) =
        ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
          ∑ P : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
            ∑ Q : (Fin r → Fin (Module.finrank ℝ E)) ×
                  (Fin s → Fin (Module.finrank ℝ E)),
              chartInvGramEuclid (I := I) g α i j y *
                chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b
                    (tensorChartBasisElement (E := E) r s P.1 P.2)
                    (tensorChartBasisElement (E := E) r s Q.1 Q.2) *
                  ((euclidPartial (E := E) i
                        (chartPushedRaw I α
                          (tensorChartComponentRaw (I := I) (M := M)
                            g r s S α P.1 P.2)) y +
                      covDerivLowerOrderTerm (I := I) (M := M)
                        g r s S α i P.1 P.2 y) *
                    (euclidPartial (E := E) j
                        (chartPushedRaw I α
                          (tensorChartComponentRaw (I := I) (M := M)
                            g r s T α Q.1 Q.2)) y +
                      covDerivLowerOrderTerm (I := I) (M := M)
                        g r s T α j Q.1 Q.2 y)) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rw [Fintype.sum_prod_type]
  have hRHS_prod :
      (∑ PQ : ((Fin r → Fin (Module.finrank ℝ E)) ×
                  (Fin s → Fin (Module.finrank ℝ E))) ×
                ((Fin r → Fin (Module.finrank ℝ E)) ×
                  (Fin s → Fin (Module.finrank ℝ E))),
          ∑ ij : Fin (Module.finrank ℝ E) × Fin (Module.finrank ℝ E),
            termFun ij PQ) =
        ∑ P : (Fin r → Fin (Module.finrank ℝ E)) ×
              (Fin s → Fin (Module.finrank ℝ E)),
          ∑ Q : (Fin r → Fin (Module.finrank ℝ E)) ×
                (Fin s → Fin (Module.finrank ℝ E)),
            ∑ i : Fin (Module.finrank ℝ E), ∑ j : Fin (Module.finrank ℝ E),
              chartInvGramEuclid (I := I) g α i j y *
                chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b
                    (tensorChartBasisElement (E := E) r s P.1 P.2)
                    (tensorChartBasisElement (E := E) r s Q.1 Q.2) *
                  ((euclidPartial (E := E) i
                        (chartPushedRaw I α
                          (tensorChartComponentRaw (I := I) (M := M)
                            g r s S α P.1 P.2)) y +
                      covDerivLowerOrderTerm (I := I) (M := M)
                        g r s S α i P.1 P.2 y) *
                    (euclidPartial (E := E) j
                        (chartPushedRaw I α
                          (tensorChartComponentRaw (I := I) (M := M)
                            g r s T α Q.1 Q.2)) y +
                      covDerivLowerOrderTerm (I := I) (M := M)
                        g r s T α j Q.1 Q.2 y)) := by
    rw [Fintype.sum_prod_type]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    rw [Fintype.sum_prod_type]
  rw [← hLHS_prod, ← hRHS_prod, Finset.sum_comm]

end TensorRegularity
end Laplacian
end Analysis
end DifferentialGeometry
