import DifferentialGeometry.Analysis.Parabolic.TensorSpectral.EllipticBridge.EigenvectorWeakSolution.PouComponentBridge
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.Analysis.InnerProductSpace.Completion

/-!
# Chart-pull of the `L²` tensor inner product against an abstract `L²` element

For a closed Riemannian manifold `(M, g)` and fixed ranks `(r, s)`, the metric
`L²` Hilbert space `TensorL2 r s g` of `(r, s)`-tensor fields is the Hausdorff
completion of the seminormed space `SmoothCcTensor g r s` of smooth
compactly-supported tensor sections. A general element of `TensorL2 r s g`
carries no concrete tensor section.

The chart-local elliptic-regularity analysis of the connection Laplacian needs
to express the global `L²` inner product of a concrete smooth tensor section
against such an abstract element as a chart-Euclidean integral of the chart
components. This file builds that bridge.

## The two chart-pulls

The project already has the chart-pull of the global `L²` pairing of two
concrete sections, one of which is supported inside the chart, in the form of
`tensorL2Inner_rotatedTestSection_chart_pull` for the inverse-Gram-rotated test
section. This file first proves the general such chart-pull
(`tensorL2Inner_chartSupported_chart_pull`): for a concrete smooth section `Sg`
supported inside the chart-`α` source and an arbitrary concrete smooth section
`T`, the global pairing equals the chart-Euclidean integral over
`chartTargetEuclid α` of

```
densityOnEuclid g α y · ∑_P ∑_Q covChartMetricGram g r s α P Q y ·
  tensorComponentEuclid g r s Sg α P y · tensorComponentEuclid g r s T α Q y.
```

The chart components here are the *raw* Euclidean chart components
`tensorComponentEuclid`. This chart-pull is partition-of-unity-free, exactly
like `tensorL2Inner_rotatedTestSection_chart_pull`.

It then extends the second argument to an abstract `L²` element. The canonical
Euclidean chart component of an abstract element, `tensorL2ChartComponent`, is
on a smooth section the **partition-of-unity-weighted** Euclidean chart
component `tensorChartComponent` — the chart-atlas partition-of-unity weight
`chartAtlasPOU I M α` times the raw chart component — because only the weighted
component carries a uniform `L²` bound and hence extends continuously to the
completion. The single partition-of-unity factor carried by the abstract chart
component is matched on the concrete side by replacing the concrete section `Sg`
with `pouSmul g r s α Sg = chartAtlasPOU I M α • Sg`: reassociating the pointwise
product `(weight · rawSg) · rawT = rawSg · (weight · rawT)` moves the weight onto
the abstract side, where it is exactly the weighting built into
`tensorL2ChartComponent`.

## Main results

* `tensorL2Inner_chartSupported_chart_pull` — the general concrete two-section
  chart-pull: the global `L²` pairing of a chart-supported smooth section `Sg`
  against an arbitrary smooth section `T` as a chart-Euclidean integral of the
  raw chart components.
* `tensorL2Inner_pouSmul_tensorL2ChartComponent_pull` — the headline: the global
  `L²` inner product of the partition-of-unity-weighted concrete section
  `pouSmul g r s α Sg` against an abstract `L²` element `u`, as the
  chart-Euclidean integral coupling the raw chart components of `Sg` to the
  canonical Euclidean chart components `tensorL2ChartComponent` of `u`.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.style.setOption false
set_option synthInstance.maxHeartbeats 1600000
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false

open Bundle Manifold MeasureTheory Set Filter Tensor0SBundle
open scoped Manifold Topology ContDiff ENNReal NNReal BigOperators Matrix
  RealInnerProductSpace InnerProductSpace

namespace DifferentialGeometry
namespace Analysis
namespace Parabolic
namespace TensorSpectral

open DifferentialGeometry.Integral.Connection
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.L2
open DifferentialGeometry.Analysis.Sobolev.Chart
open DifferentialGeometry.Analysis.Laplacian.TensorRegularity
open DifferentialGeometry.Analysis.Laplacian.MetricExtension hiding chartTargetEuclid
open DifferentialGeometry.Analysis.Laplacian.ChartMeasureEquiv

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [CompactSpace M] [I.Boundaryless] [T2Space M] [SigmaCompactSpace M]

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩
private local instance : MeasurableSpace M := borel M
private local instance : BorelSpace M := ⟨rfl⟩

local notation "EuclN" => EuclideanSpace ℝ (Fin (Module.finrank ℝ E))

/-- The wrapped raw-component projection of a smooth section's section value is
its raw chart-frame scalar component. -/
private lemma wrappedComponentProj_section_eq_tensorChartComponentRaw
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (S : SmoothCcTensor g r s) (α : M) (b : M)
    (Idx : Fin r → Fin (Module.finrank ℝ E))
    (Jdx : Fin s → Fin (Module.finrank ℝ E)) :
    wrappedComponentProj (I := I) (M := M) r s α b Idx Jdx (S.toSection b) =
      tensorChartComponentRaw (I := I) (M := M) g r s S α Idx Jdx b := by
  rw [wrappedComponentProj_apply, tensorChartComponentRaw_def]
  rfl

/-- **Chart-coordinate factorisation of the pointwise tensor inner product.** On
the Euclidean chart target the pointwise tensor inner product of two smooth
tensor sections `Sg` and `T`, read at the chart-source preimage of `y`, factors
as the finite component-coupled sum

```
∑_P ∑_Q covChartMetricGram g r s α P Q y ·
  tensorComponentEuclid g r s Sg α P y · tensorComponentEuclid g r s T α Q y.
```
-/
private lemma tensorInnerPointwise_chart_eq_component_sum
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Sg T : SmoothCcTensor g r s) (α : M)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    tensorInnerPointwise (I := I) (M := M) g r s
        ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))
        (Sg.toFun ((extChartAt I α).symm ((toEuclidean (E := E)).symm y)))
        (T.toFun ((extChartAt I α).symm ((toEuclidean (E := E)).symm y))) =
      ∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
          tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
          tensorComponentEuclid (I := I) (M := M) g r s T α Q y := by
  classical
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hb_chart : b ∈ (chartAt H α).source :=
    symm_toEuclidean_symm_mem_chartAtSource (I := I) (M := M) α hy
  rw [show Sg.toFun b = TensorRSSpace.toModel (Sg.toSection b) from rfl]
  rw [show T.toFun b = TensorRSSpace.toModel (T.toSection b) from rfl]
  rw [tensorInnerPointwise_toModel_eq_component_sum (I := I) (M := M)
    g r s α hb_chart (Sg.toSection b) (T.toSection b)]
  refine Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl (fun Q _ => ?_))
  rw [show chartTensorInnerPointwise_rs_model (I := I) (M := M) g r s α b
        (tensorChartBasisElement (E := E) r s P.1 P.2)
        (tensorChartBasisElement (E := E) r s Q.1 Q.2) =
      covChartMetricGram (I := I) (M := M) g r s α P Q y from by
    rw [covChartMetricGram_def, ← hb_def]]
  rw [wrappedComponentProj_section_eq_tensorChartComponentRaw
    (I := I) (M := M) g r s Sg α b P.1 P.2,
    wrappedComponentProj_section_eq_tensorChartComponentRaw
      (I := I) (M := M) g r s T α b Q.1 Q.2]
  rw [show tensorChartComponentRaw (I := I) (M := M) g r s Sg α P.1 P.2 b =
      tensorComponentEuclid (I := I) (M := M) g r s Sg α P y from by
    rw [tensorComponentEuclid_apply_of_mem (I := I) (M := M) g r s Sg α P hy,
      hb_def]]
  rw [show tensorChartComponentRaw (I := I) (M := M) g r s T α Q.1 Q.2 b =
      tensorComponentEuclid (I := I) (M := M) g r s T α Q y from by
    rw [tensorComponentEuclid_apply_of_mem (I := I) (M := M) g r s T α Q hy,
      hb_def]]
  ring

/-- The `L²` pairing integrand `x ↦ ⟨Sg(x), T(x)⟩` of two smooth tensor sections
is continuous on `M`. -/
private lemma pairingIntegrand_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Sg T : SmoothCcTensor g r s) :
    Continuous
      (fun x : M => tensorInnerPointwise (I := I) (M := M) g r s x
        (Sg.toFun x) (T.toFun x)) :=
  DifferentialGeometry.Integral.L2.SmoothCcTensor.continuous_inner_cross
    (I := I) (M := M) Sg T

/-- The topological support of the `L²` pairing integrand of `Sg` against `T`
sits inside the chart-`α` source whenever `Sg` is chart-supported: the integrand
vanishes wherever `Sg` does, and `Sg`'s support lies inside the chart source. -/
private lemma pairingIntegrand_tsupport_subset
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Sg T : SmoothCcTensor g r s) (α : M)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    tsupport
        (fun x : M => tensorInnerPointwise (I := I) (M := M) g r s x
          (Sg.toFun x) (T.toFun x)) ⊆
      (chartAt H α).source := by
  refine (closure_minimal ?_ (isClosed_tsupport Sg.toFun)).trans hSg
  intro x hx
  rw [Function.mem_support] at hx
  by_contra hx_notsupp
  exact hx (by
    rw [image_eq_zero_of_notMem_tsupport hx_notsupp]
    exact tensorInnerPointwise_zero_left (I := I) (M := M) g r s x (T.toFun x))

/-- **The general concrete two-section chart-pull.** For a smooth Riemannian
metric `g` on a closed Riemannian manifold `(M, g)`, a chart center `α`, and two
smooth compactly-supported `(r, s)`-tensor sections `Sg` (supported inside the
chart-`α` source) and `T` (arbitrary), the global `L²` inner product of `Sg`
against `T` equals the chart-Euclidean integral

```
∫ y in chartTargetEuclid α,
  densityOnEuclid g α y · ∑_P ∑_Q covChartMetricGram g r s α P Q y ·
    tensorComponentEuclid g r s Sg α P y · tensorComponentEuclid g r s T α Q y
  ∂volume.
```

The chart components are the raw Euclidean chart components
`tensorComponentEuclid`; the identity is partition-of-unity-free. -/
theorem tensorL2Inner_chartSupported_chart_pull
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (Sg T : SmoothCcTensor g r s) (α : M)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    tensorL2Inner (I := I) (M := M) g r s Sg.toFun T.toFun =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
              tensorComponentEuclid (I := I) (M := M) g r s T α Q y)
        ∂(volume : Measure EuclN) := by
  classical
  rw [show tensorL2Inner (I := I) (M := M) g r s Sg.toFun T.toFun =
      ∫ x, tensorInnerPointwise (I := I) (M := M) g r s x (Sg.toFun x) (T.toFun x)
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) from rfl]
  have hcont : Continuous
      (fun x : M => tensorInnerPointwise (I := I) (M := M) g r s x
        (Sg.toFun x) (T.toFun x)) :=
    pairingIntegrand_continuous (I := I) (M := M) g r s Sg T
  have hsupp : tsupport
      (fun x : M => tensorInnerPointwise (I := I) (M := M) g r s x
        (Sg.toFun x) (T.toFun x)) ⊆
      (chartAt H α).source :=
    pairingIntegrand_tsupport_subset (I := I) (M := M) g r s Sg T α hSg
  rw [integral_riemannianVolumeMeasure_eq_euclidean_chartTarget
    (I := I) (M := M) g α hcont hsupp]
  rw [map_toEuclidean_modelHaar_eq_volume (E := E)]
  have hctE_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α).measurableSet
  refine setIntegral_congr_fun hctE_meas (fun y hy => ?_)
  rw [tensorInnerPointwise_chart_eq_component_sum (I := I) (M := M)
    g r s Sg T α hy]

/-- On the Euclidean chart target the raw Euclidean chart component of the
partition-of-unity-weighted section `pouSmul g r s α Sg` equals the weighted
Euclidean chart component `tensorChartComponent` of `Sg`. -/
private lemma tensorComponentEuclid_pouSmul_eq_tensorChartComponent
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (P : CompIdx E r s) :
    tensorComponentEuclid (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α Sg) α P =
      tensorChartComponent (I := I) (M := M) g r s Sg α P.1 P.2 :=
  (tensorChartComponent_eq_tensorComponentEuclid_pouSmul
    (I := I) (M := M) g r s α Sg P).symm

/-- **The chart-coordinate summand after reassociating the partition-of-unity
weight.** On the Euclidean chart target each component-coupled summand of the
chart-pull of `⟨pouSmul g r s α Sg, T⟩`, rewritten through the weighted Euclidean
chart component of `Sg`, equals the same summand with the partition-of-unity
weight moved onto `T` — i.e. the raw Euclidean chart component of `Sg` times the
weighted Euclidean chart component `tensorChartComponent` of `T`. -/
private lemma componentSum_pouSmul_reassoc
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg T : SmoothCcTensor g r s)
    {y : EuclN} (hy : y ∈ chartTargetEuclid (I := I) (M := M) α) :
    (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
          tensorComponentEuclid (I := I) (M := M) g r s
            (pouSmul (I := I) (M := M) g r s α Sg) α P y *
          tensorComponentEuclid (I := I) (M := M) g r s T α Q y) =
      ∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
          tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
          tensorChartComponent (I := I) (M := M) g r s T α Q.1 Q.2 y := by
  classical
  refine Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl (fun Q _ => ?_))
  rw [tensorComponentEuclid_pouSmul_eq_tensorChartComponent
    (I := I) (M := M) g r s α Sg P]
  set b : M := (extChartAt I α).symm ((toEuclidean (E := E)).symm y) with hb_def
  have hSg_eq : tensorChartComponent (I := I) (M := M) g r s Sg α P.1 P.2 y =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
        tensorComponentEuclid (I := I) (M := M) g r s Sg α P y := by
    rw [tensorChartComponent_def]
    rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
    rw [tensorComponentEuclid_apply_of_mem (I := I) (M := M) g r s Sg α P hy]
    rfl
  have hT_eq : tensorChartComponent (I := I) (M := M) g r s T α Q.1 Q.2 y =
      ((chartAtlasPOU I M α : C^∞⟮I, M; ℝ⟯) : M → ℝ) b *
        tensorComponentEuclid (I := I) (M := M) g r s T α Q y := by
    rw [tensorChartComponent_def]
    rw [chartPushedRaw_apply_of_mem (I := I) (M := M) α _ hy]
    rw [tensorComponentEuclid_apply_of_mem (I := I) (M := M) g r s T α Q hy]
    rfl
  rw [hSg_eq, hT_eq]
  ring

/-- The almost-everywhere identity, on the Euclidean chart target, between the
weighted Euclidean chart component `tensorChartComponent` of a smooth section
and the canonical Euclidean chart component `tensorL2ChartComponent` of its `L²`
class. -/
private lemma tensorChartComponent_aeEq_tensorL2ChartComponent
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (T : SmoothCcTensor g r s) (α : M) (Q : CompIdx E r s) :
    tensorChartComponent (I := I) (M := M) g r s T α Q.1 Q.2 =ᵐ[
        (volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)]
      ((tensorL2ChartComponent (I := I) (M := M) g r s
          (T : TensorL2 r s g) α Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) :=
  (tensorL2ChartComponent_smoothToTensorL2_coeFn
    (I := I) (M := M) g r s T α Q).symm

/-- The Euclidean chart target carries plain Lebesgue measure: `chartL2Measure α`
unfolds to `volume.restrict (chartTargetEuclid α)`. -/
private lemma chartL2Measure_eq_volume_restrict (α : M) :
    chartL2Measure (I := I) (M := M) α =
      (volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α) := rfl

/-- The pointwise integrand of the chart-pull of `⟨pouSmul g r s α Sg, T⟩`,
rewritten through the weighted chart component of `T`, agrees almost everywhere
on the chart target with the integrand built from the canonical abstract chart
component `tensorL2ChartComponent` of `T`'s `L²` class. -/
private lemma chartPull_integrand_aeEq_abstract
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg T : SmoothCcTensor g r s) :
    (fun y : EuclN => densityOnEuclid (I := I) g α y *
        (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
            tensorChartComponent (I := I) (M := M) g r s T α Q.1 Q.2 y)) =ᵐ[
        (volume : Measure EuclN).restrict (chartTargetEuclid (I := I) (M := M) α)]
      (fun y : EuclN => densityOnEuclid (I := I) g α y *
        (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
            ((tensorL2ChartComponent (I := I) (M := M) g r s
                (T : TensorL2 r s g) α Q :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
              y)) := by
  classical
  have hae : ∀ Q : CompIdx E r s,
      tensorChartComponent (I := I) (M := M) g r s T α Q.1 Q.2 =ᵐ[
          (volume : Measure EuclN).restrict
            (chartTargetEuclid (I := I) (M := M) α)]
        ((tensorL2ChartComponent (I := I) (M := M) g r s
            (T : TensorL2 r s g) α Q :
            Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) :=
    fun Q => tensorChartComponent_aeEq_tensorL2ChartComponent
      (I := I) (M := M) g r s T α Q
  have hall : ∀ᵐ y ∂((volume : Measure EuclN).restrict
        (chartTargetEuclid (I := I) (M := M) α)),
      ∀ Q : CompIdx E r s,
        tensorChartComponent (I := I) (M := M) g r s T α Q.1 Q.2 y =
          ((tensorL2ChartComponent (I := I) (M := M) g r s
              (T : TensorL2 r s g) α Q :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y := by
    rw [MeasureTheory.ae_all_iff]
    exact hae
  filter_upwards [hall] with y hy
  refine congrArg (densityOnEuclid (I := I) g α y * ·) ?_
  refine Finset.sum_congr rfl (fun P _ => Finset.sum_congr rfl (fun Q _ => ?_))
  rw [hy Q]

/-- **The concrete two-section chart-pull through the abstract chart component.**
For a chart-supported smooth section `Sg` and an arbitrary smooth section `T`, the
global `L²` pairing of `pouSmul g r s α Sg` against `T` equals the chart-Euclidean
integral coupling the raw Euclidean chart components of `Sg` to the canonical
Euclidean chart components `tensorL2ChartComponent` of `T`'s `L²` class. -/
private lemma tensorL2Inner_pouSmul_smooth_chart_pull
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg T : SmoothCcTensor g r s) :
    tensorL2Inner (I := I) (M := M) g r s
        (pouSmul (I := I) (M := M) g r s α Sg).toFun T.toFun =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
              ((tensorL2ChartComponent (I := I) (M := M) g r s
                  (T : TensorL2 r s g) α Q :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)
                y)
        ∂(volume : Measure EuclN) := by
  classical
  have hpou_supp : tsupport (pouSmul (I := I) (M := M) g r s α Sg).toFun ⊆
      (chartAt H α).source :=
    pouSmul_tsupport_subset_chartSource (I := I) (M := M) g r s α Sg
  rw [tensorL2Inner_chartSupported_chart_pull (I := I) (M := M) g r s
    (pouSmul (I := I) (M := M) g r s α Sg) T α hpou_supp]
  have hctE_meas : MeasurableSet (chartTargetEuclid (I := I) (M := M) α) :=
    (DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α).measurableSet
  rw [setIntegral_congr_fun hctE_meas (fun y hy => by
    rw [componentSum_pouSmul_reassoc (I := I) (M := M) g r s α Sg T hy])]
  exact MeasureTheory.integral_congr_ae
    (chartPull_integrand_aeEq_abstract (I := I) (M := M) g r s α Sg T)

/-- The chart coefficient pairing the source `Sg` against the `Q`-th canonical
abstract chart component: `∑_P densityOnEuclid g α y · covChartMetricGram g r s α
P Q y · tensorComponentEuclid g r s Sg α P y`. -/
private noncomputable def chartPullCoeff
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (Q : CompIdx E r s) : EuclN → ℝ :=
  fun y => ∑ P : CompIdx E r s,
    densityOnEuclid (I := I) g α y *
      covChartMetricGram (I := I) (M := M) g r s α P Q y *
      tensorComponentEuclid (I := I) (M := M) g r s Sg α P y

/-- A single summand of the chart coefficient `densityOnEuclid g α ·
covChartMetricGram g r s α P Q · tensorComponentEuclid g r s Sg α P` is, for a
chart-supported section `Sg`, continuous on the whole Euclidean model space: it
is `ContDiffOn` on the open chart target, and its topological support sits
inside the (compact) support of `tensorComponentEuclid g r s Sg α P`, hence inside
the chart target. -/
private lemma chartPullCoeff_summand_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (P Q : CompIdx E r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    Continuous (fun y : EuclN =>
      densityOnEuclid (I := I) g α y *
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
        tensorComponentEuclid (I := I) (M := M) g r s Sg α P y) := by
  classical
  have hopen : IsOpen (chartTargetEuclid (I := I) (M := M) α) :=
    DifferentialGeometry.Analysis.Sobolev.Chart.chartTargetEuclid_isOpen
      (I := I) (M := M) α
  have hdensity : ContinuousOn (densityOnEuclid (I := I) g α)
      (chartTargetEuclid (I := I) (M := M) α) :=
    (densityOnEuclid_contDiffOn (I := I) g α).continuousOn
  have hgram : ContinuousOn (covChartMetricGram (I := I) (M := M) g r s α P Q)
      (chartTargetEuclid (I := I) (M := M) α) :=
    (covChartMetricGram_contDiffOn (I := I) (M := M) g r s α P Q).continuousOn
  have hcomp : ContinuousOn (tensorComponentEuclid (I := I) (M := M) g r s Sg α P)
      (chartTargetEuclid (I := I) (M := M) α) :=
    (tensorComponentEuclid_contDiffOn (I := I) (M := M) g r s Sg α P).continuousOn
  have hcontOn : ContinuousOn (fun y : EuclN =>
      densityOnEuclid (I := I) g α y *
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
        tensorComponentEuclid (I := I) (M := M) g r s Sg α P y)
      (chartTargetEuclid (I := I) (M := M) α) :=
    (hdensity.mul hgram).mul hcomp
  have hsupp_subset : tsupport (fun y : EuclN =>
      densityOnEuclid (I := I) g α y *
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
        tensorComponentEuclid (I := I) (M := M) g r s Sg α P y) ⊆
      chartTargetEuclid (I := I) (M := M) α := by
    refine Subset.trans ?_
      (tensorComponentEuclid_tsupport_subset (I := I) (M := M) g r s Sg α P hSg)
    refine closure_minimal ?_ (isClosed_tsupport _)
    intro y hy
    rw [Function.mem_support] at hy
    refine subset_tsupport _ ?_
    rw [Function.mem_support]
    intro hzero
    exact hy (by rw [hzero, mul_zero])
  exact hcontOn.continuous_of_tsupport_subset hopen hsupp_subset

/-- The single chart-coefficient summand has compact support: its support sits
inside the compact support of `tensorComponentEuclid g r s Sg α P`. -/
private lemma chartPullCoeff_summand_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (P Q : CompIdx E r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    HasCompactSupport (fun y : EuclN =>
      densityOnEuclid (I := I) g α y *
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
        tensorComponentEuclid (I := I) (M := M) g r s Sg α P y) := by
  classical
  refine HasCompactSupport.of_support_subset_isCompact
    (tensorComponentEuclid_hasCompactSupport (I := I) (M := M) g r s Sg α P hSg) ?_
  intro y hy
  rw [Function.mem_support] at hy
  refine subset_tsupport _ ?_
  rw [Function.mem_support]
  intro hzero
  exact hy (by rw [hzero, mul_zero])

/-- The chart coefficient `chartPullCoeff g r s α Sg Q` is, for a chart-supported
section `Sg`, continuous on the whole Euclidean model space: it is a finite sum
of continuous summands. -/
private lemma chartPullCoeff_continuous
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (Q : CompIdx E r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    Continuous (chartPullCoeff (I := I) (M := M) g r s α Sg Q) := by
  classical
  unfold chartPullCoeff
  exact continuous_finset_sum _ (fun P _ =>
    chartPullCoeff_summand_continuous (I := I) (M := M) g r s α Sg P Q hSg)

/-- The chart coefficient `chartPullCoeff g r s α Sg Q` has compact support: its
support sits inside the finite union, over `P`, of the compact supports of the
chart-coefficient summands. -/
private lemma chartPullCoeff_hasCompactSupport
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (Q : CompIdx E r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    HasCompactSupport (chartPullCoeff (I := I) (M := M) g r s α Sg Q) := by
  classical
  set K : Set EuclN :=
    ⋃ P : CompIdx E r s, tsupport (fun y : EuclN =>
      densityOnEuclid (I := I) g α y *
        covChartMetricGram (I := I) (M := M) g r s α P Q y *
        tensorComponentEuclid (I := I) (M := M) g r s Sg α P y) with hK_def
  have hK_compact : IsCompact K := by
    rw [hK_def]
    refine isCompact_iUnion (fun P => ?_)
    exact chartPullCoeff_summand_hasCompactSupport
      (I := I) (M := M) g r s α Sg P Q hSg
  refine HasCompactSupport.of_support_subset_isCompact hK_compact ?_
  intro y hy
  rw [Function.mem_support] at hy
  rw [hK_def, Set.mem_iUnion]
  by_contra hy_notin
  simp only [not_exists] at hy_notin
  refine hy ?_
  unfold chartPullCoeff
  refine Finset.sum_eq_zero (fun P _ => ?_)
  exact image_eq_zero_of_notMem_tsupport (f := fun y : EuclN =>
    densityOnEuclid (I := I) g α y *
      covChartMetricGram (I := I) (M := M) g r s α P Q y *
      tensorComponentEuclid (I := I) (M := M) g r s Sg α P y) (hy_notin P)

/-- The chart coefficient `chartPullCoeff g r s α Sg Q` is in `MemLp 2` of the
Euclidean `L²` reference measure of the chart: it is continuous with compact
support, and a continuous compactly-supported function lies in every `Lᵖ`. -/
private lemma chartPullCoeff_memLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (Q : CompIdx E r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    MemLp (chartPullCoeff (I := I) (M := M) g r s α Sg Q) 2
      (chartL2Measure (I := I) (M := M) α) := by
  haveI : IsFiniteMeasureOnCompacts (chartL2Measure (I := I) (M := M) α) := by
    rw [chartL2Measure_eq_volume_restrict (I := I) (M := M) α]
    infer_instance
  exact (chartPullCoeff_continuous (I := I) (M := M) g r s α Sg Q
      hSg).memLp_of_hasCompactSupport
    (chartPullCoeff_hasCompactSupport (I := I) (M := M) g r s α Sg Q hSg)

/-- The `L²` class of the chart coefficient `chartPullCoeff g r s α Sg Q`. -/
private noncomputable def chartPullCoeffLp
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (Q : CompIdx E r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) :=
  (chartPullCoeff_memLp (I := I) (M := M) g r s α Sg Q hSg).toLp _

/-- The `L²` inner product of the chart coefficient `L²` class against an
`Lp` element is the Bochner integral of the pointwise product. -/
private lemma inner_chartPullCoeffLp_eq_integral
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (Q : CompIdx E r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source)
    (w : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) :
    (⟪chartPullCoeffLp (I := I) (M := M) g r s α Sg Q hSg, w⟫_ℝ : ℝ) =
      ∫ y, chartPullCoeff (I := I) (M := M) g r s α Sg Q y * (w : EuclN → ℝ) y
        ∂(chartL2Measure (I := I) (M := M) α) := by
  classical
  rw [MeasureTheory.L2.inner_def]
  refine MeasureTheory.integral_congr_ae ?_
  have hcoe : ((chartPullCoeffLp (I := I) (M := M) g r s α Sg Q hSg :
        Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) =ᵐ[
        chartL2Measure (I := I) (M := M) α]
      chartPullCoeff (I := I) (M := M) g r s α Sg Q := by
    unfold chartPullCoeffLp
    exact MemLp.coeFn_toLp _
  filter_upwards [hcoe] with y hy
  rw [RCLike.inner_apply, conj_trivial, hy, mul_comm]

/-- The `L²` inner product against the chart coefficient `L²` class, as a
function of the abstract `L²` element through the canonical chart component, is
continuous. -/
private lemma continuous_chartPullCoeff_pairing
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (Q : CompIdx E r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    Continuous (fun u : TensorL2 r s g =>
      (⟪chartPullCoeffLp (I := I) (M := M) g r s α Sg Q hSg,
          tensorL2ChartComponent (I := I) (M := M) g r s u α Q⟫_ℝ : ℝ)) := by
  classical
  have hfun : (fun u : TensorL2 r s g =>
      (⟪chartPullCoeffLp (I := I) (M := M) g r s α Sg Q hSg,
          tensorL2ChartComponent (I := I) (M := M) g r s u α Q⟫_ℝ : ℝ)) =
      (fun w : Lp ℝ 2 (chartL2Measure (I := I) (M := M) α) =>
        (⟪chartPullCoeffLp (I := I) (M := M) g r s α Sg Q hSg, w⟫_ℝ : ℝ)) ∘
        (fun u : TensorL2 r s g =>
          tensorL2ChartComponentCLM (I := I) (M := M) g r s α Q u) := by
    funext u
    rw [Function.comp_apply, tensorL2ChartComponentCLM_apply]
  rw [hfun]
  refine Continuous.comp ?_
    (tensorL2ChartComponentCLM (I := I) (M := M) g r s α Q).continuous
  exact (innerSL ℝ
    (chartPullCoeffLp (I := I) (M := M) g r s α Sg Q hSg)).continuous

/-- The chart-pull integrand, summed only over `P`, is the chart coefficient
times the canonical chart component: a `Finset.mul_sum` rearrangement. -/
private lemma chartPull_integrand_eq_coeff_mul
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (u : TensorL2 r s g) (y : EuclN) :
    densityOnEuclid (I := I) g α y *
        (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
            ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) =
      ∑ Q : CompIdx E r s,
        chartPullCoeff (I := I) (M := M) g r s α Sg Q y *
          ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y := by
  classical
  have hlhs : densityOnEuclid (I := I) g α y *
        (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
          covChartMetricGram (I := I) (M := M) g r s α P Q y *
            tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
            ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) =
      ∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
        (densityOnEuclid (I := I) g α y *
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
            tensorComponentEuclid (I := I) (M := M) g r s Sg α P y) *
          ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun P _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    ring
  have hrhs : (∑ Q : CompIdx E r s,
        chartPullCoeff (I := I) (M := M) g r s α Sg Q y *
          ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) =
      ∑ Q : CompIdx E r s, ∑ P : CompIdx E r s,
        (densityOnEuclid (I := I) g α y *
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
            tensorComponentEuclid (I := I) (M := M) g r s Sg α P y) *
          ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y := by
    refine Finset.sum_congr rfl (fun Q _ => ?_)
    unfold chartPullCoeff
    rw [Finset.sum_mul]
  rw [hlhs, hrhs, Finset.sum_comm]

/-- Each `Q`-summand of the chart-pull integrand is Bochner-integrable: the
chart coefficient `chartPullCoeff g r s α Sg Q` is in `L²` and the canonical
chart component is in `L²`, so the pointwise product is in `L¹`. -/
private lemma chartPull_summand_integrable
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (u : TensorL2 r s g) (Q : CompIdx E r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    Integrable (fun y : EuclN =>
        chartPullCoeff (I := I) (M := M) g r s α Sg Q y *
          ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
              Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
      (chartL2Measure (I := I) (M := M) α) := by
  classical
  have hcoeff : MemLp (chartPullCoeff (I := I) (M := M) g r s α Sg Q) 2
      (chartL2Measure (I := I) (M := M) α) :=
    chartPullCoeff_memLp (I := I) (M := M) g r s α Sg Q hSg
  have hcomp : MemLp
      (((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
          Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ)) 2
      (chartL2Measure (I := I) (M := M) α) :=
    Lp.memLp _
  have hint := MemLp.integrable_mul hcoeff hcomp
  exact hint

/-- **The chart-pull integral as a finite sum of `L²` pairings.** The chart-pull
integral coupling the raw chart components of `Sg` to the canonical Euclidean
chart components `tensorL2ChartComponent` of an abstract `L²` element `u` is the
finite sum, over component multi-indices `Q`, of the `L²` inner product of the
chart coefficient `chartPullCoeff g r s α Sg Q` against
`tensorL2ChartComponent u α Q`. -/
private lemma chartPull_integral_eq_sum_inner
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) (u : TensorL2 r s g)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
              ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        ∂(volume : Measure EuclN) =
      ∑ Q : CompIdx E r s,
        (⟪chartPullCoeffLp (I := I) (M := M) g r s α Sg Q hSg,
            tensorL2ChartComponent (I := I) (M := M) g r s u α Q⟫_ℝ : ℝ) := by
  classical
  rw [show (∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
              ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        ∂(volume : Measure EuclN)) =
      ∫ y,
        densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
              ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        ∂(chartL2Measure (I := I) (M := M) α) from rfl]
  rw [show (fun y : EuclN =>
        densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
              ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)) =
      (fun y : EuclN =>
        ∑ Q : CompIdx E r s,
          chartPullCoeff (I := I) (M := M) g r s α Sg Q y *
            ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
                Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y) from by
    funext y
    exact chartPull_integrand_eq_coeff_mul (I := I) (M := M) g r s α Sg u y]
  rw [MeasureTheory.integral_finset_sum (Finset.univ : Finset (CompIdx E r s))
    (fun Q _ => chartPull_summand_integrable
      (I := I) (M := M) g r s α Sg u Q hSg)]
  refine Finset.sum_congr rfl (fun Q _ => ?_)
  rw [inner_chartPullCoeffLp_eq_integral (I := I) (M := M) g r s α Sg Q hSg]

/-- The left-hand side of the headline, `u ↦ ⟪(pouSmul g r s α Sg : TensorL2),
u⟫`, is continuous. -/
private lemma continuous_lhs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s) :
    Continuous (fun u : TensorL2 r s g =>
      (⟪(pouSmul (I := I) (M := M) g r s α Sg : TensorL2 r s g), u⟫_ℝ : ℝ)) :=
  (innerSL ℝ (pouSmul (I := I) (M := M) g r s α Sg :
    TensorL2 r s g)).continuous

/-- The right-hand side of the headline, as a function of the abstract `L²`
element `u`, is continuous: it is the finite sum over component multi-indices
`Q` of the continuous `L²` pairings of the chart coefficients. -/
private lemma continuous_rhs
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    Continuous (fun u : TensorL2 r s g =>
      ∑ Q : CompIdx E r s,
        (⟪chartPullCoeffLp (I := I) (M := M) g r s α Sg Q hSg,
            tensorL2ChartComponent (I := I) (M := M) g r s u α Q⟫_ℝ : ℝ)) :=
  continuous_finset_sum _ (fun Q _ =>
    continuous_chartPullCoeff_pairing (I := I) (M := M) g r s α Sg Q hSg)

/-- The headline holds on the dense subspace of smooth sections: for
`u = (T : TensorL2)` the global `L²` inner product of `pouSmul g r s α Sg`
against `(T : TensorL2)` equals the finite sum of `L²` pairings of the chart
coefficients against the canonical chart components of `(T : TensorL2)`. -/
private lemma headline_on_smooth
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source)
    (T : SmoothCcTensor g r s) :
    (⟪(pouSmul (I := I) (M := M) g r s α Sg : TensorL2 r s g),
        (T : TensorL2 r s g)⟫_ℝ : ℝ) =
      ∑ Q : CompIdx E r s,
        (⟪chartPullCoeffLp (I := I) (M := M) g r s α Sg Q hSg,
            tensorL2ChartComponent (I := I) (M := M) g r s
              (T : TensorL2 r s g) α Q⟫_ℝ : ℝ) := by
  classical
  rw [show (⟪(pouSmul (I := I) (M := M) g r s α Sg : TensorL2 r s g),
        (T : TensorL2 r s g)⟫_ℝ : ℝ) =
      (⟪pouSmul (I := I) (M := M) g r s α Sg, T⟫_ℝ : ℝ) from
    UniformSpace.Completion.inner_coe _ _]
  rw [SmoothCcTensor.inner_def]
  rw [tensorL2Inner_pouSmul_smooth_chart_pull (I := I) (M := M) g r s α Sg T]
  exact chartPull_integral_eq_sum_inner (I := I) (M := M) g r s α Sg
    (T : TensorL2 r s g) hSg

/-- The two sides of the headline, as functions of the abstract `L²` element,
are equal: they are continuous and agree on the dense range of the canonical
embedding of smooth sections into the `L²` Hilbert space. -/
private lemma headline_fun_eq
    (g : SmoothRiemannianMetric I M) (r s : ℕ) (α : M)
    (Sg : SmoothCcTensor g r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    (fun u : TensorL2 r s g =>
        (⟪(pouSmul (I := I) (M := M) g r s α Sg : TensorL2 r s g), u⟫_ℝ : ℝ)) =
      (fun u : TensorL2 r s g =>
        ∑ Q : CompIdx E r s,
          (⟪chartPullCoeffLp (I := I) (M := M) g r s α Sg Q hSg,
              tensorL2ChartComponent (I := I) (M := M) g r s u α Q⟫_ℝ : ℝ)) := by
  classical
  have hdense : DenseRange
      ((↑) : SmoothCcTensor g r s → UniformSpace.Completion (SmoothCcTensor g r s)) :=
    UniformSpace.Completion.denseRange_coe
  refine hdense.equalizer
    (continuous_lhs (I := I) (M := M) g r s α Sg)
    (continuous_rhs (I := I) (M := M) g r s α Sg hSg) ?_
  funext T
  exact headline_on_smooth (I := I) (M := M) g r s α Sg hSg T

/-- **Chart-pull of the `L²` tensor inner product against an abstract `L²`
element.**

Let `g` be a smooth Riemannian metric on a closed (compact, boundaryless) smooth
manifold `M`, let `α : M` be a chart center, fix tensor ranks `(r, s)`, let
`u : TensorL2 r s g` be an abstract element of the metric `L²` Hilbert space of
`(r, s)`-tensor fields, and let `Sg` be a smooth compactly-supported
`(r, s)`-tensor section supported inside the chart-`α` source.

Then the global `L²` inner product of the partition-of-unity-weighted concrete
section `pouSmul g r s α Sg = chartAtlasPOU I M α • Sg` against `u` equals the
chart-Euclidean integral

```
∫ y in chartTargetEuclid α,
  densityOnEuclid g α y · ∑_P ∑_Q covChartMetricGram g r s α P Q y ·
    tensorComponentEuclid g r s Sg α P y ·
    (tensorL2ChartComponent g r s u α Q : EuclN → ℝ) y
  ∂volume.
```

The integrand couples the *raw* Euclidean chart components
`tensorComponentEuclid` of `Sg` — through the chart-frame tensor-metric Gram
`covChartMetricGram` and the chart density `densityOnEuclid` — to the canonical
Euclidean chart components `tensorL2ChartComponent` of the abstract element `u`.
The partition-of-unity weight built into `tensorL2ChartComponent` is matched on
the concrete side by the weighting `pouSmul`.

The theorem is rank-polymorphic; a downstream consumer instantiates it at
`s := s + 1`. -/
theorem tensorL2Inner_pouSmul_tensorL2ChartComponent_pull
    (g : SmoothRiemannianMetric I M) (r s : ℕ)
    (α : M) (u : TensorL2 r s g) (Sg : SmoothCcTensor g r s)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    (⟪(pouSmul (I := I) (M := M) g r s α Sg : TensorL2 r s g), u⟫_ℝ : ℝ) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
              ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        ∂(volume : Measure EuclN) := by
  classical
  have hfun := headline_fun_eq (I := I) (M := M) g r s α Sg hSg
  have hu := congrFun hfun u
  rw [hu]
  exact (chartPull_integral_eq_sum_inner (I := I) (M := M) g r s α Sg u hSg).symm

section ElaborationTests

variable (g : SmoothRiemannianMetric I M) (r s : ℕ)

example (Sg T : SmoothCcTensor g r s) (α : M)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    tensorL2Inner (I := I) (M := M) g r s Sg.toFun T.toFun =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
              tensorComponentEuclid (I := I) (M := M) g r s T α Q y)
        ∂(volume : Measure EuclN) :=
  tensorL2Inner_chartSupported_chart_pull (I := I) (M := M) g r s Sg T α hSg

example (u : TensorL2 r s g) (Sg : SmoothCcTensor g r s) (α : M)
    (hSg : tsupport Sg.toFun ⊆ (chartAt H α).source) :
    (⟪(pouSmul (I := I) (M := M) g r s α Sg : TensorL2 r s g), u⟫_ℝ : ℝ) =
      ∫ y in chartTargetEuclid (I := I) (M := M) α,
        densityOnEuclid (I := I) g α y *
          (∑ P : CompIdx E r s, ∑ Q : CompIdx E r s,
            covChartMetricGram (I := I) (M := M) g r s α P Q y *
              tensorComponentEuclid (I := I) (M := M) g r s Sg α P y *
              ((tensorL2ChartComponent (I := I) (M := M) g r s u α Q :
                  Lp ℝ 2 (chartL2Measure (I := I) (M := M) α)) : EuclN → ℝ) y)
        ∂(volume : Measure EuclN) :=
  tensorL2Inner_pouSmul_tensorL2ChartComponent_pull
    (I := I) (M := M) g r s α u Sg hSg

end ElaborationTests

end TensorSpectral
end Parabolic
end Analysis
end DifferentialGeometry

end
