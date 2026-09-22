import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EventData
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.MetricConvergence
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import DifferentialGeometry.Analysis.Integration.Measure.OpenSubtype

noncomputable section

open Set Filter Manifold MeasureTheory
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u

variable {P : OrientedThreeStage.{u}} {a s : ℝ} {G : P.IncomingSlab a s}

private local instance : MeasurableSpace P.Carrier := borel P.Carrier
private local instance : BorelSpace P.Carrier := ⟨rfl⟩
private local instance : MeasurableSpace G.terminalRegularOpen := borel G.terminalRegularOpen
private local instance : BorelSpace G.terminalRegularOpen := ⟨rfl⟩
private local instance : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

theorem TerminalLimitMetric.tendsto_riemannianVolumeMeasure_compact
    (L : G.TerminalLimitMetric) {K : Set G.terminalRegularOpen} (hK : IsCompact K) :
    Tendsto (fun t => riemannianVolumeMeasure (I := ThreeModel) (M := G.terminalRegularOpen)
      ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen) K)
      (𝓝[<] s) (𝓝 (riemannianVolumeMeasure (I := ThreeModel) (M := G.terminalRegularOpen) L.metric K)) := by
  let : SecondCountableTopology P.Carrier :=
    ChartedSpace.secondCountable_of_sigmaCompact ThreeSpace P.Carrier
  let : LocallyCompactSpace G.terminalRegularOpen :=
    ChartedSpace.locallyCompactSpace ThreeSpace G.terminalRegularOpen
  let : IsFiniteMeasureOnCompacts (riemannianVolumeMeasure (I := ThreeModel) (M := G.terminalRegularOpen) L.metric) :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts L.metric
  have hmetric : TendstoUniformlyOn
      (fun t x => metricDerivNorm 0
        ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen) L.metric L.metric x)
      (fun _ => 0) (𝓝[<] s) K := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    obtain ⟨d, hd, hbound⟩ := L.converges K hK 0 ε hε
    filter_upwards [Ioo_mem_nhdsLT hd.2] with t ht
    intro x hx
    have hn : 0 ≤ metricDerivNorm 0
        ((G.flow.base.metric t).restrictOpen G.terminalRegularOpen) L.metric L.metric x :=
      Real.sqrt_nonneg _
    simpa only [Real.dist_eq, zero_sub, abs_neg, abs_of_nonneg hn] using hbound t ht x hx
  have hconv := tendsto_setLIntegral_of_dominated_convergence_of_metricDerivNorm
    (fun t => (G.flow.base.metric t).restrictOpen G.terminalRegularOpen) L.metric
    hK.measurableSet hmetric (fs := fun _ _ => (1 : ℝ≥0∞)) (f := fun _ => 1)
    (fun _ => 1)
    (Eventually.of_forall fun _ => aemeasurable_const)
    (Eventually.of_forall fun _ => Eventually.of_forall fun _ => le_rfl)
    (by simpa only [lintegral_const, one_mul, Measure.restrict_apply_univ] using
      hK.measure_lt_top.ne)
    (Eventually.of_forall fun _ => tendsto_const_nhds)
  simpa only [lintegral_const, one_mul, Measure.restrict_apply_univ] using hconv

theorem TerminalLimitMetric.volume_compact_le_of_eventually_volume_le
    (L : G.TerminalLimitMetric) {K : Set G.terminalRegularOpen} (hK : IsCompact K)
    {V : ℝ≥0∞}
    (hV : ∀ᶠ t in 𝓝[<] s,
      riemannianVolumeMeasure (I := ThreeModel) (M := P.Carrier) (G.flow.base.metric t) univ ≤ V) :
    riemannianVolumeMeasure (I := ThreeModel) (M := G.terminalRegularOpen) L.metric K ≤ V := by
  apply le_of_tendsto (L.tendsto_riemannianVolumeMeasure_compact hK)
  filter_upwards [hV] with t ht
  have hmap := congrArg (fun μ : Measure P.Carrier => μ univ)
    (map_riemannianVolumeMeasure_restrictOpen (G.flow.base.metric t) G.terminalRegularOpen)
  rw [Measure.map_apply continuous_subtype_val.measurable MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ] at hmap
  exact ((measure_mono (subset_univ K)).trans hmap.le).trans
    ((measure_mono (subset_univ _)).trans ht)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
