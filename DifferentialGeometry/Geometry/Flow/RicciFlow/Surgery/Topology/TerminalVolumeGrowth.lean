import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.EndpointAntitone
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TerminalVolume
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.ClosedSlabEndpoints

set_option autoImplicit false
noncomputable section

open Set Filter MeasureTheory
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff Topology ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab

universe u

variable {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s)

private local instance : MeasurableSpace P.Carrier := borel P.Carrier
private local instance : BorelSpace P.Carrier := ⟨rfl⟩
private local instance : MeasurableSpace G.terminalRegularOpen := borel G.terminalRegularOpen
private local instance : BorelSpace G.terminalRegularOpen := ⟨rfl⟩
private local instance : SigmaCompactSpace G.terminalRegularOpen :=
  isSigmaCompact_iff_sigmaCompactSpace.mp
    (DifferentialGeometry.Geometry.isSigmaCompact_of_isOpen ThreeModel
      G.terminalRegularOpen.isOpen)

theorem volume_le_exp_mul_initial {K : ℝ}
    (hscalar : ∀ t ∈ Ico a s, ∀ x : P.Carrier,
      -K ≤ metricScalarAt (G.flow.base.metric t) x) {t : ℝ} (ht : t ∈ Ico a s) :
    riemannianVolumeMeasure ThreeModel P.Carrier (G.flow.base.metric t) univ ≤
      ENNReal.ofReal (Real.exp (K * (t - a))) *
        riemannianVolumeMeasure ThreeModel P.Carrier (G.flow.base.metric a) univ := by
  obtain ⟨b, htb, hbs⟩ := exists_between ht.2
  let S := G.closedPrefix b (ht.1.trans_lt htb) hbs
  have hbound := S.exp_mul_volume_le_endpoint K
    (fun u hu x => hscalar u ⟨hu.1, hu.2.trans_lt hbs⟩ x)
    t ⟨ht.1, htb.le⟩
  change Real.exp (-K * t) *
      (riemannianVolumeMeasure ThreeModel P.Carrier (G.flow.base.metric t) univ).toReal ≤
    Real.exp (-K * a) *
      (riemannianVolumeMeasure ThreeModel P.Carrier (G.flow.base.metric a) univ).toReal at hbound
  have hmul := mul_le_mul_of_nonneg_left hbound (Real.exp_pos (K * t)).le
  have hcancel : Real.exp (K * t) * Real.exp (-K * t) = 1 := by
    rw [← Real.exp_add]
    ring_nf
    exact Real.exp_zero
  have hweight : Real.exp (K * t) * Real.exp (-K * a) = Real.exp (K * (t - a)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  rw [← mul_assoc, hcancel, one_mul, ← mul_assoc, hweight] at hmul
  let _ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (G.flow.base.metric a)
  let _ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (G.flow.base.metric t)
  apply (ENNReal.toReal_le_toReal (measure_ne_top _ _) ?_).mp
  · simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (Real.exp_pos _).le] using hmul
  · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)

theorem TerminalLimitMetric.volume_compact_le_exp_mul_initial
    (L : G.TerminalLimitMetric) {K : ℝ}
    (hscalar : ∀ t ∈ Ico a s, ∀ x : P.Carrier,
      -K ≤ metricScalarAt (G.flow.base.metric t) x)
    {F : Set G.terminalRegularOpen} (hF : IsCompact F) :
    riemannianVolumeMeasure ThreeModel G.terminalRegularOpen L.metric F ≤
      ENNReal.ofReal (Real.exp (K * (s - a))) *
        riemannianVolumeMeasure ThreeModel P.Carrier (G.flow.base.metric a) univ := by
  have hconv : Tendsto (fun t : ℝ =>
      ENNReal.ofReal (Real.exp (K * (t - a))) *
        riemannianVolumeMeasure ThreeModel P.Carrier (G.flow.base.metric a) univ)
      (𝓝[<] s) (𝓝 (ENNReal.ofReal (Real.exp (K * (s - a))) *
        riemannianVolumeMeasure ThreeModel P.Carrier (G.flow.base.metric a) univ)) := by
    let _ := riemannianVolumeMeasure_isFiniteMeasure_of_compactSpace (G.flow.base.metric a)
    apply ENNReal.Tendsto.mul_const _ (Or.inr (measure_ne_top _ _))
    apply Filter.Tendsto.mono_left _ nhdsWithin_le_nhds
    apply ContinuousAt.tendsto
    exact ENNReal.continuous_ofReal.continuousAt.comp (by fun_prop)
  apply le_of_tendsto_of_tendsto (L.tendsto_riemannianVolumeMeasure_compact hF) hconv
  filter_upwards [Ioo_mem_nhdsLT G.lt] with t ht
  have hmap := congrArg (fun μ : Measure P.Carrier => μ univ)
    (map_riemannianVolumeMeasure_restrictOpen (G.flow.base.metric t) G.terminalRegularOpen)
  rw [Measure.map_apply continuous_subtype_val.measurable MeasurableSet.univ,
    preimage_univ, Measure.restrict_apply_univ] at hmap
  exact ((measure_mono (subset_univ F)).trans hmap.le).trans
    ((measure_mono (subset_univ _)).trans (G.volume_le_exp_mul_initial hscalar ⟨ht.1.le, ht.2⟩))

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.OrientedThreeStage.IncomingSlab
