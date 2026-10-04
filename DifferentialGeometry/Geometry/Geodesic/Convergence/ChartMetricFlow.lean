import DifferentialGeometry.Geometry.Metric.Convergence.Coordinates.BilinearCoefficients
import DifferentialGeometry.Analysis.ODE.GeodesicLimits.MetricChristoffel
import DifferentialGeometry.Bundle.TangentChart

/-!
# Actual chart geodesic-flow convergence under covariant metric convergence

The chart equations and their coefficient convergence are derived from the same actual metrics.
The conclusion is local to a chart interval; supplying such intervals for lifted minimizing
segments is a separate geometric binding step.
-/

set_option autoImplicit false

noncomputable section

open Set Filter Bundle
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Geometry (pullbackMetricCoefficients)
open DifferentialGeometry.Analysis.ODE.GeodesicLimits
open DifferentialGeometry.MetricKoszul

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private local instance chartFlowDual : DifferentialGeometry.ContinuousDualEquiv E :=
  IsCoercive.continuousDualEquivOfFiniteDimensional
private local instance chartFlowDualGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance chartFlowDualSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
private local instance chartFlowBilinearGroup : NormedAddCommGroup (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance chartFlowBilinearSpace : NormedSpace ℝ (E →L[ℝ] E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem tendstoUniformlyOn_geodesicFlow_chart_of_metricCP
    (g : ℕ → SmoothRiemannianMetric I M) (gInf gRef : SmoothRiemannianMetric I M)
    (hconv : ∀ C : Set M, IsCompact C → MetricCPConvergenceOn C 1 g gInf gRef)
    (q : TangentBundle I M) (p : ℕ → TangentBundle I M) (pInf : TangentBundle I M)
    {t0 t1 : ℝ}
    (hdom : ∀ i, ∀ t ∈ Icc t0 t1, (p i, t) ∈ (g i).geodesicFlowDomain)
    (hdomInf : ∀ t ∈ Icc t0 t1, (pInf, t) ∈ gInf.geodesicFlowDomain)
    (hchart : ∀ i, ∀ t ∈ Icc t0 t1,
      ((g i).geodesicFlow (p i) t).proj ∈ (chartAt H q.proj).source)
    (hchartInf : ∀ t ∈ Icc t0 t1,
      (gInf.geodesicFlow pInf t).proj ∈ (chartAt H q.proj).source)
    (hinit : Tendsto (fun i => extChartAt I.tangent q ((g i).geodesicFlow (p i) t0))
      atTop (𝓝 (extChartAt I.tangent q (gInf.geodesicFlow pInf t0)))) :
    TendstoUniformlyOn
      (fun i t => extChartAt I.tangent q ((g i).geodesicFlow (p i) t))
      (fun t => extChartAt I.tangent q (gInf.geodesicFlow pInf t)) atTop (Icc t0 t1) := by
  let U := (extChartAt I q.proj).target
  have hU : IsOpen U := isOpen_extChartAt_target q.proj
  let b (G : SmoothRiemannianMetric I M) :=
    pullbackMetricCoefficients G (extChartAt I q.proj).symm
  have hb (G : SmoothRiemannianMetric I M) : ContDiffOn ℝ ∞ (b G) U :=
    contDiffOn_pullback_metric_coefficients G hU (contMDiffOn_extChartAt_symm q.proj)
  have hco : ∀ y ∈ U, IsCoercive (b gInf y) := by
    intro y hy
    apply DifferentialGeometry.Analysis.isCoercive_of_pos_diagonal
    intro v hv
    apply pullbackMetricCoefficients_pos gInf
    · let Phi := (DifferentialGeometry.PartialDiffeomorph.extChartAt I ∞ q.proj).symm
      exact (Phi.isLocalDiffeomorphAt _ _ _ hy
        |>.mfderivToContinuousLinearEquiv (by simp)).injective
    · exact hv
  have hbc : ∀ K : Set E, IsCompact K → K ⊆ U → MapCPConvergenceOn K 1
      (fun i => b (g i)) (b gInf) := by
    intro K hK hKU
    apply mapCPConvergence_chartBilinear_of_metricCP g gInf gRef q.proj hK hKU 1
    exact hconv _ (hK.image_of_continuousOn
      ((continuousOn_extChartAt_symm q.proj).mono hKU))
  let z (G : SmoothRiemannianMetric I M) (v : TangentBundle I M) (t : ℝ) :=
    extChartAt I.tangent q (G.geodesicFlow v t)
  have hz (G : SmoothRiemannianMetric I M) (v : TangentBundle I M) (t : ℝ)
      (ht : (v, t) ∈ G.geodesicFlowDomain)
      (hc : (G.geodesicFlow v t).proj ∈ (chartAt H q.proj).source) :
      HasDerivWithinAt (z G v) (metricSpray (b G) (z G v t)) (Icc t0 t1) t :=
    (G.hasDerivAt_geodesicFlow_chart (r := ⊤) le_top ht q hc).hasDerivWithinAt
  have hcU : ∀ t ∈ Icc t0 t1, (z gInf pInf t).1 ∈ U := by
    intro t ht
    rw [TangentBundle.extChartAt_tangent_apply_fst]
    exact (extChartAt I q.proj).map_source
      (by simpa only [extChartAt_source] using hchartInf t ht)
  obtain ⟨hpos, hvel⟩ := tendstoUniformlyOn_of_metric_tendsto hU
    (fun i => b (g i)) (b gInf) (fun i => (hb (g i)).of_le (by simp))
    ((hb gInf).of_le (by simp)) hco hbc
    (fun t => (z gInf pInf t).1) (fun t => (z gInf pInf t).2) hcU
    (fun t ht => by simpa only [HasDerivWithinAt, metricSpray,
      ContinuousLinearMap.comp_toSpanSingleton,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.toSpanSingleton_apply, one_smul] using (hz gInf pInf t (hdomInf t ht)
      (hchartInf t ht)).fst.hasDerivAtFilter)
    (fun t ht => by simpa only [HasDerivWithinAt, metricSpray,
      ContinuousLinearMap.comp_toSpanSingleton,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.toSpanSingleton_apply, one_smul] using (hz gInf pInf t (hdomInf t ht)
      (hchartInf t ht)).snd.hasDerivAtFilter)
    (fun i t => (z (g i) (p i) t).1) (fun i t => (z (g i) (p i) t).2)
    (fun i t ht => by simpa only [HasDerivWithinAt, metricSpray,
      ContinuousLinearMap.comp_toSpanSingleton,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.toSpanSingleton_apply, one_smul] using (hz (g i) (p i) t (hdom i t ht)
      (hchart i t ht)).fst.hasDerivAtFilter)
    (fun i t ht => by simpa only [HasDerivWithinAt, metricSpray,
      ContinuousLinearMap.comp_toSpanSingleton,
      ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd',
      ContinuousLinearMap.toSpanSingleton_apply, one_smul] using (hz (g i) (p i) t (hdom i t ht)
      (hchart i t ht)).snd.hasDerivAtFilter)
    (continuous_fst.tendsto _ |>.comp hinit) (continuous_snd.tendsto _ |>.comp hinit)
  rw [Metric.tendstoUniformlyOn_iff] at hpos hvel ⊢
  intro epsilon hepsilon
  filter_upwards [hpos epsilon hepsilon, hvel epsilon hepsilon] with i hi hv t ht
  exact max_lt (hi t ht) (hv t ht)

theorem realZero_geodesicFlow_chart_converges (T : ℝ) :
    let g := euclideanMetric (E := ℝ)
    let p : TangentBundle 𝓘(ℝ, ℝ) ℝ := ⟨0, 0⟩
    TendstoUniformlyOn
      (fun (_i : ℕ) t => extChartAt (𝓘(ℝ, ℝ)).tangent p (g.geodesicFlow p t))
      (fun t => extChartAt (𝓘(ℝ, ℝ)).tangent p (g.geodesicFlow p t)) atTop (Icc 0 T) := by
  let g := euclideanMetric (E := ℝ)
  let p : TangentBundle 𝓘(ℝ, ℝ) ℝ := ⟨0, 0⟩
  have hdom (t : ℝ) : (p, t) ∈ g.geodesicFlowDomain :=
    g.mem_geodesicFlowDomain_zeroSection 0 t
  have hchart (t : ℝ) : (g.geodesicFlow p t).proj ∈ (chartAt ℝ p.proj).source := by
    simp
  exact tendstoUniformlyOn_geodesicFlow_chart_of_metricCP (fun _i => g) g g
    (fun C hC epsilon hepsilon => ⟨0, fun i hi => by
      rw [metricDerivNormSupOn_self]; exact hepsilon⟩) p (fun _i => p) p
    (fun i t ht => hdom t) (fun t ht => hdom t)
    (fun i t ht => hchart t) (fun t ht => hchart t) tendsto_const_nhds

end DifferentialGeometry.Geometry.Riemannian.Geodesic
