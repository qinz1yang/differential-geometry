import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.IntegralConvergence
import DifferentialGeometry.Analysis.Integration.Measure.Chart.PartitionOfUnity.Integral
import Mathlib.Topology.ContinuousMap.CompactlySupported
import Mathlib.Topology.UniformSpace.LocallyUniformConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.Map
import Mathlib.MeasureTheory.Measure.WithDensity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.PointedCutoffs
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Invariance
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Topology.Instances.ENNReal.Lemmas
import DifferentialGeometry.Analysis.Integration.Measure.TightConvergence
import Mathlib.MeasureTheory.Integral.IntegrableOn
import DifferentialGeometry.Analysis.Integration.Measure.IntegralConvergence
import DifferentialGeometry.Analysis.Integration.Measure.Riemannian.Properties
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineExistence
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite

section

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter MeasureTheory Set Manifold
open DifferentialGeometry.Integral.Measure
open scoped CompactlySupported ContDiff Manifold _root_.Topology ENNReal

universe u uE uH

section ChartPartition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private abbrev indices (f : C_c(M, ℝ)) : Finset M :=
  (chartAtlasPOU I M).toPartitionOfUnity.fintsupportOn
    (tsupport (f : M → ℝ)) f.hasCompactSupport

private abbrev carrier (f : C_c(M, ℝ)) (i : M) : Set M :=
  tsupport ((chartAtlasPOU I M) i) ∩ tsupport (f : M → ℝ)

private abbrev chartImage (f : C_c(M, ℝ)) (i : M) : Set E :=
  extChartAt I i '' carrier (I := I) f i

private theorem carrier_compact (f : C_c(M, ℝ)) (i : M) :
    IsCompact (carrier (I := I) f i) :=
  f.hasCompactSupport.of_isClosed_subset
    ((isClosed_tsupport _).inter (isClosed_tsupport _)) inter_subset_right

private theorem carrier_subset_source (f : C_c(M, ℝ)) (i : M) :
    carrier (I := I) f i ⊆ (extChartAt I i).source := by
  intro y hy
  rw [extChartAt_source]
  exact chartAtlasPOU_isSubordinate I M i hy.1

private theorem chartImage_compact (f : C_c(M, ℝ)) (i : M) :
    IsCompact (chartImage (I := I) f i) :=
  (carrier_compact f i).image_of_continuousOn
    ((continuousOn_extChartAt i).mono (carrier_subset_source f i))

private theorem chartImage_subset_target (f : C_c(M, ℝ)) (i : M) :
    chartImage (I := I) f i ⊆ (extChartAt I i).target := by
  rintro _ ⟨y, hy, rfl⟩
  exact (extChartAt I i).map_source (carrier_subset_source f i hy)

private theorem inverse_chart_mem_carrier (f : C_c(M, ℝ)) (i : M)
    {z : E} (hz : z ∈ chartImage (I := I) f i) :
    (extChartAt I i).symm z ∈ carrier (I := I) f i := by
  obtain ⟨x, hx, rfl⟩ := hz
  rw [(extChartAt I i).left_inv (carrier_subset_source f i hx)]
  exact hx

end ChartPartition

section Flow

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq.{u, uE, uH} (I := I)}
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedFlowData.topology PointedFlowData.charted PointedFlowData.smooth
  PointedFlowData.t2 PointedFlowData.sigmaCompact

private local instance : MeasurableSpace P.M := borel P.M
private local instance : BorelSpace P.M := ⟨rfl⟩
private local instance (k : ℕ) : MeasurableSpace (X.term k).M := borel (X.term k).M
private local instance (k : ℕ) : BorelSpace (X.term k).M := ⟨rfl⟩
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

theorem FlowMetricConvergenceData.tendsto_lintegral_map_density_of_hasCompactSupport
    (Phi : PointedCGHMaps X P subseq) (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Phi) (hSrc : SourceIsSigmaCompact Phi) (hTgt : TargetIsSigmaCompact Phi)
    (beta psi : ℝ) (co : FlowMetricConvergenceData Phi R bf hSrc hTgt beta psi)
    (t : ℝ) (ht : t ∈ Icc beta psi)
    (density : ∀ k, (X.term (subseq (co.φ k))).M → ℝ)
    (densityLim : P.M → ℝ) (hDensity : ∀ k, Measurable (density k))
    (hDensityLim : Continuous densityLim)
    (hconv : TendstoLocallyUniformly
      (fun k y => density k (Phi.map (co.φ k) y)) densityLim atTop)
    (f : C_c(P.M, ℝ)) :
    Tendsto
      (fun k => ∫⁻ y, ENNReal.ofReal (f y)
        ∂Measure.map (Phi.partialDiffeomorph (co.φ k)).symm
          (((riemannianVolumeMeasure (I := I) (M := (X.term (subseq (co.φ k))).M)
            ((X.term (subseq (co.φ k))).S.base.metric t)).withDensity
            (fun y => ENNReal.ofReal (density k y))).restrict
              (Phi.partialDiffeomorph (co.φ k)).target))
      atTop (𝓝 (∫⁻ y, ENNReal.ofReal (f y)
        ∂(riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf t)).withDensity
          (fun y => ENNReal.ofReal (densityLim y)))) := by
  classical
  let K := tsupport (f : P.M → ℝ)
  have hK : IsCompact K := f.hasCompactSupport
  have hUniform : TendstoUniformlyOn
      (fun k y => density k (Phi.map (co.φ k) y)) densityLim atTop K :=
    (tendstoLocallyUniformlyOn_iff_tendstoUniformlyOn_of_compact hK).mp
      hconv.tendstoLocallyUniformlyOn
  obtain ⟨M, hM⟩ := hK.bddAbove_image hDensityLim.continuousOn
  let C : NNReal := Real.toNNReal (max M 0 + 1)
  have hBound : ∀ᶠ k in atTop, ∀ y ∈ K,
      ENNReal.ofReal (density k (Phi.map (co.φ k) y)) ≤ (C : ENNReal) := by
    filter_upwards [(Metric.tendstoUniformlyOn_iff.mp hUniform) 1 zero_lt_one] with k hk
    intro y hy
    have hdist : |density k (Phi.map (co.φ k) y) - densityLim y| < 1 := by
      simpa only [Real.dist_eq, abs_sub_comm] using hk y hy
    change ENNReal.ofReal (density k (Phi.map (co.φ k) y)) ≤
      ENNReal.ofReal (max M 0 + 1)
    apply ENNReal.ofReal_le_ofReal
    linarith [le_abs_self (density k (Phi.map (co.φ k) y) - densityLim y),
      hM ⟨y, hy, rfl⟩, le_max_left M (0 : ℝ)]
  obtain ⟨k0, hk0⟩ := Phi.source_subset hK
  have hSource : ∀ᶠ k in atTop, K ⊆ Phi.source (co.φ k) := by
    filter_upwards [eventually_ge_atTop k0] with k hk
    exact hk0 (co.φ k) (hk.trans (co.strictMono.id_le k))
  let w : P.M → E → ENNReal := fun i z => ENNReal.ofReal
    ((chartAtlasPOU I P.M) i ((extChartAt I i).symm z) * f ((extChartAt I i).symm z))
  let sourceTerm : P.M → ℕ → ENNReal := fun i k =>
    ∫⁻ y in Phi.chartParametrization (co.φ k) i '' chartImage (I := I) f i,
      w i ((Phi.chartParametrization (co.φ k) i).symm y) * ENNReal.ofReal (density k y)
        ∂riemannianVolumeMeasure (I := I) (M := (X.term (subseq (co.φ k))).M)
            ((X.term (subseq (co.φ k))).S.base.metric t)
  let limitTerm : P.M → ENNReal := fun i =>
    ∫⁻ y in (extChartAt I i).symm '' chartImage (I := I) f i,
      w i (extChartAt I i y) * ENNReal.ofReal (densityLim y)
        ∂riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf t)
  have hTerm : ∀ i ∈ indices (I := I) f,
      Tendsto (sourceTerm i) atTop (𝓝 (limitTerm i)) := by
    intro i _
    have hB := chartImage_compact (I := I) f i
    have hBt := chartImage_subset_target (I := I) f i
    have hWeight : ContinuousOn
        (fun z => (chartAtlasPOU I P.M) i ((extChartAt I i).symm z) *
          f ((extChartAt I i).symm z)) (chartImage (I := I) f i) :=
      ((((chartAtlasPOU I P.M) i).contMDiff.continuous.mul f.continuous).comp_continuousOn
        (continuousOn_extChartAt_symm i)).mono hBt
    have hw : AEMeasurable (w i) ((modelHaar (E := E)).restrict (chartImage (I := I) f i)) :=
      (ENNReal.continuous_ofReal.comp_continuousOn hWeight).aemeasurable hB.measurableSet
    have hwInt : ∫⁻ z in chartImage (I := I) f i, w i z ∂modelHaar < ⊤ :=
      (hWeight.integrableOn_compact hB (μ := modelHaar)).lintegral_lt_top
    have hMeas : ∀ᶠ k in atTop, AEMeasurable
        (fun z => ENNReal.ofReal (density k
          (Phi.map (co.φ k) ((extChartAt I i).symm z))))
        ((modelHaar (E := E)).restrict (chartImage (I := I) f i)) := by
      filter_upwards [hSource] with k hk
      have hChartSource : chartImage (I := I) f i ⊆
          (Phi.chartParametrization (co.φ k) i).source := by
        intro z hz
        exact ⟨hBt hz, hk (inverse_chart_mem_carrier f i hz).2⟩
      have hmap := ((Phi.chartParametrization (co.φ k) i).toOpenPartialHomeomorph.continuousOn.mono
        hChartSource).aemeasurable (μ := modelHaar) hB.measurableSet
      exact (hDensity k).ennreal_ofReal.comp_aemeasurable hmap
    have hLim : ∀ᵐ z ∂((modelHaar (E := E)).restrict (chartImage (I := I) f i)),
        Tendsto (fun k => density k (Phi.map (co.φ k) ((extChartAt I i).symm z)))
          atTop (𝓝 (densityLim ((extChartAt I i).symm z))) := by
      filter_upwards [ae_restrict_mem hB.measurableSet] with z hz
      exact hUniform.tendsto_at (inverse_chart_mem_carrier f i hz).2
    have hBd : ∀ᶠ k in atTop,
        ∀ᵐ z ∂((modelHaar (E := E)).restrict (chartImage (I := I) f i)),
        ENNReal.ofReal (density k (Phi.map (co.φ k) ((extChartAt I i).symm z))) ≤
          (C : ENNReal) := by
      filter_upwards [hBound] with k hk
      filter_upwards [ae_restrict_mem hB.measurableSet] with z hz
      exact hk _ (inverse_chart_mem_carrier f i hz).2
    exact FlowMetricConvergenceData.tendsto_lintegral_mul_density_chartParametrization
      Phi R bf hSrc hTgt beta psi co t i density densityLim ht hBt hB
      (w i) hw hwInt hMeas hLim C hBd
  have hfSupport : Function.support (fun y => ENNReal.ofReal (f y)) ⊆ K := by
    intro y hy
    apply subset_tsupport _
    intro hz
    exact hy (by simp only [hz, ENNReal.ofReal_zero])
  have hSourceSum : ∀ᶠ k in atTop,
      (∫⁻ y, ENNReal.ofReal (f y)
        ∂Measure.map (Phi.partialDiffeomorph (co.φ k)).symm
          (((riemannianVolumeMeasure (I := I) (M := (X.term (subseq (co.φ k))).M)
            ((X.term (subseq (co.φ k))).S.base.metric t)).withDensity
            (fun y => ENNReal.ofReal (density k y))).restrict
              (Phi.partialDiffeomorph (co.φ k)).target)) =
        ∑ i ∈ indices (I := I) f, sourceTerm i k := by
    filter_upwards [hSource] with k hk
    have h := OpenPartialHomeomorph.lintegral_map_symm_withDensity_eq_sum_chartAtlasPOU
      (I := I) (Phi.partialDiffeomorph (co.φ k)).toOpenPartialHomeomorph
      (riemannianVolumeMeasure (I := I) (M := (X.term (subseq (co.φ k))).M)
            ((X.term (subseq (co.φ k))).S.base.metric t))
      (fun y => ENNReal.ofReal (density k y)) hK (fun y => ENNReal.ofReal (f y))
      f.continuous.measurable.ennreal_ofReal hfSupport (fun _ _ _ hy => hk hy.2)
      (fun _ _ => (hDensity k).ennreal_ofReal.aemeasurable)
    simpa only [sourceTerm, w, indices, chartImage, carrier, K,
      PointedCGHMaps.chartParametrization,
      ENNReal.ofReal_mul ((chartAtlasPOU I P.M).nonneg _ _)] using! h
  have hLimitSum :
      (∫⁻ y, ENNReal.ofReal (f y)
        ∂(riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf t)).withDensity
          (fun y => ENNReal.ofReal (densityLim y))) =
        ∑ i ∈ indices (I := I) f, limitTerm i := by
    have h := lintegral_withDensity_eq_sum_chartAtlasPOU
      (I := I) (riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf t))
      (fun y => ENNReal.ofReal (densityLim y)) hK (fun y => ENNReal.ofReal (f y))
      f.continuous.measurable.ennreal_ofReal hfSupport
      (fun _ _ => hDensityLim.measurable.ennreal_ofReal.aemeasurable)
    simpa only [limitTerm, w, indices, chartImage, carrier, K,
      ENNReal.ofReal_mul ((chartAtlasPOU I P.M).nonneg _ _)] using! h
  rw [hLimitSum]
  exact (tendsto_finsetSum _ hTerm).congr' (Filter.EventuallyEq.symm hSourceSum)

end Flow

end DifferentialGeometry.CheegerGromovCompactness

end

end

section

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter MeasureTheory Set
open DifferentialGeometry.Integral.Measure
open scoped CompactlySupported ContDiff Manifold _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq.{u, uE, uH} (I := I)}
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedFlowData.topology PointedFlowData.charted PointedFlowData.smooth
  PointedFlowData.t2 PointedFlowData.sigmaCompact

private local instance : MeasurableSpace P.M := borel P.M
private local instance : BorelSpace P.M := ⟨rfl⟩
private local instance (k : ℕ) : MeasurableSpace (X.term k).M := borel (X.term k).M
private local instance (k : ℕ) : BorelSpace (X.term k).M := ⟨rfl⟩

theorem FlowMetricConvergenceData.tendsto_lintegral_mul_density_of_hasCompactSupport
    (Phi : PointedCGHMaps X P subseq) (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Phi) (hSrc : SourceIsSigmaCompact Phi) (hTgt : TargetIsSigmaCompact Phi)
    (beta psi : ℝ) (co : FlowMetricConvergenceData Phi R bf hSrc hTgt beta psi)
    (t : ℝ) (ht : t ∈ Icc beta psi)
    (density : ∀ k, (X.term (subseq (co.φ k))).M → ℝ)
    (densityLim : P.M → ℝ) (hDensity : ∀ k, Measurable (density k))
    (hDensityLim : Continuous densityLim)
    (hconv : TendstoLocallyUniformly
      (fun k y => density k (Phi.map (co.φ k) y)) densityLim atTop)
    (f : C_c(P.M, ℝ)) :
    Tendsto
      (fun k => ∫⁻ y in (Phi.partialDiffeomorph (co.φ k)).target,
        ENNReal.ofReal (f ((Phi.partialDiffeomorph (co.φ k)).symm y)) *
          ENNReal.ofReal (density k y)
          ∂riemannianVolumeMeasure (I := I) (M := (X.term (subseq (co.φ k))).M)
            ((X.term (subseq (co.φ k))).S.base.metric t))
      atTop (𝓝 (∫⁻ y, ENNReal.ofReal (f y) * ENNReal.ofReal (densityLim y)
        ∂riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf t))) := by
  have hTest : Measurable (fun y : P.M => ENNReal.ofReal (f y)) :=
    f.continuous.measurable.ennreal_ofReal
  have hSource (k : ℕ) :
      (∫⁻ y, ENNReal.ofReal (f y)
        ∂Measure.map (Phi.partialDiffeomorph (co.φ k)).symm
          (((riemannianVolumeMeasure (I := I) (M := (X.term (subseq (co.φ k))).M)
            ((X.term (subseq (co.φ k))).S.base.metric t)).withDensity
              (fun y => ENNReal.ofReal (density k y))).restrict
                (Phi.partialDiffeomorph (co.φ k)).target)) =
      ∫⁻ y in (Phi.partialDiffeomorph (co.φ k)).target,
        ENNReal.ofReal (f ((Phi.partialDiffeomorph (co.φ k)).symm y)) *
          ENNReal.ofReal (density k y)
          ∂riemannianVolumeMeasure (I := I) (M := (X.term (subseq (co.φ k))).M)
            ((X.term (subseq (co.φ k))).S.base.metric t) := by
    let e := Phi.partialDiffeomorph (co.φ k)
    let μ := riemannianVolumeMeasure (I := I) (M := (X.term (subseq (co.φ k))).M)
      ((X.term (subseq (co.φ k))).S.base.metric t)
    have htarget : MeasurableSet e.target := e.toOpenPartialHomeomorph.open_target.measurableSet
    have hinv : AEMeasurable e.symm
        ((μ.withDensity (fun y => ENNReal.ofReal (density k y))).restrict e.target) :=
      e.toOpenPartialHomeomorph.continuousOn_symm.aemeasurable htarget
    change (∫⁻ y, ENNReal.ofReal (f y)
        ∂Measure.map e.symm
          ((μ.withDensity (fun y => ENNReal.ofReal (density k y))).restrict e.target)) =
      ∫⁻ y in e.target, ENNReal.ofReal (f (e.symm y)) *
        ENNReal.ofReal (density k y) ∂μ
    rw [lintegral_map' hTest.aemeasurable hinv, restrict_withDensity htarget]
    have hinvBase : AEMeasurable e.symm (μ.restrict e.target) :=
      e.toOpenPartialHomeomorph.continuousOn_symm.aemeasurable htarget
    have hIntegrand : AEMeasurable (fun y => ENNReal.ofReal (f (e.symm y)))
        (μ.restrict e.target) :=
      hTest.aemeasurable.comp_aemeasurable hinvBase
    rw [lintegral_withDensity_eq_lintegral_mul₀
      (hDensity k).ennreal_ofReal.aemeasurable hIntegrand]
    exact lintegral_congr fun y =>
      mul_comm (ENNReal.ofReal (density k y)) (ENNReal.ofReal (f (e.symm y)))
  have hLimit :
      (∫⁻ y, ENNReal.ofReal (f y)
        ∂(riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf t)).withDensity
          (fun y => ENNReal.ofReal (densityLim y))) =
      ∫⁻ y, ENNReal.ofReal (f y) * ENNReal.ofReal (densityLim y)
        ∂riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf t) := by
    rw [lintegral_withDensity_eq_lintegral_mul₀
      hDensityLim.measurable.ennreal_ofReal.aemeasurable hTest.aemeasurable]
    exact lintegral_congr fun y =>
      mul_comm (ENNReal.ofReal (densityLim y)) (ENNReal.ofReal (f y))
  have h := FlowMetricConvergenceData.tendsto_lintegral_map_density_of_hasCompactSupport
    Phi R bf hSrc hTgt beta psi co t ht density densityLim hDensity hDensityLim hconv f
  simp_rw [hSource] at h
  rw [hLimit] at h
  exact h

end DifferentialGeometry.CheegerGromovCompactness

end

end

section

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq.{u, uE, uH} (I := I)}
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedFlowData.topology PointedFlowData.charted PointedFlowData.smooth
  PointedFlowData.t2 PointedFlowData.sigmaCompact

private local instance densityTailSourceMeasurable (i : ℕ) :
    MeasurableSpace (X.term i).M := borel (X.term i).M
private local instance densityTailSourceBorel (i : ℕ) :
    BorelSpace (X.term i).M := ⟨rfl⟩

theorem HalfLineMetricConvergenceData.tendsto_lintegral_compl_target_of_ball_tails
    (Phi : PointedCGHMaps X P phi) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    {t : ℝ} (ht : t ≤ 0)
    (hcomplete : MetricComplete (I := I)
      ({ P with metric := co.gInf t } : PointedRiemannianManifold (I := I)))
    (z : P.M) (density : ∀ k, (X.term (phi (co.φ k))).M → ℝ≥0∞)
    (htail : ∀ ε : ℝ≥0∞, 0 < ε → ∃ s : ℝ, 0 ≤ s ∧ ∀ᶠ k in atTop,
      (∫⁻ y in (riemannianClosedBallOf
          ((X.term (phi (co.φ k))).S.base.metric t) (Phi.map (co.φ k) z) s)ᶜ,
        density k y ∂riemannianVolumeMeasure (I := I) (M := (X.term (phi (co.φ k))).M)
          ((X.term (phi (co.φ k))).S.base.metric t)) < ε) :
    Tendsto (fun k =>
      ∫⁻ y in (Phi.partialDiffeomorph (co.φ k)).targetᶜ,
        density k y ∂riemannianVolumeMeasure (I := I) (M := (X.term (phi (co.φ k))).M)
          ((X.term (phi (co.φ k))).S.base.metric t)) atTop (𝓝 0) := by
  apply ENNReal.tendsto_nhds_zero.mpr
  intro ε hε
  obtain ⟨s, hs, hstail⟩ := htail ε hε
  obtain ⟨_, _, _, hcapture⟩ :=
    co.exists_inverse_capture_cutoff_at Phi ht hcomplete z ∅ isCompact_empty hs
      (show (0 : ℝ) < 1 by norm_num)
  filter_upwards [hstail, hcapture] with k hkTail hkCapture
  apply le_trans _ hkTail.le
  apply lintegral_mono_set
  exact compl_subset_compl.mpr (fun y hy => (hkCapture.2 y hy).1)

end DifferentialGeometry.CheegerGromovCompactness

end

end

section

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
open scoped Manifold ContDiff CompactlySupported Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq.{u, uE, uH} (I := I)}
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle
  PointedFlowData.topology PointedFlowData.charted PointedFlowData.smooth
  PointedFlowData.t2 PointedFlowData.sigmaCompact

private local instance : MeasurableSpace P.M := borel P.M
private local instance : BorelSpace P.M := ⟨rfl⟩
private local instance (j : ℕ) : MeasurableSpace (X.term j).M := borel (X.term j).M
private local instance (j : ℕ) : BorelSpace (X.term j).M := ⟨rfl⟩

theorem HalfLineMetricConvergenceData.exists_isCompact_inverse_map_compl_le_of_ball_tails
    (Phi : PointedCGHMaps X P phi) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    {t : ℝ} (ht : t ≤ 0)
    (hcomplete : MetricComplete (I := I)
      ({ P with metric := co.gInf t } : PointedRiemannianManifold (I := I)))
    (z : P.M) (density : ∀ k : ℕ, (X.term (phi (co.φ k))).M → ℝ≥0∞)
    (htails : ∀ epsilon : ℝ≥0∞, 0 < epsilon → ∃ r : ℝ, 0 ≤ r ∧ ∀ᶠ k in atTop,
      ((riemannianVolumeMeasure (I := I) (M := (X.term (phi (co.φ k))).M)
        ((X.term (phi (co.φ k))).S.base.metric t)).withDensity (density k))
        (riemannianClosedBallOf ((X.term (phi (co.φ k))).S.base.metric t)
          (Phi.map (co.φ k) z) r)ᶜ ≤ epsilon) :
    ∀ epsilon : ℝ≥0∞, 0 < epsilon → ∃ K : Set P.M, IsCompact K ∧ ∀ᶠ k in atTop,
      Measure.map (Phi.partialDiffeomorph (co.φ k)).symm
        (((riemannianVolumeMeasure (I := I) (M := (X.term (phi (co.φ k))).M)
          ((X.term (phi (co.φ k))).S.base.metric t)).withDensity (density k)).restrict
            (Phi.partialDiffeomorph (co.φ k)).target) Kᶜ ≤ epsilon := by
  intro epsilon hepsilon
  obtain ⟨r, hr, htail⟩ := htails epsilon hepsilon
  obtain ⟨f, _hf, _hone, hcapture⟩ :=
    co.exists_inverse_capture_cutoff_at Phi ht hcomplete z ∅ isCompact_empty hr
      (show (0 : ℝ) < 1 by norm_num)
  refine ⟨tsupport (f : P.M → ℝ), f.hasCompactSupport, ?_⟩
  filter_upwards [hcapture, htail] with k hk hktail
  let mu := (riemannianVolumeMeasure (I := I) (M := (X.term (phi (co.φ k))).M)
    ((X.term (phi (co.φ k))).S.base.metric t)).withDensity (density k)
  have hF : AEMeasurable (Phi.partialDiffeomorph (co.φ k)).symm
      (mu.restrict (Phi.partialDiffeomorph (co.φ k)).target) :=
    (Phi.partialDiffeomorph (co.φ k)).contMDiffOn_invFun.continuousOn.aemeasurable
      (Phi.partialDiffeomorph (co.φ k)).open_target.measurableSet
  have hBK : MapsTo (Phi.partialDiffeomorph (co.φ k)).symm
      (riemannianClosedBallOf ((X.term (phi (co.φ k))).S.base.metric t)
        (Phi.map (co.φ k) z) r ∩ (Phi.partialDiffeomorph (co.φ k)).target)
      (tsupport (f : P.M → ℝ)) := by
    intro y hy
    have hone : f ((Phi.partialDiffeomorph (co.φ k)).symm y) = 1 :=
      (hk.2 y hy.1).2.2.2
    exact subset_tsupport _ (by
      change f ((Phi.partialDiffeomorph (co.φ k)).symm y) ≠ 0
      rw [hone]
      exact one_ne_zero)
  exact (DifferentialGeometry.Analysis.Measure.map_restrict_compl_le_of_mapsTo mu
    f.hasCompactSupport.measurableSet hF hBK).trans hktail

end DifferentialGeometry.CheegerGromovCompactness

end

end

section

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter MeasureTheory Set
open DifferentialGeometry.Integral.Measure
open scoped CompactlySupported ContDiff Manifold _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq.{u, uE, uH} (I := I)}
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedFlowData.topology PointedFlowData.charted PointedFlowData.smooth
  PointedFlowData.t2 PointedFlowData.sigmaCompact

private local instance : MeasurableSpace P.M := borel P.M
private local instance : BorelSpace P.M := ⟨rfl⟩
private local instance (k : ℕ) : MeasurableSpace (X.term k).M := borel (X.term k).M
private local instance (k : ℕ) : BorelSpace (X.term k).M := ⟨rfl⟩

theorem FlowMetricConvergenceData.tendsto_integral_map_density_of_hasCompactSupport
    (Phi : PointedCGHMaps X P subseq) (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Phi) (hSrc : SourceIsSigmaCompact Phi) (hTgt : TargetIsSigmaCompact Phi)
    (beta psi : ℝ) (co : FlowMetricConvergenceData Phi R bf hSrc hTgt beta psi)
    (t : ℝ) (ht : t ∈ Icc beta psi)
    (density : ∀ k, (X.term (subseq (co.φ k))).M → ℝ)
    (densityLim : P.M → ℝ) (hDensity : ∀ k, Measurable (density k))
    (hDensityLim : Continuous densityLim)
    (hconv : TendstoLocallyUniformly
      (fun k y => density k (Phi.map (co.φ k) y)) densityLim atTop)
    (f : C_c(P.M, ℝ)) :
    Tendsto
      (fun k => ∫ y, f y
        ∂Measure.map (Phi.partialDiffeomorph (co.φ k)).symm
          (((riemannianVolumeMeasure (I := I) (M := (X.term (subseq (co.φ k))).M)
            ((X.term (subseq (co.φ k))).S.base.metric t)).withDensity
            (fun y => ENNReal.ofReal (density k y))).restrict
              (Phi.partialDiffeomorph (co.φ k)).target))
      atTop (𝓝 (∫ y, f y
        ∂(riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf t)).withDensity
          (fun y => ENNReal.ofReal (densityLim y)))) := by
  let μ := riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf t)
  let ν := μ.withDensity (fun y => ENNReal.ofReal (densityLim y))
  let μs : ℕ → Measure P.M := fun k =>
    Measure.map (Phi.partialDiffeomorph (co.φ k)).symm
      (((riemannianVolumeMeasure (I := I) (M := (X.term (subseq (co.φ k))).M)
        ((X.term (subseq (co.φ k))).S.base.metric t)).withDensity
        (fun y => ENNReal.ofReal (density k y))).restrict
          (Phi.partialDiffeomorph (co.φ k)).target)
  change Tendsto (fun k => ∫ y, f y ∂μs k) atTop (𝓝 (∫ y, f y ∂ν))
  let : IsFiniteMeasureOnCompacts μ :=
    riemannianVolumeMeasure_isFiniteMeasureOnCompacts (I := I) (M := P.M) (co.gInf t)
  have hprod : Continuous (fun y => f y * max (densityLim y) 0) :=
    f.continuous.mul (hDensityLim.max continuous_const)
  have hsupp : HasCompactSupport (fun y => f y * max (densityLim y) 0) :=
    f.hasCompactSupport.mul_right
  have hf : Integrable (fun y => f y) ν := by
    change Integrable (fun y => f y) (μ.withDensity (fun y => ENNReal.ofReal (densityLim y)))
    apply (integrable_withDensity_iff hDensityLim.measurable.ennreal_ofReal
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top)).mpr
    simpa only [ENNReal.toReal_ofReal'] using hprod.integrable_of_hasCompactSupport hsupp
  apply tendsto_integral_of_tendsto_lintegral_pos_neg
    (F := fun (_ : ℕ) (y : P.M) => f y)
    (Eventually.of_forall fun _ => f.continuous.aestronglyMeasurable) hf
  · exact FlowMetricConvergenceData.tendsto_lintegral_map_density_of_hasCompactSupport
      Phi R bf hSrc hTgt beta psi co t ht density densityLim hDensity hDensityLim hconv f
  · simpa only [CompactlySupportedContinuousMap.coe_neg, Pi.neg_apply] using
      FlowMetricConvergenceData.tendsto_lintegral_map_density_of_hasCompactSupport
        Phi R bf hSrc hTgt beta psi co t ht density densityLim hDensity hDensityLim hconv (-f)

end DifferentialGeometry.CheegerGromovCompactness

end

end

section

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter MeasureTheory Set
open DifferentialGeometry.Integral.Measure
open scoped CompactlySupported ContDiff Manifold _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type uH} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq.{u, uE, uH} (I := I)}
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {subseq : ℕ → ℕ}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedFlowData.topology PointedFlowData.charted PointedFlowData.smooth
  PointedFlowData.t2 PointedFlowData.sigmaCompact

private local instance : MeasurableSpace P.M := borel P.M
private local instance : BorelSpace P.M := ⟨rfl⟩
private local instance (k : ℕ) : MeasurableSpace (X.term k).M := borel (X.term k).M
private local instance (k : ℕ) : BorelSpace (X.term k).M := ⟨rfl⟩

theorem HalfLineMetricConvergenceData.tendsto_lintegral_map_density_of_hasCompactSupport
    (Phi : PointedCGHMaps X P subseq) (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Phi) (hSrc : SourceIsSigmaCompact Phi) (hTgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hSrc hTgt)
    (t : ℝ) (ht : t ≤ 0)
    (density : ∀ k, (X.term (subseq (co.φ k))).M → ℝ)
    (densityLim : P.M → ℝ) (hDensity : ∀ k, Measurable (density k))
    (hDensityLim : Continuous densityLim)
    (hconv : TendstoLocallyUniformly
      (fun k y => density k (Phi.map (co.φ k) y)) densityLim atTop)
    (f : C_c(P.M, ℝ)) :
    Tendsto
      (fun k => ∫⁻ y, ENNReal.ofReal (f y)
        ∂Measure.map (Phi.partialDiffeomorph (co.φ k)).symm
          (((riemannianVolumeMeasure (I := I) (M := (X.term (subseq (co.φ k))).M)
            ((X.term (subseq (co.φ k))).S.base.metric t)).withDensity
            (fun y => ENNReal.ofReal (density k y))).restrict
              (Phi.partialDiffeomorph (co.φ k)).target))
      atTop (𝓝 (∫⁻ y, ENNReal.ofReal (f y)
        ∂(riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf t)).withDensity
          (fun y => ENNReal.ofReal (densityLim y)))) := by
  obtain ⟨n, hn⟩ := exists_nat_ge (-t)
  have htwin : t ∈ Icc (-(n : ℝ)) 0 := ⟨by linarith, ht⟩
  exact FlowMetricConvergenceData.tendsto_lintegral_map_density_of_hasCompactSupport
    Phi R bf hSrc hTgt (-(n : ℝ)) 0 (HalfLineMetricConvergenceData.atWindow Phi co n)
    t htwin density densityLim hDensity hDensityLim hconv f

theorem HalfLineMetricConvergenceData.tendsto_lintegral_mul_density_of_hasCompactSupport
    (Phi : PointedCGHMaps X P subseq) (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Phi) (hSrc : SourceIsSigmaCompact Phi) (hTgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hSrc hTgt)
    (t : ℝ) (ht : t ≤ 0)
    (density : ∀ k, (X.term (subseq (co.φ k))).M → ℝ)
    (densityLim : P.M → ℝ) (hDensity : ∀ k, Measurable (density k))
    (hDensityLim : Continuous densityLim)
    (hconv : TendstoLocallyUniformly
      (fun k y => density k (Phi.map (co.φ k) y)) densityLim atTop)
    (f : C_c(P.M, ℝ)) :
    Tendsto
      (fun k => ∫⁻ y in (Phi.partialDiffeomorph (co.φ k)).target,
        ENNReal.ofReal (f ((Phi.partialDiffeomorph (co.φ k)).symm y)) *
          ENNReal.ofReal (density k y)
          ∂riemannianVolumeMeasure (I := I) (M := (X.term (subseq (co.φ k))).M)
            ((X.term (subseq (co.φ k))).S.base.metric t))
      atTop (𝓝 (∫⁻ y, ENNReal.ofReal (f y) * ENNReal.ofReal (densityLim y)
        ∂riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf t))) := by
  obtain ⟨n, hn⟩ := exists_nat_ge (-t)
  have htwin : t ∈ Icc (-(n : ℝ)) 0 := ⟨by linarith, ht⟩
  exact FlowMetricConvergenceData.tendsto_lintegral_mul_density_of_hasCompactSupport
    Phi R bf hSrc hTgt (-(n : ℝ)) 0 (HalfLineMetricConvergenceData.atWindow Phi co n)
    t htwin density densityLim hDensity hDensityLim hconv f

theorem HalfLineMetricConvergenceData.tendsto_integral_map_density_of_hasCompactSupport
    (Phi : PointedCGHMaps X P subseq) (R : SmoothRiemannianMetric I P.M)
    (bf : BumpFamily Phi) (hSrc : SourceIsSigmaCompact Phi) (hTgt : TargetIsSigmaCompact Phi)
    (co : HalfLineMetricConvergenceData Phi R bf hSrc hTgt)
    (t : ℝ) (ht : t ≤ 0)
    (density : ∀ k, (X.term (subseq (co.φ k))).M → ℝ)
    (densityLim : P.M → ℝ) (hDensity : ∀ k, Measurable (density k))
    (hDensityLim : Continuous densityLim)
    (hconv : TendstoLocallyUniformly
      (fun k y => density k (Phi.map (co.φ k) y)) densityLim atTop)
    (f : C_c(P.M, ℝ)) :
    Tendsto
      (fun k => ∫ y, f y
        ∂Measure.map (Phi.partialDiffeomorph (co.φ k)).symm
          (((riemannianVolumeMeasure (I := I) (M := (X.term (subseq (co.φ k))).M)
            ((X.term (subseq (co.φ k))).S.base.metric t)).withDensity
            (fun y => ENNReal.ofReal (density k y))).restrict
              (Phi.partialDiffeomorph (co.φ k)).target))
      atTop (𝓝 (∫ y, f y
        ∂(riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf t)).withDensity
          (fun y => ENNReal.ofReal (densityLim y)))) := by
  obtain ⟨n, hn⟩ := exists_nat_ge (-t)
  have htwin : t ∈ Icc (-(n : ℝ)) 0 := ⟨by linarith, ht⟩
  exact FlowMetricConvergenceData.tendsto_integral_map_density_of_hasCompactSupport
    Phi R bf hSrc hTgt (-(n : ℝ)) 0 (HalfLineMetricConvergenceData.atWindow Phi co n)
    t htwin density densityLim hDensity hDensityLim hconv f

end DifferentialGeometry.CheegerGromovCompactness

end

end

section

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter MeasureTheory Set
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff CompactlySupported _root_.Topology ENNReal

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq.{u, uE, uH} (I := I)}
  {P : PointedRiemannianManifold.{u, uE, uH} (I := I)} {phi : ℕ → ℕ}

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedFlowData.topology PointedFlowData.charted PointedFlowData.smooth
  PointedFlowData.t2 PointedFlowData.sigmaCompact

private local instance : MeasurableSpace P.M := borel P.M
private local instance : BorelSpace P.M := ⟨rfl⟩
private local instance (k : ℕ) : MeasurableSpace (X.term k).M := borel (X.term k).M
private local instance (k : ℕ) : BorelSpace (X.term k).M := ⟨rfl⟩

theorem HalfLineMetricConvergenceData.tendsto_lintegral_density_of_ball_tails
    (Phi : PointedCGHMaps X P phi) {R : SmoothRiemannianMetric I P.M}
    {bf : BumpFamily Phi} {hsrc : SourceIsSigmaCompact Phi} {htgt : TargetIsSigmaCompact Phi}
    (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt)
    {t : ℝ} (ht : t ≤ 0)
    (hcomplete : MetricComplete (I := I)
      ({ P with metric := co.gInf t } : PointedRiemannianManifold (I := I)))
    (z : P.M) (density : ∀ k, (X.term (phi (co.φ k))).M → ℝ)
    (densityLim : P.M → ℝ) (hDensity : ∀ k, Measurable (density k))
    (hDensityLim : Continuous densityLim)
    (hconv : TendstoLocallyUniformly
      (fun k y => density k (Phi.map (co.φ k) y)) densityLim atTop)
    {C : ℝ≥0∞} (hC : C < ⊤)
    (hbound : ∀ k, (∫⁻ y, ENNReal.ofReal (density k y)
      ∂riemannianVolumeMeasure (I := I) (M := (X.term (phi (co.φ k))).M)
        ((X.term (phi (co.φ k))).S.base.metric t)) ≤ C)
    (htail : ∀ ε : ℝ≥0∞, 0 < ε → ∃ r : ℝ, 0 ≤ r ∧ ∀ᶠ k in atTop,
      (∫⁻ y in (riemannianClosedBallOf
          ((X.term (phi (co.φ k))).S.base.metric t) (Phi.map (co.φ k) z) r)ᶜ,
        ENNReal.ofReal (density k y)
          ∂riemannianVolumeMeasure (I := I) (M := (X.term (phi (co.φ k))).M)
            ((X.term (phi (co.φ k))).S.base.metric t)) < ε) :
    (∫⁻ y, ENNReal.ofReal (densityLim y)
      ∂riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf t)) ≤ C ∧
      Tendsto (fun k => ∫⁻ y, ENNReal.ofReal (density k y)
        ∂riemannianVolumeMeasure (I := I) (M := (X.term (phi (co.φ k))).M)
          ((X.term (phi (co.φ k))).S.base.metric t)) atTop
        (𝓝 (∫⁻ y, ENNReal.ofReal (densityLim y)
          ∂riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf t))) := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : LocallyCompactSpace E := inferInstance
  let _ : LocallyCompactSpace H := I.locallyCompactSpace
  let _ : LocallyCompactSpace P.M := ChartedSpace.locallyCompactSpace H P.M
  let mu (k : ℕ) := (riemannianVolumeMeasure (I := I)
    (M := (X.term (phi (co.φ k))).M)
    ((X.term (phi (co.φ k))).S.base.metric t)).withDensity
      (fun y => ENNReal.ofReal (density k y))
  let nu := (riemannianVolumeMeasure (I := I) (M := P.M) (co.gInf t)).withDensity
    (fun y => ENNReal.ofReal (densityLim y))
  let e k := Phi.partialDiffeomorph (co.φ k)
  let pushed (k : ℕ) := Measure.map (e k).symm ((mu k).restrict (e k).target)
  have hmu (k : ℕ) : mu k univ ≤ C := by
    simpa only [mu, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] using hbound k
  have hinv (k : ℕ) : AEMeasurable (e k).symm ((mu k).restrict (e k).target) :=
    (e k).contMDiffOn_invFun.continuousOn.aemeasurable (e k).open_target.measurableSet
  have hpushed (k : ℕ) : pushed k univ ≤ C := by
    dsimp only [pushed]
    rw [Measure.map_apply_of_aemeasurable (hinv k) MeasurableSet.univ,
      preimage_univ, Measure.restrict_apply_univ]
    exact (measure_mono (subset_univ _)).trans (hmu k)
  have hlocal (f : C_c(P.M, ℝ)) :
      Tendsto (fun k => ∫⁻ y, ENNReal.ofReal (f y) ∂pushed k) atTop
        (𝓝 (∫⁻ y, ENNReal.ofReal (f y) ∂nu)) :=
    co.tendsto_lintegral_map_density_of_hasCompactSupport Phi R bf hsrc htgt
      t ht density densityLim hDensity hDensityLim hconv f
  have hcompact (K : Set P.M) (hK : IsCompact K) : nu K ≤ C := by
    obtain ⟨f, hfK, hfsupp, _, hfrange⟩ :=
      exists_continuousMap_one_of_isCompact_subset_isOpen hK isOpen_univ K.subset_univ
    let f' : C_c(P.M, ℝ) := ⟨f, hasCompactSupport_def.mpr hfsupp⟩
    have hlow : nu K ≤ ∫⁻ y, ENNReal.ofReal (f' y) ∂nu := by
      calc
        nu K = ∫⁻ y in K, ENNReal.ofReal (f' y) ∂nu := by
          have heq : (∫⁻ y in K, ENNReal.ofReal (f' y) ∂nu) = ∫⁻ _y in K, (1 : ℝ≥0∞) ∂nu := by
            apply setLIntegral_congr_fun hK.measurableSet
            intro y hy
            change ENNReal.ofReal (f y) = 1
            rw [hfK hy]
            exact ENNReal.ofReal_one
          rw [heq, setLIntegral_const, one_mul]
        _ ≤ _ := setLIntegral_le_lintegral K _
    apply hlow.trans
    apply le_of_tendsto (hlocal f')
    exact Eventually.of_forall fun k =>
      (calc
        (∫⁻ y, ENNReal.ofReal (f' y) ∂pushed k) ≤ ∫⁻ _y, (1 : ℝ≥0∞) ∂pushed k :=
          lintegral_mono fun y => by
            change ENNReal.ofReal (f y) ≤ 1
            exact_mod_cast ENNReal.ofReal_le_ofReal (hfrange y).2
        _ = pushed k univ := lintegral_one
        _ ≤ C := hpushed k)
  have hnu : nu univ ≤ C := by
    have hlim := tendsto_measure_iUnion_atTop (μ := nu) (compactCovering_subset P.M)
    rw [iUnion_compactCovering] at hlim
    exact le_of_tendsto hlim (Eventually.of_forall fun n =>
      hcompact (compactCovering P.M n) (isCompact_compactCovering P.M n))
  let _ : IsFiniteMeasure nu := ⟨hnu.trans_lt hC⟩
  let _ (k : ℕ) : IsFiniteMeasure (pushed k) := ⟨(hpushed k).trans_lt hC⟩
  let finiteNu : FiniteMeasure P.M := ⟨nu, inferInstance⟩
  let finitePushed (k : ℕ) : FiniteMeasure P.M := ⟨pushed k, inferInstance⟩
  have hnuTight (ε : ℝ≥0∞) (hε : 0 < ε) :
      ∃ K : Set P.M, IsCompact K ∧ nu Kᶜ ≤ ε := by
    have hlim := tendsto_measure_iInter_atTop (μ := nu)
      (s := fun n => (compactCovering P.M n)ᶜ)
      (fun n => (isCompact_compactCovering P.M n).measurableSet.compl.nullMeasurableSet)
      (fun i j hij => compl_subset_compl.mpr (compactCovering_subset P.M hij))
      ⟨0, measure_ne_top nu _⟩
    have hinter : (⋂ n, (compactCovering P.M n)ᶜ) = ∅ := by
      rw [← compl_iUnion, iUnion_compactCovering, compl_univ]
    rw [hinter, measure_empty] at hlim
    obtain ⟨n, hn⟩ := (ENNReal.tendsto_nhds_zero.mp hlim ε hε).exists
    exact ⟨compactCovering P.M n, isCompact_compactCovering P.M n, hn⟩
  have hpushedTight : ∀ ε : ℝ≥0∞, 0 < ε →
      ∃ K : Set P.M, IsCompact K ∧ ∀ᶠ k in atTop, pushed k Kᶜ ≤ ε := by
    apply co.exists_isCompact_inverse_map_compl_le_of_ball_tails Phi ht hcomplete z
      (fun k y => ENNReal.ofReal (density k y))
    intro ε hε
    obtain ⟨r, hr, hrtail⟩ := htail ε hε
    refine ⟨r, hr, ?_⟩
    filter_upwards [hrtail] with k hk
    have hB : MeasurableSet (riemannianClosedBallOf
        ((X.term (phi (co.φ k))).S.base.metric t) (Phi.map (co.φ k) z) r) := by
      exact (isClosed_le (Geometry.Riemannian.continuous_riemannianEDist
        ((X.term (phi (co.φ k))).S.base.metric t) (Phi.map (co.φ k) z))
        continuous_const).measurableSet
    rw [withDensity_apply _ hB.compl]
    exact hk.le
  have hmassNN : Tendsto (fun k => (finitePushed k).mass) atTop (𝓝 finiteNu.mass) := by
    apply DifferentialGeometry.Analysis.Measure.tendsto_mass_of_integral_tendsto_of_tight
    · intro f
      exact co.tendsto_integral_map_density_of_hasCompactSupport Phi R bf hsrc htgt
        t ht density densityLim hDensity hDensityLim hconv f
    · intro ε hε
      have he : 0 < ENNReal.ofReal ε := ENNReal.ofReal_pos.mpr hε
      obtain ⟨K, hK, hk⟩ := hpushedTight _ he
      obtain ⟨L, hL, hl⟩ := hnuTight _ he
      refine ⟨K ∪ L, hK.union hL, ?_, ?_⟩
      · filter_upwards [hk] with k hki
        have hle : pushed k (K ∪ L)ᶜ ≤ ENNReal.ofReal ε :=
          (measure_mono (compl_subset_compl.mpr subset_union_left)).trans hki
        change (pushed k (K ∪ L)ᶜ).toReal ≤ ε
        simpa only [ENNReal.toReal_ofReal hε.le] using
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
      · have hle : nu (K ∪ L)ᶜ ≤ ENNReal.ofReal ε :=
          (measure_mono (compl_subset_compl.mpr subset_union_right)).trans hl
        change (nu (K ∪ L)ᶜ).toReal ≤ ε
        simpa only [ENNReal.toReal_ofReal hε.le] using
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
  have hmass : Tendsto (fun k => pushed k univ) atTop (𝓝 (nu univ)) := by
    have h := (ENNReal.continuous_coe.tendsto finiteNu.mass).comp hmassNN
    have hmassEq (k : ℕ) : ((finitePushed k).mass : ℝ≥0∞) = pushed k univ :=
      FiniteMeasure.ennreal_mass
    have hnuEq : (finiteNu.mass : ℝ≥0∞) = nu univ := FiniteMeasure.ennreal_mass
    simpa only [Function.comp_def, hmassEq, hnuEq] using h
  have hmissing : Tendsto (fun k => mu k (e k).targetᶜ) atTop (𝓝 0) := by
    have h := co.tendsto_lintegral_compl_target_of_ball_tails Phi ht hcomplete z
      (fun k y => ENNReal.ofReal (density k y)) htail
    convert h using 1
    ext k
    exact withDensity_apply _ (e k).open_target.measurableSet.compl
  have hfull := DifferentialGeometry.Analysis.Measure.tendsto_measure_univ_of_map_restrict_and_compl
    mu (fun k => (e k).symm) (fun k => (e k).target) (fun k => (e k).target)
    (Eventually.of_forall hinv) (Eventually.of_forall fun _ => subset_rfl) hmass hmissing
  constructor
  · simpa only [nu, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] using hnu
  · simpa only [mu, nu, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] using hfull

end DifferentialGeometry.CheegerGromovCompactness

end

end
