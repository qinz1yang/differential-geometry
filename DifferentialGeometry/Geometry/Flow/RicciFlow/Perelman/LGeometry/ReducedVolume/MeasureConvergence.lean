import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.SourceIntegralConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Measure
import DifferentialGeometry.Analysis.Integration.Measure.IntegralConvergence
import DifferentialGeometry.Analysis.Integration.Measure.Chart.PartitionOfUnity.Integral
import Mathlib.Topology.ContinuousMap.CompactlySupported

noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Filter MeasureTheory Set Manifold
open Integral.Measure PDE.RicciFlow.Perelman
open scoped CompactlySupported ContDiff Manifold Topology ENNReal

universe u uE uH

section ChartPartition

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

private abbrev indices (f : C_c(M, ℝ)) : Finset M :=
  (chartAtlasPOU I M).toPartitionOfUnity.fintsupportOn
    (tsupport (f : M → ℝ)) f.hasCompactSupport

private abbrev carrier (f : C_c(M, ℝ)) (i : M) : Set M :=
  tsupport ((chartAtlasPOU I M) i) ∩ tsupport (f : M → ℝ)

private abbrev image (f : C_c(M, ℝ)) (i : M) : Set E :=
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

private theorem image_compact (f : C_c(M, ℝ)) (i : M) :
    IsCompact (image (I := I) f i) :=
  (carrier_compact f i).image_of_continuousOn
    ((continuousOn_extChartAt i).mono (carrier_subset_source f i))

private theorem image_subset_target (f : C_c(M, ℝ)) (i : M) :
    image (I := I) f i ⊆ (extChartAt I i).target := by
  rintro _ ⟨y, hy, rfl⟩
  exact (extChartAt I i).map_source (carrier_subset_source f i hy)

end ChartPartition

section Flow

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [Module.Finite ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {X : PointedFlowSeq.{u, uE, uH} (I := I)}
  {L : PointedFlowData.{u, uE, uH} (I := I) X.D} {subseq : ℕ → ℕ}

private local instance : TopologicalSpace L.M := L.topology
private local instance : ChartedSpace H L.M := L.charted
private local instance : T2Space L.M := L.t2
private local instance : IsManifold I ∞ L.M := L.smooth
private local instance : SigmaCompactSpace L.M := L.sigmaCompact
private local instance : MeasurableSpace L.M := borel L.M
private local instance : BorelSpace L.M := ⟨rfl⟩
private local instance : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
private local instance : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
private local instance : T2Space (L.atTime 0).M := (L.atTime 0).t2
private local instance : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
private local instance : SigmaCompactSpace (L.atTime 0).M := (L.atTime 0).sigmaCompact
private local instance : MeasurableSpace (L.atTime 0).M := borel (L.atTime 0).M
private local instance : BorelSpace (L.atTime 0).M := ⟨rfl⟩

private local instance (k : ℕ) : TopologicalSpace (X.term k).M := (X.term k).topology
private local instance (k : ℕ) : ChartedSpace H (X.term k).M := (X.term k).charted
private local instance (k : ℕ) : T2Space (X.term k).M := (X.term k).t2
private local instance (k : ℕ) : IsManifold I ∞ (X.term k).M := (X.term k).smooth
private local instance (k : ℕ) : SigmaCompactSpace (X.term k).M := (X.term k).sigmaCompact
private local instance (k : ℕ) : MeasurableSpace (X.term k).M := borel (X.term k).M
private local instance (k : ℕ) : BorelSpace (X.term k).M := ⟨rfl⟩
private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

variable {Phi : PointedCGHMaps (I := I) X (L.atTime 0) subseq}
  {R : SmoothRiemannianMetric I L.M} {bf : BumpFamily (I := I) Phi}
  {hSrc : SourceIsSigmaCompact Phi} {hTgt : TargetIsSigmaCompact Phi}
  {beta psi : ℝ}

private theorem limit_positive_chart_decomposition
    (co : FlowMetricConvergenceData (I := I) Phi R bf hSrc hTgt beta psi)
    (T tau : ℝ) (x : L.M) (f g : C_c(L.M, ℝ))
    (hgSupp : tsupport (g : L.M → ℝ) ⊆ tsupport (f : L.M → ℝ))
    (hd : ∀ i ∈ indices (I := I) (M := L.M) f,
      AEMeasurable (fun y => ENNReal.ofReal (redDensity L.S T x y tau))
        ((riemannianVolumeMeasure (I := I) (M := (L.atTime 0).M) (co.gInf (T - tau))).restrict
          (carrier (I := I) (M := L.M) f i))) :
    ∫⁻ y, ENNReal.ofReal (g y)
        ∂(riemannianVolumeMeasure (I := I) (M := (L.atTime 0).M) (co.gInf (T - tau))).withDensity
          (fun y => ENNReal.ofReal (redDensity L.S T x y tau)) =
      ∑ i ∈ indices (I := I) (M := L.M) f,
        ∫⁻ y in (extChartAt I i).symm '' image (I := I) (M := L.M) f i,
        ENNReal.ofReal
          ((chartAtlasPOU I L.M) i ((extChartAt I i).symm (extChartAt I i y)) *
            g ((extChartAt I i).symm (extChartAt I i y))) *
          ENNReal.ofReal (redDensity L.S T x y tau)
        ∂riemannianVolumeMeasure (I := I) (M := (L.atTime 0).M) (co.gInf (T - tau)) := by
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : IsManifold I ∞ L.M := L.smooth
  let : T2Space L.M := L.t2
  let : SigmaCompactSpace L.M := L.sigmaCompact
  let : MeasurableSpace L.M := borel L.M
  let : BorelSpace L.M := ⟨rfl⟩
  have hF : Function.support (fun y => ENNReal.ofReal (g y)) ⊆
      tsupport (f : L.M → ℝ) := by
    intro y hy
    apply hgSupp
    apply subset_tsupport _
    intro hz
    exact hy (by simp only [hz, ENNReal.ofReal_zero])
  have h := @Integral.Measure.lintegral_withDensity_eq_sum_chartAtlasPOU
    E _ _ _ H _ I L.M L.topology L.charted L.smooth L.t2 L.sigmaCompact
    (borel L.M) ⟨rfl⟩
    (riemannianVolumeMeasure (I := I) (M := (L.atTime 0).M) (co.gInf (T - tau)))
    (fun y => ENNReal.ofReal (redDensity L.S T x y tau))
    (tsupport (f : L.M → ℝ)) f.hasCompactSupport
    (fun y => ENNReal.ofReal (g y)) g.continuous.measurable.ennreal_ofReal hF hd
  simpa only [indices, image, carrier,
    ENNReal.ofReal_mul ((chartAtlasPOU I L.M).nonneg _ _)] using! h

private theorem source_positive_chart_decomposition [I.Boundaryless]
    (co : FlowMetricConvergenceData (I := I) Phi R bf hSrc hTgt beta psi)
    (T tau : ℝ) (x : L.M) (f g : C_c(L.M, ℝ))
    (hgSupp : tsupport (g : L.M → ℝ) ⊆ tsupport (f : L.M → ℝ))
    (hd : ∀ᶠ k in atTop,
      let : TopologicalSpace (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).topology
      let : ChartedSpace H (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).charted
      let : T2Space (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).t2
      let : IsManifold I ∞ (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).smooth
      let : SigmaCompactSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).sigmaCompact
      let : MeasurableSpace (X.term (subseq (co.φ k))).M := borel _
      ∀ i ∈ indices (I := I) (M := L.M) f,
        AEMeasurable
          (fun y => ENNReal.ofReal
            (redDensity (X.term (subseq (co.φ k))).S T (Phi.map (co.φ k) x) y tau))
          ((riemannianVolumeMeasure (I := I) (M := (X.term (subseq (co.φ k))).M)
              ((X.term (subseq (co.φ k))).S.base.metric (T - tau))).restrict
            ((Phi.partialDiffeomorph (co.φ k)) '' carrier (I := I) (M := L.M) f i))) :
    ∀ᶠ k in atTop,
      let : TopologicalSpace (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).topology
      let : ChartedSpace H (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).charted
      let : T2Space (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).t2
      let : IsManifold I ∞ (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).smooth
      let : SigmaCompactSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).sigmaCompact
      let : MeasurableSpace (X.term (subseq (co.φ k))).M := borel _
      let e := Phi.partialDiffeomorph (co.φ k)
      let vol := riemannianVolumeMeasure (I := I) (M := (X.term (subseq (co.φ k))).M)
        ((X.term (subseq (co.φ k))).S.base.metric (T - tau))
      let d := fun y => ENNReal.ofReal
        (redDensity (X.term (subseq (co.φ k))).S T (Phi.map (co.φ k) x) y tau)
      ∫⁻ y, ENNReal.ofReal (g y)
        ∂Measure.map e.symm
          ((redDensityMeasure (X.term (subseq (co.φ k))).S T (Phi.map (co.φ k) x) tau).restrict
            e.target) =
        ∑ i ∈ indices (I := I) (M := L.M) f,
          ∫⁻ y in Phi.chartParametrization (co.φ k) i '' image (I := I) (M := L.M) f i,
            ENNReal.ofReal
              ((chartAtlasPOU I L.M) i
                  ((extChartAt I i).symm ((Phi.chartParametrization (co.φ k) i).symm y)) *
                g ((extChartAt I i).symm ((Phi.chartParametrization (co.φ k) i).symm y))) *
              d y ∂vol := by
  obtain ⟨k0, hk0⟩ := Phi.source_subset f.hasCompactSupport
  filter_upwards [Filter.eventually_ge_atTop k0, hd] with k hk hdk
  let : TopologicalSpace (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).topology
  let : ChartedSpace H (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).charted
  let : T2Space (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).t2
  let : IsManifold I ∞ (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).smooth
  let : SigmaCompactSpace (X.term (subseq (co.φ k))).M :=
    (X.term (subseq (co.φ k))).sigmaCompact
  let : MeasurableSpace (X.term (subseq (co.φ k))).M := borel _
  let : BorelSpace (X.term (subseq (co.φ k))).M := ⟨rfl⟩
  have hcover : tsupport (f : L.M → ℝ) ⊆ Phi.source (co.φ k) :=
    hk0 (co.φ k) (hk.trans (co.strictMono.id_le k))
  have hF : Function.support (fun y => ENNReal.ofReal (g y)) ⊆
      tsupport (f : L.M → ℝ) := by
    intro y hy
    apply hgSupp
    apply subset_tsupport _
    intro hz
    exact hy (by simp only [hz, ENNReal.ofReal_zero])
  have h := OpenPartialHomeomorph.lintegral_map_symm_withDensity_eq_sum_chartAtlasPOU
    (I := I) (Phi.partialDiffeomorph (co.φ k)).toOpenPartialHomeomorph
    (riemannianVolumeMeasure (I := I) (M := (X.term (subseq (co.φ k))).M)
      ((X.term (subseq (co.φ k))).S.base.metric (T - tau)))
    (fun y => ENNReal.ofReal
      (redDensity (X.term (subseq (co.φ k))).S T (Phi.map (co.φ k) x) y tau))
    f.hasCompactSupport (fun y => ENNReal.ofReal (g y))
    g.continuous.measurable.ennreal_ofReal hF (fun _ _ _ hy => hcover hy.2) hdk
  simpa only [indices, image, carrier, redDensityMeasure, PointedCGHMaps.chartParametrization,
    ENNReal.ofReal_mul ((chartAtlasPOU I L.M).nonneg _ _)] using! h

variable [I.Boundaryless]

private def sourceMeasure
    (co : FlowMetricConvergenceData Phi R bf hSrc hTgt beta psi)
    (T tau : ℝ) (x : L.M) (k : ℕ) : Measure L.M :=
  Measure.map (Phi.partialDiffeomorph (co.φ k)).symm
    ((redDensityMeasure (X.term (subseq (co.φ k))).S T (Phi.map (co.φ k) x) tau).restrict
      (Phi.partialDiffeomorph (co.φ k)).target)

private def limitMeasure
    (co : FlowMetricConvergenceData Phi R bf hSrc hTgt beta psi)
    (T tau : ℝ) (x : L.M) : Measure L.M :=
  (riemannianVolumeMeasure (I := I) (M := (L.atTime 0).M) (co.gInf (T - tau))).withDensity
    (fun y => ENNReal.ofReal (redDensity L.S T x y tau))

private theorem test_lintegral_convergence
    (co : FlowMetricConvergenceData Phi R bf hSrc hTgt beta psi)
    (T tau : ℝ) (x : L.M) (hTime : T - tau ∈ Icc beta psi)
    (f g : C_c(L.M, ℝ))
    (hgSupp : tsupport (g : L.M → ℝ) ⊆ tsupport (f : L.M → ℝ))
    (hSrcDens : ∀ᶠ k in atTop, ∀ i ∈ indices (I := I) (M := L.M) f,
      AEMeasurable (fun y => ENNReal.ofReal
        (redDensity (X.term (subseq (co.φ k))).S T (Phi.map (co.φ k) x) y tau))
        ((riemannianVolumeMeasure (I := I) (M := (X.term (subseq (co.φ k))).M)
            ((X.term (subseq (co.φ k))).S.base.metric (T - tau))).restrict
          ((Phi.partialDiffeomorph (co.φ k)) '' carrier (I := I) (M := L.M) f i)))
    (hLimDens : ∀ i ∈ indices (I := I) (M := L.M) f,
      AEMeasurable (fun y => ENNReal.ofReal (redDensity L.S T x y tau))
        ((riemannianVolumeMeasure (I := I) (M := (L.atTime 0).M) (co.gInf (T - tau))).restrict
          (carrier (I := I) (M := L.M) f i)))
    (hRedMeas : ∀ i ∈ indices (I := I) (M := L.M) f, ∀ᶠ k in atTop,
      AEMeasurable (fun z => ENNReal.ofReal
        (redDensity (X.term (subseq (co.φ k))).S T (Phi.map (co.φ k) x)
          (Phi.map (co.φ k) ((extChartAt I i).symm z)) tau))
        ((modelHaar (E := E)).restrict (image (I := I) (M := L.M) f i)))
    (hRedLim : ∀ i ∈ indices (I := I) (M := L.M) f,
      ∀ᵐ z ∂((modelHaar (E := E)).restrict (image (I := I) (M := L.M) f i)),
      Tendsto (fun k => redDensity (X.term (subseq (co.φ k))).S T
        (Phi.map (co.φ k) x) (Phi.map (co.φ k) ((extChartAt I i).symm z)) tau)
        atTop (𝓝 (redDensity L.S T x ((extChartAt I i).symm z) tau)))
    (Cred : L.M → NNReal)
    (hRedBd : ∀ i ∈ indices (I := I) (M := L.M) f, ∀ᶠ k in atTop,
      ∀ᵐ z ∂((modelHaar (E := E)).restrict (image (I := I) (M := L.M) f i)),
      ENNReal.ofReal (redDensity (X.term (subseq (co.φ k))).S T (Phi.map (co.φ k) x)
        (Phi.map (co.φ k) ((extChartAt I i).symm z)) tau) ≤ (Cred i : ENNReal)) :
    Tendsto (fun k => ∫⁻ y, ENNReal.ofReal (g y) ∂sourceMeasure co T tau x k) atTop
      (𝓝 (∫⁻ y, ENNReal.ofReal (g y) ∂limitMeasure co T tau x)) ∧
      (∫⁻ y, ENNReal.ofReal (g y) ∂limitMeasure co T tau x) < ⊤ := by
  classical
  let w : L.M → E → ENNReal := fun i z => ENNReal.ofReal
    ((chartAtlasPOU I L.M) i ((extChartAt I i).symm z) * g ((extChartAt I i).symm z))
  let p : L.M → ℕ → ENNReal := fun i k =>
    ∫⁻ y in Phi.chartParametrization (co.φ k) i '' image (I := I) (M := L.M) f i,
      w i ((Phi.chartParametrization (co.φ k) i).symm y) *
        ENNReal.ofReal (redDensity (X.term (subseq (co.φ k))).S T (Phi.map (co.φ k) x) y tau)
        ∂riemannianVolumeMeasure (I := I) (M := (X.term (subseq (co.φ k))).M)
          ((X.term (subseq (co.φ k))).S.base.metric (T - tau))
  let q : L.M → ENNReal := fun i =>
    ∫⁻ y in (extChartAt I i).symm '' image (I := I) (M := L.M) f i,
      w i (extChartAt I i y) * ENNReal.ofReal (redDensity L.S T x y tau)
        ∂riemannianVolumeMeasure (I := I) (M := (L.atTime 0).M) (co.gInf (T - tau))
  have hpq : ∀ i ∈ indices (I := I) (M := L.M) f, Tendsto (p i) atTop (𝓝 (q i)) ∧ q i < ⊤ := by
    intro i hi
    have hB := image_compact (I := I) f i
    have ht := image_subset_target (I := I) f i
    have hc : ContinuousOn
        (fun z => (chartAtlasPOU I L.M) i ((extChartAt I i).symm z) *
          g ((extChartAt I i).symm z)) (image (I := I) (M := L.M) f i) :=
      ((((chartAtlasPOU I L.M) i).contMDiff.continuous.mul g.continuous).comp_continuousOn
        (continuousOn_extChartAt_symm i)).mono ht
    have hw : AEMeasurable (w i) ((modelHaar (E := E)).restrict (image (I := I) (M := L.M) f i)) :=
      (ENNReal.continuous_ofReal.comp_continuousOn hc).aemeasurable hB.measurableSet
    have hwInt : ∫⁻ z in image (I := I) (M := L.M) f i, w i z ∂modelHaar < ⊤ :=
      (hc.integrableOn_compact hB (μ := modelHaar)).lintegral_lt_top
    exact ⟨FlowMetricConvergenceData.tendsto_lintegral_mul_redDensity_chartParametrization
      Phi R bf hSrc hTgt beta psi co T tau x i hTime ht hB (w i) hw hwInt
      (hRedMeas i hi) (hRedLim i hi) (Cred i) (hRedBd i hi),
      FlowMetricConvergenceData.lintegral_mul_redDensity_lt_top
        Phi R bf hSrc hTgt beta psi co T tau x i ht hB (w i) hwInt
        (hRedLim i hi) (Cred i) (hRedBd i hi)⟩
  have hSource : ∀ᶠ k in atTop,
      (∫⁻ y, ENNReal.ofReal (g y) ∂sourceMeasure co T tau x k) =
        ∑ i ∈ indices (I := I) (M := L.M) f, p i k :=
    source_positive_chart_decomposition
      co T tau x f g hgSupp hSrcDens
  have hLimit : (∫⁻ y, ENNReal.ofReal (g y) ∂limitMeasure co T tau x) =
      ∑ i ∈ indices (I := I) (M := L.M) f, q i :=
    limit_positive_chart_decomposition
      co T tau x f g hgSupp hLimDens
  rw [hLimit]
  exact ⟨(tendsto_finsetSum _ fun i hi => (hpq i hi).1).congr'
    (Filter.EventuallyEq.symm hSource),
    (ENNReal.sum_ne_top.mpr fun i hi => (hpq i hi).2.ne).lt_top⟩

theorem FlowMetricConvergenceData.tendsto_integral_map_redDensityMeasure
    (co : FlowMetricConvergenceData Phi R bf hSrc hTgt beta psi)
    (T tau : ℝ) (x : L.M) (hTime : T - tau ∈ Icc beta psi)
    (f : C_c(L.M, ℝ))
    (hSrcDens : ∀ᶠ k in atTop, ∀ i ∈ (chartAtlasPOU I L.M).toPartitionOfUnity.fintsupportOn
        (tsupport (f : L.M → ℝ)) f.hasCompactSupport,
      AEMeasurable (fun y => ENNReal.ofReal
        (redDensity (X.term (subseq (co.φ k))).S T (Phi.map (co.φ k) x) y tau))
        ((riemannianVolumeMeasure (I := I) (M := (X.term (subseq (co.φ k))).M)
            ((X.term (subseq (co.φ k))).S.base.metric (T - tau))).restrict
          ((Phi.partialDiffeomorph (co.φ k)) ''
            (tsupport ((chartAtlasPOU I L.M) i) ∩ tsupport (f : L.M → ℝ)))))
    (hLimDens : ∀ i ∈ (chartAtlasPOU I L.M).toPartitionOfUnity.fintsupportOn
        (tsupport (f : L.M → ℝ)) f.hasCompactSupport,
      AEMeasurable (fun y => ENNReal.ofReal (redDensity L.S T x y tau))
        ((riemannianVolumeMeasure (I := I) (M := (L.atTime 0).M) (co.gInf (T - tau))).restrict
          (tsupport ((chartAtlasPOU I L.M) i) ∩ tsupport (f : L.M → ℝ))))
    (hRedMeas : ∀ i ∈ (chartAtlasPOU I L.M).toPartitionOfUnity.fintsupportOn
        (tsupport (f : L.M → ℝ)) f.hasCompactSupport, ∀ᶠ k in atTop,
      AEMeasurable (fun z => ENNReal.ofReal
        (redDensity (X.term (subseq (co.φ k))).S T (Phi.map (co.φ k) x)
          (Phi.map (co.φ k) ((extChartAt I i).symm z)) tau))
        ((modelHaar (E := E)).restrict (extChartAt I i ''
          (tsupport ((chartAtlasPOU I L.M) i) ∩ tsupport (f : L.M → ℝ)))))
    (hRedLim : ∀ i ∈ (chartAtlasPOU I L.M).toPartitionOfUnity.fintsupportOn
        (tsupport (f : L.M → ℝ)) f.hasCompactSupport,
      ∀ᵐ z ∂((modelHaar (E := E)).restrict (extChartAt I i ''
          (tsupport ((chartAtlasPOU I L.M) i) ∩ tsupport (f : L.M → ℝ)))),
      Tendsto (fun k => redDensity (X.term (subseq (co.φ k))).S T
        (Phi.map (co.φ k) x) (Phi.map (co.φ k) ((extChartAt I i).symm z)) tau)
        atTop (𝓝 (redDensity L.S T x ((extChartAt I i).symm z) tau)))
    (Cred : L.M → NNReal)
    (hRedBd : ∀ i ∈ (chartAtlasPOU I L.M).toPartitionOfUnity.fintsupportOn
        (tsupport (f : L.M → ℝ)) f.hasCompactSupport, ∀ᶠ k in atTop,
      ∀ᵐ z ∂((modelHaar (E := E)).restrict (extChartAt I i ''
          (tsupport ((chartAtlasPOU I L.M) i) ∩ tsupport (f : L.M → ℝ)))),
      ENNReal.ofReal (redDensity (X.term (subseq (co.φ k))).S T (Phi.map (co.φ k) x)
        (Phi.map (co.φ k) ((extChartAt I i).symm z)) tau) ≤ (Cred i : ENNReal)) :
    Tendsto (fun k => ∫ y, f y ∂(Measure.map (Phi.partialDiffeomorph (co.φ k)).symm
        ((redDensityMeasure (X.term (subseq (co.φ k))).S T (Phi.map (co.φ k) x) tau).restrict
          (Phi.partialDiffeomorph (co.φ k)).target))) atTop
      (𝓝 (∫ y, f y ∂((riemannianVolumeMeasure (I := I) (M := (L.atTime 0).M)
        (co.gInf (T - tau))).withDensity (fun y => ENNReal.ofReal (redDensity L.S T x y tau))))) := by
  change Tendsto (fun k => ∫ y, f y ∂sourceMeasure co T tau x k) atTop
    (𝓝 (∫ y, f y ∂limitMeasure co T tau x))
  have hsupp (q : C_c(L.M, ℝ)) :
      tsupport (q.nnrealPart.toReal : L.M → ℝ) ⊆ tsupport (q : L.M → ℝ) := by
    apply closure_mono
    intro y hy hz
    exact hy (by simp [hz])
  have hnegSupp : tsupport ((-f).nnrealPart.toReal : L.M → ℝ) ⊆
      tsupport (f : L.M → ℝ) := by
    simpa only [CompactlySupportedContinuousMap.coe_neg, tsupport_neg] using hsupp (-f)
  have hp := test_lintegral_convergence co T tau x hTime f f.nnrealPart.toReal
    (hsupp f)
    hSrcDens hLimDens hRedMeas hRedLim Cred hRedBd
  have hn := test_lintegral_convergence co T tau x hTime f (-f).nnrealPart.toReal
    hnegSupp
    hSrcDens hLimDens hRedMeas hRedLim Cred hRedBd
  have hip : Integrable (fun y => f.nnrealPart.toReal y) (limitMeasure co T tau x) :=
    (lintegral_ofReal_ne_top_iff_integrable
      f.nnrealPart.toReal.continuous.aestronglyMeasurable
      (Eventually.of_forall fun y => by simp)).mp hp.2.ne
  have hin : Integrable (fun y => (-f).nnrealPart.toReal y) (limitMeasure co T tau x) :=
    (lintegral_ofReal_ne_top_iff_integrable
      (-f).nnrealPart.toReal.continuous.aestronglyMeasurable
      (Eventually.of_forall fun y => by simp)).mp hn.2.ne
  have hf : Integrable (fun y => f y) (limitMeasure co T tau x) := by
    rw [← CompactlySupportedContinuousMap.nnrealPart_sub_nnrealPart_neg f]
    exact hip.sub hin
  apply tendsto_integral_of_tendsto_lintegral_pos_neg
    (F := fun (_ : ℕ) (y : L.M) => f y)
    (Eventually.of_forall fun _ => f.continuous.aestronglyMeasurable) hf
  · simpa only [sourceMeasure, CompactlySupportedContinuousMap.toReal_apply,
      CompactlySupportedContinuousMap.nnrealPart_apply, ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal, Real.toNNReal_coe] using hp.1
  · simpa only [sourceMeasure, CompactlySupportedContinuousMap.toReal_apply,
      CompactlySupportedContinuousMap.nnrealPart_apply, ENNReal.ofReal_coe_nnreal,
      ENNReal.ofReal, Real.toNNReal_coe, CompactlySupportedContinuousMap.coe_neg,
      Pi.neg_apply] using hn.1

end Flow

end DifferentialGeometry.CheegerGromovCompactness
