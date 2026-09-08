import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedVolume.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.VolumeConvergence
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence

noncomputable section

open Filter MeasureTheory Set
open scoped ContDiff Manifold Topology

namespace DifferentialGeometry.CheegerGromovCompactness

open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}

private local instance : MeasurableSpace E := borel E
private local instance : BorelSpace E := ⟨rfl⟩

theorem FlowMetricConvergenceData.tendsto_lintegral_mul_chartDensity_mul_redDensity
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat → Nat}
    (Phi : PointedCGHMaps (I := I) X (L.atTime 0) subseq)
    (R : let : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
      let : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
      let : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      SmoothRiemannianMetric I (L.atTime 0).M)
    (bf : BumpFamily (I := I) Phi) (hSrc : SourceIsSigmaCompact Phi) (hTgt : TargetIsSigmaCompact Phi)
    (beta psi : Real) (co : FlowMetricConvergenceData (I := I) Phi R bf hSrc hTgt beta psi)
    (T tau : Real) (x alpha : L.M) {B : Set E}
    (hTime : T - tau ∈ Icc beta psi)
    (hBChart : let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      B ⊆ (extChartAt I alpha).target)
    (hBc : IsCompact B)
    (w : E → ENNReal)
    (hw : AEMeasurable w ((modelHaar (E := E)).restrict B))
    (hwInt : ∫⁻ z in B, w z ∂(modelHaar (E := E)) < ⊤)
    (hRedMeas : let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      let : IsManifold I ∞ L.M := L.smooth
      ∀ᶠ k in atTop, AEMeasurable
        (fun z : E ↦
          let : TopologicalSpace (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).topology
          let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
            (X.term (subseq (co.φ k))).charted
          let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
            (X.term (subseq (co.φ k))).smooth
          ENNReal.ofReal (redDensity (X.term (subseq (co.φ k))).S T
            (Phi.map (co.φ k) x)
            (Phi.map (co.φ k) ((extChartAt I alpha).symm z)) tau))
        ((modelHaar (E := E)).restrict B))
    (hRedLim : let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      let : IsManifold I ∞ L.M := L.smooth
      ∀ᵐ z ∂((modelHaar (E := E)).restrict B), Tendsto
        (fun k ↦
          let : TopologicalSpace (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).topology
          let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
            (X.term (subseq (co.φ k))).charted
          let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
            (X.term (subseq (co.φ k))).smooth
          redDensity (X.term (subseq (co.φ k))).S T
            (Phi.map (co.φ k) x)
            (Phi.map (co.φ k) ((extChartAt I alpha).symm z)) tau)
        atTop (nhds (redDensity L.S T x ((extChartAt I alpha).symm z) tau)))
    (Cred : NNReal)
    (hRedBd : let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      ∀ᶠ k in atTop, ∀ᵐ z ∂((modelHaar (E := E)).restrict B),
        let : TopologicalSpace (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).topology
        let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
          (X.term (subseq (co.φ k))).charted
        let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
          (X.term (subseq (co.φ k))).smooth
        ENNReal.ofReal (redDensity (X.term (subseq (co.φ k))).S T
          (Phi.map (co.φ k) x)
          (Phi.map (co.φ k) ((extChartAt I alpha).symm z)) tau) ≤
            (Cred : ENNReal)) :
    let : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
    let : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
    let : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
    let : TopologicalSpace L.M := L.topology
    let : ChartedSpace H L.M := L.charted
    let : IsManifold I ∞ L.M := L.smooth
    Tendsto
      (fun k ↦ ∫⁻ z in B,
        w z * (ENNReal.ofReal (chartDensity (I := I)
          (gSeqExt (I := I) Phi R bf hSrc hTgt (co.φ k) (T - tau)) alpha
          ((extChartAt I alpha).symm z)) *
        (let : TopologicalSpace (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).topology
         let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
            (X.term (subseq (co.φ k))).charted
         let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
            (X.term (subseq (co.φ k))).smooth
         ENNReal.ofReal (redDensity (X.term (subseq (co.φ k))).S T
           (Phi.map (co.φ k) x)
           (Phi.map (co.φ k) ((extChartAt I alpha).symm z)) tau)))
        ∂(modelHaar (E := E)))
      atTop
      (nhds (∫⁻ z in B,
        w z * (ENNReal.ofReal (chartDensity (I := I) (co.gInf (T - tau)) alpha
          ((extChartAt I alpha).symm z)) *
        ENNReal.ofReal (redDensity L.S T x ((extChartAt I alpha).symm z) tau))
        ∂(modelHaar (E := E)))) := by
  let : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
  let : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
  let : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : IsManifold I ∞ L.M := L.smooth
  let vol : Nat → E → Real := fun k z ↦ chartDensity (I := I)
    (gSeqExt (I := I) Phi R bf hSrc hTgt (co.φ k) (T - tau)) alpha
    ((extChartAt I alpha).symm z)
  let volLim : E → Real := fun z ↦ chartDensity (I := I)
    (co.gInf (T - tau)) alpha ((extChartAt I alpha).symm z)
  let red : Nat → E → Real := fun k z ↦
    let : TopologicalSpace (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).topology
    let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).charted
    let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
      (X.term (subseq (co.φ k))).smooth
    redDensity (X.term (subseq (co.φ k))).S T (Phi.map (co.φ k) x)
      (Phi.map (co.φ k) ((extChartAt I alpha).symm z)) tau
  let redLim : E → Real := fun z ↦
    redDensity L.S T x ((extChartAt I alpha).symm z) tau
  have hVolU := FlowMetricConvergenceData.tendstoUniformlyOn_chartDensity
    Phi R bf hSrc hTgt beta psi co alpha hBChart hBc hTime
  have hVolCont : ContinuousOn volLim B :=
    (chartDensityOnE_contDiffOn (co.gInf (T - tau)) alpha).continuousOn.mono hBChart
  obtain ⟨Mvol, hMvol⟩ := hBc.bddAbove_image hVolCont
  let Cvol : NNReal := Real.toNNReal (max Mvol 0 + 1)
  have hNear := (Metric.tendstoUniformlyOn_iff.1 hVolU) 1 zero_lt_one
  have hVolBd : ∀ᶠ k in atTop, ∀ᵐ z ∂((modelHaar (E := E)).restrict B),
      ENNReal.ofReal (vol k z) ≤ (Cvol : ENNReal) := by
    filter_upwards [hNear] with k hk
    filter_upwards [ae_restrict_mem hBc.measurableSet] with z hz
    have hdist : |vol k z - volLim z| < 1 := by
      simpa only [Real.dist_eq, abs_sub_comm, vol, volLim] using! hk z hz
    have hseq : vol k z ≤ max Mvol 0 + 1 := by
      linarith [le_abs_self (vol k z - volLim z), hMvol ⟨z, hz, rfl⟩, le_max_left Mvol (0 : Real)]
    change ENNReal.ofReal (vol k z) ≤ ENNReal.ofReal (max Mvol 0 + 1)
    exact ENNReal.ofReal_le_ofReal hseq
  have hVolLim : ∀ z ∈ B, Tendsto (fun k ↦ vol k z) atTop (nhds (volLim z)) := by
    intro z hz
    convert hVolU.tendsto_at hz using 1 <;> rfl
  have hVolMeas (k : Nat) : AEMeasurable
      (fun z ↦ ENNReal.ofReal (vol k z)) ((modelHaar (E := E)).restrict B) := by
    have hc := ((chartDensityOnE_contDiffOn
      (gSeqExt (I := I) Phi R bf hSrc hTgt (co.φ k) (T - tau)) alpha).continuousOn.mono hBChart)
    exact ENNReal.measurable_ofReal.comp_aemeasurable (hc.aemeasurable hBc.measurableSet)
  have hRedMeas' : ∀ᶠ k in atTop, AEMeasurable
      (fun z ↦ ENNReal.ofReal (red k z)) ((modelHaar (E := E)).restrict B) := by
    filter_upwards [hRedMeas] with k hk
    simpa only [red] using hk
  have hRedLim' : ∀ᵐ z ∂((modelHaar (E := E)).restrict B),
      Tendsto (fun k ↦ red k z) atTop (nhds (redLim z)) := by
    simpa only [red, redLim] using hRedLim
  let μ : Measure E := (modelHaar (E := E)).restrict B
  let F : Nat → E → ENNReal := fun k z =>
    w z * (ENNReal.ofReal (vol k z) * ENNReal.ofReal (red k z))
  let f : E → ENNReal := fun z =>
    w z * (ENNReal.ofReal (volLim z) * ENNReal.ofReal (redLim z))
  let C : E → ENNReal := fun z => ((Cvol : ENNReal) * (Cred : ENNReal)) * w z
  have hFMeas : ∀ᶠ k in atTop, AEMeasurable (F k) μ := by
    filter_upwards [hRedMeas'] with k hk
    convert hw.mul ((hVolMeas k).mul hk) using 1 <;> rfl
  have hBound : ∀ᶠ k in atTop, F k ≤ᵐ[μ] C := by
    filter_upwards [hVolBd, hRedBd] with k hkVol hkRed
    filter_upwards [hkVol, hkRed] with z hzVol hzRed
    exact (mul_le_mul' (le_refl (w z)) (mul_le_mul' hzVol hzRed)).trans_eq (mul_comm _ _)
  have hFin : ∫⁻ z, C z ∂μ ≠ ⊤ := by
    rw [lintegral_const_mul'' _ hw]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (by simp)) hwInt.ne
  have hLim : ∀ᵐ z ∂μ, Tendsto (fun k => F k z) atTop (nhds (f z)) := by
    filter_upwards [ae_restrict_mem hBc.measurableSet, hRedLim', ae_lt_top' hw hwInt.ne] with z hz hr hwz
    have hp : Tendsto
        (fun k => ENNReal.ofReal (vol k z) * ENNReal.ofReal (red k z)) atTop
        (nhds (ENNReal.ofReal (volLim z) * ENNReal.ofReal (redLim z))) := by
      apply ENNReal.Tendsto.mul
      · exact (ENNReal.continuous_ofReal.tendsto _).comp (hVolLim z hz)
      · exact Or.inr ENNReal.ofReal_ne_top
      · exact (ENNReal.continuous_ofReal.tendsto _).comp hr
      · exact Or.inr ENNReal.ofReal_ne_top
    exact ENNReal.Tendsto.mul tendsto_const_nhds (Or.inr
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)) hp (Or.inr hwz.ne)
  simpa only [F, f, μ, vol, volLim, red, redLim] using
    (tendsto_lintegral_filter_of_dominated_convergence' C hFMeas hBound hFin hLim)

theorem FlowMetricConvergenceData.tendsto_lintegral_chartDensity_mul_redDensity
    {X : PointedFlowSeq.{u, uE, uH} (I := I)}
    {L : PointedFlowData.{u, uE, uH} (I := I) X.D}
    {subseq : Nat → Nat}
    (Phi : PointedCGHMaps (I := I) X (L.atTime 0) subseq)
    (R : let : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
      let : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
      let : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
      SmoothRiemannianMetric I (L.atTime 0).M)
    (bf : BumpFamily (I := I) Phi) (hSrc : SourceIsSigmaCompact Phi) (hTgt : TargetIsSigmaCompact Phi)
    (beta psi : Real) (co : FlowMetricConvergenceData (I := I) Phi R bf hSrc hTgt beta psi)
    (T tau : Real) (x alpha : L.M) {B : Set E}
    (hTime : T - tau ∈ Icc beta psi)
    (hBChart : let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      B ⊆ (extChartAt I alpha).target)
    (hBc : IsCompact B)
    (hRedMeas : let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      let : IsManifold I ∞ L.M := L.smooth
      ∀ᶠ k in atTop, AEMeasurable
        (fun z : E ↦
          let : TopologicalSpace (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).topology
          let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
            (X.term (subseq (co.φ k))).charted
          let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
            (X.term (subseq (co.φ k))).smooth
          ENNReal.ofReal (redDensity (X.term (subseq (co.φ k))).S T
            (Phi.map (co.φ k) x)
            (Phi.map (co.φ k) ((extChartAt I alpha).symm z)) tau))
        ((modelHaar (E := E)).restrict B))
    (hRedLim : let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      let : IsManifold I ∞ L.M := L.smooth
      ∀ᵐ z ∂((modelHaar (E := E)).restrict B), Tendsto
        (fun k ↦
          let : TopologicalSpace (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).topology
          let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
            (X.term (subseq (co.φ k))).charted
          let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
            (X.term (subseq (co.φ k))).smooth
          redDensity (X.term (subseq (co.φ k))).S T
            (Phi.map (co.φ k) x)
            (Phi.map (co.φ k) ((extChartAt I alpha).symm z)) tau)
        atTop (nhds (redDensity L.S T x ((extChartAt I alpha).symm z) tau)))
    (Cred : NNReal)
    (hRedBd : let : TopologicalSpace L.M := L.topology
      let : ChartedSpace H L.M := L.charted
      ∀ᶠ k in atTop, ∀ᵐ z ∂((modelHaar (E := E)).restrict B),
        let : TopologicalSpace (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).topology
        let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
          (X.term (subseq (co.φ k))).charted
        let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
          (X.term (subseq (co.φ k))).smooth
        ENNReal.ofReal (redDensity (X.term (subseq (co.φ k))).S T
          (Phi.map (co.φ k) x)
          (Phi.map (co.φ k) ((extChartAt I alpha).symm z)) tau) ≤
            (Cred : ENNReal)) :
    let : TopologicalSpace (L.atTime 0).M := (L.atTime 0).topology
    let : ChartedSpace H (L.atTime 0).M := (L.atTime 0).charted
    let : IsManifold I ∞ (L.atTime 0).M := (L.atTime 0).smooth
    let : TopologicalSpace L.M := L.topology
    let : ChartedSpace H L.M := L.charted
    let : IsManifold I ∞ L.M := L.smooth
    Tendsto
      (fun k ↦ ∫⁻ z in B,
        ENNReal.ofReal (chartDensity (I := I)
          (gSeqExt (I := I) Phi R bf hSrc hTgt (co.φ k) (T - tau)) alpha
          ((extChartAt I alpha).symm z)) *
        (let : TopologicalSpace (X.term (subseq (co.φ k))).M := (X.term (subseq (co.φ k))).topology
         let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
            (X.term (subseq (co.φ k))).charted
         let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
            (X.term (subseq (co.φ k))).smooth
         ENNReal.ofReal (redDensity (X.term (subseq (co.φ k))).S T
           (Phi.map (co.φ k) x)
           (Phi.map (co.φ k) ((extChartAt I alpha).symm z)) tau))
        ∂(modelHaar (E := E)))
      atTop
      (nhds (∫⁻ z in B,
        ENNReal.ofReal (chartDensity (I := I) (co.gInf (T - tau)) alpha
          ((extChartAt I alpha).symm z)) *
        ENNReal.ofReal (redDensity L.S T x ((extChartAt I alpha).symm z) tau)
        ∂(modelHaar (E := E)))) := by
  have h := FlowMetricConvergenceData.tendsto_lintegral_mul_chartDensity_mul_redDensity Phi R bf hSrc hTgt beta psi co
    T tau x alpha hTime hBChart hBc (fun _ => 1) aemeasurable_const
    (by simpa only [lintegral_const, Measure.restrict_apply_univ, one_mul] using hBc.measure_lt_top)
    hRedMeas hRedLim Cred hRedBd
  simpa only [one_mul] using h

end DifferentialGeometry.CheegerGromovCompactness
