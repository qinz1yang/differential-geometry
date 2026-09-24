import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.IntegralConvergence
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
  let : TopologicalSpace L.M := L.topology
  let : ChartedSpace H L.M := L.charted
  let : IsManifold I ∞ L.M := L.smooth
  exact co.tendsto_lintegral_mul_chartDensity_mul_density Phi R bf hSrc hTgt
    beta psi (T - tau) alpha
    (fun k =>
      let : TopologicalSpace (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).topology
      let : ChartedSpace H (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).charted
      let : IsManifold I ∞ (X.term (subseq (co.φ k))).M :=
        (X.term (subseq (co.φ k))).smooth
      fun y => redDensity (X.term (subseq (co.φ k))).S T (Phi.map (co.φ k) x) y tau)
    (fun y => redDensity L.S T x y tau)
    hTime hBChart hBc w hw hwInt hRedMeas hRedLim Cred hRedBd

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
