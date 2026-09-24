import DifferentialGeometry.Geometry.Metric.Family.GradientCoefficients
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.GramConvergence

noncomputable section

open Set Filter Bundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

open Geometry.Curvature Geometry.Operator Integral.Measure

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {X : PointedFlowSeq.{u, uE, uH} (I := I)}
variable {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
variable {subseq : ℕ → ℕ}
variable (Φ : PointedCGHMaps (I := I) X P subseq)

private local instance covectorNormedAddCommGroup : NormedAddCommGroup (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorNormedSpace : NormedSpace ℝ (E →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance covectorDualNormedAddCommGroup : NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorDualNormedSpace : NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

private local instance covectorBilinNormedAddCommGroup :
    NormedAddCommGroup ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup

private local instance covectorBilinNormedSpace :
    NormedSpace ℝ ((E →L[ℝ] ℝ) →L[ℝ] (E →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem continuousOn_chartDensity_smul_chartGradientBilin_gSeqExt [I.Boundaryless]
    (R : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      let : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ)
    (htgt : TargetIsSigmaCompact Φ)
    (k : ℕ)
    (alpha : P.M) {K : Set E}
    (hKchart : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      K ⊆ (extChartAt I alpha).target)
    (w : ℝ × E → ℝ) (hw : ContinuousOn w (X.D.carrier ×ˢ K)) :
    let : TopologicalSpace P.M := P.topology
    let : ChartedSpace H P.M := P.charted
    let : T2Space P.M := P.t2
    let : IsManifold I ∞ P.M := P.smooth
    let : SigmaCompactSpace P.M := P.sigmaCompact
    ContinuousOn
      (fun q : ℝ × E =>
        (w q * chartDensity (gSeqExt (I := I) Φ R bf hsrc htgt k q.1)
          alpha ((extChartAt I alpha).symm q.2)) •
        chartGradientBilin (gSeqExt (I := I) Φ R bf hsrc htgt k q.1)
          alpha ((extChartAt I alpha).symm q.2))
      (X.D.carrier ×ˢ K) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let G : MetricConnectionFamilyOn (I := I) (M := P.M) X.D :=
    (lcMetricFamily (I := I) (M := P.M)
      (fun t => gSeqExt (I := I) Φ R bf hsrc htgt k t)).restrict X.D
  exact continuousOn_chartDensity_smul_chartGradientBilin G alpha
    (fun q hq => hKchart hq.2)
    (continuousOn_chartGramOp_gSeqExt Φ R bf hsrc htgt k alpha hKchart) w hw

theorem FlowMetricConvergenceData.continuousOn_chartDensity_smul_chartGradientBilin [I.Boundaryless]
    (R : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      let : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ)
    (htgt : TargetIsSigmaCompact Φ)
    (beta psi : ℝ) (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt beta psi)
    (alpha : P.M) {K : Set E}
    (hKchart : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      K ⊆ (extChartAt I alpha).target) (hKc : IsCompact K)
    (hcarrier : Icc beta psi ⊆ X.D.carrier)
    (w : ℝ × E → ℝ) (hw : ContinuousOn w (Icc beta psi ×ˢ K)) :
    let : TopologicalSpace P.M := P.topology
    let : ChartedSpace H P.M := P.charted
    let : T2Space P.M := P.t2
    let : IsManifold I ∞ P.M := P.smooth
    let : SigmaCompactSpace P.M := P.sigmaCompact
    ContinuousOn
      (fun q : ℝ × E =>
        (w q * chartDensity (co.gInf q.1) alpha ((extChartAt I alpha).symm q.2)) •
        chartGradientBilin (co.gInf q.1) alpha ((extChartAt I alpha).symm q.2))
      (Icc beta psi ×ˢ K) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let G : MetricConnectionFamilyOn (I := I) (M := P.M) X.D :=
    (lcMetricFamily (I := I) (M := P.M) co.gInf).restrict X.D
  exact Geometry.Curvature.continuousOn_chartDensity_smul_chartGradientBilin G alpha
    (fun q hq => hKchart hq.2)
    (co.continuousOn_chartGramOp Φ R bf hsrc htgt beta psi alpha hKchart hKc hcarrier) w hw

theorem FlowMetricConvergenceData.tendstoUniformlyOn_chartDensity_smul_chartGradientBilin
    [I.Boundaryless]
    (R : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      let : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ)
    (htgt : TargetIsSigmaCompact Φ)
    (beta psi : ℝ) (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt beta psi)
    (alpha : P.M) {K : Set E}
    (hKchart : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      K ⊆ (extChartAt I alpha).target) (hKc : IsCompact K)
    (hcarrier : Icc beta psi ⊆ X.D.carrier)
    (w : ℝ × E → ℝ) (hw : ContinuousOn w (Icc beta psi ×ˢ K)) :
    let : TopologicalSpace P.M := P.topology
    let : ChartedSpace H P.M := P.charted
    let : T2Space P.M := P.t2
    let : IsManifold I ∞ P.M := P.smooth
    let : SigmaCompactSpace P.M := P.sigmaCompact
    TendstoUniformlyOn
      (fun k (q : ℝ × E) =>
        (w q * chartDensity (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) q.1)
          alpha ((extChartAt I alpha).symm q.2)) •
        chartGradientBilin (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) q.1)
          alpha ((extChartAt I alpha).symm q.2))
      (fun q =>
        (w q * chartDensity (co.gInf q.1) alpha ((extChartAt I alpha).symm q.2)) •
        chartGradientBilin (co.gInf q.1) alpha ((extChartAt I alpha).symm q.2))
      atTop (Icc beta psi ×ˢ K) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let GSeq : ℕ → MetricConnectionFamilyOn (I := I) (M := P.M) X.D := fun k =>
    (lcMetricFamily (I := I) (M := P.M)
      (fun t => gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) t)).restrict X.D
  let GInf : MetricConnectionFamilyOn (I := I) (M := P.M) X.D :=
    (lcMetricFamily (I := I) (M := P.M) co.gInf).restrict X.D
  exact Geometry.Curvature.tendstoUniformlyOn_chartDensity_smul_chartGradientBilin
    GSeq GInf alpha (isCompact_Icc.prod hKc) (fun q hq => hKchart hq.2)
    (co.continuousOn_chartGramOp Φ R bf hsrc htgt beta psi alpha hKchart hKc hcarrier)
    (co.tendstoUniformlyOn_chartGramOp Φ R bf hsrc htgt beta psi alpha hKchart hKc)
    w hw

end DifferentialGeometry.CheegerGromovCompactness
