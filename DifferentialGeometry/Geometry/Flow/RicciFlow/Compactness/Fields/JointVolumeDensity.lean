import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.VolumeConvergence

noncomputable section

open Set Filter Bundle
open scoped Manifold Topology ContDiff

namespace DifferentialGeometry.CheegerGromovCompactness

open Geometry.Curvature Geometry.Operator Integral.Measure Tensor.Coordinates

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {X : PointedFlowSeq.{u, uE, uH} (I := I)}
variable {P : PointedRiemannianManifold.{u, uE, uH} (I := I)}
variable {subseq : ℕ → ℕ}
variable (Φ : PointedCGHMaps (I := I) X P subseq)

theorem continuousOn_chartDensity_gSeqExt [I.Boundaryless]
    (R : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      let : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    (k : ℕ) (alpha : P.M) {K : Set E}
    (hKchart : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      K ⊆ (extChartAt I alpha).target) :
    let : TopologicalSpace P.M := P.topology
    let : ChartedSpace H P.M := P.charted
    let : T2Space P.M := P.t2
    let : IsManifold I ∞ P.M := P.smooth
    let : SigmaCompactSpace P.M := P.sigmaCompact
    ContinuousOn
      (fun q : ℝ × E => chartDensity (gSeqExt (I := I) Φ R bf hsrc htgt k q.1)
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
  have hGram : ContinuousOn (chartGramOp G alpha) (X.D.carrier ×ˢ K) :=
    continuousOn_chartGramOp_gSeqExt Φ R bf hsrc htgt k alpha hKchart
  have hdet : Continuous (fun A : E →L[ℝ] E =>
      Real.sqrt (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
        inner ℝ (A (chartModelBasis E i)) (chartModelBasis E j)).det) := by
    apply Real.continuous_sqrt.comp
    apply Continuous.matrix_det
    apply continuous_matrix
    intro i j
    exact (ContinuousLinearMap.apply ℝ E (chartModelBasis E i)).continuous.inner
      continuous_const
  change ContinuousOn
    (fun q : ℝ × E => chartDensity (G.metric q.1) alpha ((extChartAt I alpha).symm q.2))
    (X.D.carrier ×ˢ K)
  simpa only [chartDensity_eq_sqrt_det_chartGramOp, Function.comp_def] using
    hdet.comp_continuousOn hGram

theorem FlowMetricConvergenceData.continuousOn_chartDensity [I.Boundaryless]
    (R : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      let : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    (beta psi : ℝ) (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt beta psi)
    (alpha : P.M) {K : Set E}
    (hKchart : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      K ⊆ (extChartAt I alpha).target) (hKc : IsCompact K)
    (hcarrier : Icc beta psi ⊆ X.D.carrier) :
    let : TopologicalSpace P.M := P.topology
    let : ChartedSpace H P.M := P.charted
    let : T2Space P.M := P.t2
    let : IsManifold I ∞ P.M := P.smooth
    let : SigmaCompactSpace P.M := P.sigmaCompact
    ContinuousOn
      (fun q : ℝ × E => chartDensity (co.gInf q.1) alpha ((extChartAt I alpha).symm q.2))
      (Icc beta psi ×ˢ K) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  let G : MetricConnectionFamilyOn (I := I) (M := P.M) X.D :=
    (lcMetricFamily (I := I) (M := P.M) co.gInf).restrict X.D
  have hGram : ContinuousOn (chartGramOp G alpha) (Icc beta psi ×ˢ K) :=
    co.continuousOn_chartGramOp Φ R bf hsrc htgt beta psi alpha hKchart hKc hcarrier
  have hdet : Continuous (fun A : E →L[ℝ] E =>
      Real.sqrt (Matrix.of fun i j : Fin (Module.finrank ℝ E) =>
        inner ℝ (A (chartModelBasis E i)) (chartModelBasis E j)).det) := by
    apply Real.continuous_sqrt.comp
    apply Continuous.matrix_det
    apply continuous_matrix
    intro i j
    exact (ContinuousLinearMap.apply ℝ E (chartModelBasis E i)).continuous.inner
      continuous_const
  change ContinuousOn
    (fun q : ℝ × E => chartDensity (G.metric q.1) alpha ((extChartAt I alpha).symm q.2))
    (Icc beta psi ×ˢ K)
  simpa only [chartDensity_eq_sqrt_det_chartGramOp, Function.comp_def] using
    hdet.comp_continuousOn hGram

theorem FlowMetricConvergenceData.tendstoUniformlyOn_chartDensity_prod [I.Boundaryless]
    (R : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      let : IsManifold I ∞ P.M := P.smooth
      SmoothRiemannianMetric I P.M)
    (bf : BumpFamily (I := I) Φ) (hsrc : SourceIsSigmaCompact Φ) (htgt : TargetIsSigmaCompact Φ)
    (beta psi : ℝ) (co : FlowMetricConvergenceData (I := I) Φ R bf hsrc htgt beta psi)
    (alpha : P.M) {K : Set E}
    (hKchart : let : TopologicalSpace P.M := P.topology
      let : ChartedSpace H P.M := P.charted
      K ⊆ (extChartAt I alpha).target) (hKc : IsCompact K)
    (hcarrier : Icc beta psi ⊆ X.D.carrier) :
    let : TopologicalSpace P.M := P.topology
    let : ChartedSpace H P.M := P.charted
    let : T2Space P.M := P.t2
    let : IsManifold I ∞ P.M := P.smooth
    let : SigmaCompactSpace P.M := P.sigmaCompact
    TendstoUniformlyOn
      (fun k (q : ℝ × E) =>
        chartDensity (gSeqExt (I := I) Φ R bf hsrc htgt (co.φ k) q.1)
          alpha ((extChartAt I alpha).symm q.2))
      (fun q => chartDensity (co.gInf q.1) alpha ((extChartAt I alpha).symm q.2))
      atTop (Icc beta psi ×ˢ K) := by
  let : TopologicalSpace P.M := P.topology
  let : ChartedSpace H P.M := P.charted
  let : T2Space P.M := P.t2
  let : IsManifold I ∞ P.M := P.smooth
  let : SigmaCompactSpace P.M := P.sigmaCompact
  rw [tendstoUniformlyOn_iff_tendstoUniformly_comp_coe]
  apply co.tendstoUniformly_chartDensity_of_subset_carrier Φ R bf hsrc htgt beta psi
    alpha hKchart hKc hcarrier
    (Q := ↥(Icc beta psi ×ˢ K))
    (tau := fun q => q.1.1) (u := fun _ q => q.1.2) (uLim := fun q => q.1.2)
  · exact fun q => q.2.1
  · exact Eventually.of_forall fun _ q => q.2.2
  · exact fun q => q.2.2
  · rw [Metric.tendstoUniformly_iff]
    intro ε hε
    exact Eventually.of_forall fun _ q => by simpa only [dist_self] using hε

end DifferentialGeometry.CheegerGromovCompactness
