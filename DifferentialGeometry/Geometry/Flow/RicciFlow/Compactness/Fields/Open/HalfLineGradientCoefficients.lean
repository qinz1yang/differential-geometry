import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.GradientCoefficients
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Fields.Open.HalfLineRegularity
import DifferentialGeometry.Analysis.Integration.Measure.VolumeDensityFamily


noncomputable section

namespace DifferentialGeometry.CheegerGromovCompactness

open Bundle Set
open Geometry.Curvature Geometry.Operator Integral.Measure
open scoped _root_.Manifold ContDiff _root_.Topology

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {X : PointedFlowSeq (I := I)} {P : PointedRiemannianManifold (I := I)}
  {subseq : ℕ → ℕ} (Φ : PointedCGHMaps X P subseq)

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

attribute [local instance] PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] in
private theorem continuousOn_chart_pullback
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    {F : Type*} [TopologicalSpace F] {J : Set ℝ} (α : M)
    (f : ℝ × M → F)
    (hf : ContinuousOn f (J ×ˢ (trivializationAt E (TangentSpace I) α).baseSet)) :
    ContinuousOn (fun z : ℝ × E => f (z.1, (extChartAt I α).symm z.2))
      (J ×ˢ (extChartAt I α).target) := by
  have hchart : ContinuousOn (fun z : ℝ × E => (extChartAt I α).symm z.2)
      (J ×ˢ (extChartAt I α).target) :=
    (continuousOn_extChartAt_symm (I := I) α).comp
      (continuous_snd.continuousOn : ContinuousOn (fun z : ℝ × E => z.2)
        (J ×ˢ (extChartAt I α).target)) (fun _ hz => hz.2)
  have hpair : ContinuousOn (fun z : ℝ × E => (z.1, (extChartAt I α).symm z.2))
      (J ×ˢ (extChartAt I α).target) :=
    continuous_fst.continuousOn.prodMk hchart
  exact hf.comp hpair
    (fun z hz => ⟨hz.1,
      Tensor.Coordinates.extChartAt_symm_mem_trivializationAt_baseSet (I := I) α hz.2⟩)

namespace HalfLineMetricConvergenceData

variable {R : SmoothRiemannianMetric I P.M}
  {bf : BumpFamily Φ} {hsrc : SourceIsSigmaCompact Φ} {htgt : TargetIsSigmaCompact Φ}
  (co : HalfLineMetricConvergenceData Φ R bf hsrc htgt)

theorem continuousOn_chartDensity
    (hreg : Iio 0 ⊆ X.D.regular) (α : P.M) :
    ContinuousOn (fun z : ℝ × E =>
      chartDensity (co.gInf z.1) α ((extChartAt I α).symm z.2))
      (Iio 0 ×ˢ (extChartAt I α).target) := by
  have hc : ContinuousOn
      (fun p : ℝ × P.M => chartDensity (I := I) (co.gInf p.1) α p.2)
      (Iio 0 ×ˢ (trivializationAt E (TangentSpace I) α).baseSet) :=
    (chartDensity_family_contMDiffOn (I := I) (M := P.M) co.gInf α
      (gramSmooth (I := I) (Φ := Φ) co hreg α)).continuousOn
  exact continuousOn_chart_pullback (I := I) α _ hc

theorem continuousOn_chartGradientBilin
    (hreg : Iio 0 ⊆ X.D.regular) (α : P.M) :
    ContinuousOn (fun z : ℝ × E =>
      chartGradientBilin (co.gInf z.1) α ((extChartAt I α).symm z.2))
      (Iio 0 ×ˢ (extChartAt I α).target) := by
  let G : MetricConnectionFamilyOn (I := I) (M := P.M) X.D :=
    (lcMetricFamily (I := I) co.gInf).restrict X.D
  have hgram : ContinuousOn (chartGramOp G α) (Iio 0 ×ˢ (extChartAt I α).target) := by
    apply Geometry.Curvature.continuousOn_chartGramOp
    intro i j
    exact continuousOn_chart_pullback (I := I) α _
      ((gramSmooth (I := I) (Φ := Φ) co hreg α i j).continuousOn)
  have hc := Geometry.Curvature.continuousOn_smul_chartGradientBilin G α
    (fun z hz => hz.2) hgram (fun _ => (1 : ℝ)) continuousOn_const
  simpa only [one_smul, G, MetricConnectionFamily.restrict_metric, lcMetricFamily] using hc

end HalfLineMetricConvergenceData

end DifferentialGeometry.CheegerGromovCompactness
