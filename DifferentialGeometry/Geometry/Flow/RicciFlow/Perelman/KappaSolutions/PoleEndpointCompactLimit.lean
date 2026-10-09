import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Limits.HalfLineMetricData
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PoleEndpointInjectivity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.AncientMetricMonotonicity

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle Filter Set
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.CheegerGromovCompactness
open CanonicalNeighborhood
open scoped _root_.Manifold ContDiff _root_.Topology ENNReal

universe u uE uH

section Inner

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E] [NeZero (Module.finrank ℝ E)]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {D : RealTimeInterval} (F : PointedFlowData.{u, uE, uH} (I := I) D)

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem exists_complete_halfLineMetricConvergenceData_of_poleEndpoint_redLength_bound
    {kappa : ℝ} (hF : IsAncientKappaSolution kappa F)
    (p : F.M) (b : ℝ) (hbmem : b ∈ D.carrier)
    (tau : ℕ → ℝ) (q : ℕ → F.M) (hsigma : ∀ i, 0 < tau i + b)
    (hancient : ∀ i, IsAncientKappaSolution kappa
      ((poleRescaledFlowSeq F hF.carrier_eq hF.regular_eq b hbmem tau q hsigma).term i))
    {A : ℝ} (hbase : ∀ i, redLength
      ((poleRescaledFlowSeq F hF.carrier_eq hF.regular_eq b hbmem tau q hsigma).term i).S
      0 p (q i) 1 ≤ A) :
    let Y := poleEndpointRescaledFlowSeq F hF.carrier_eq hF.regular_eq b hbmem tau q hsigma
    ∃ (P : PointedRiemannianManifold.{u, uE, uH} (I := I)) (phi : ℕ → ℕ),
      StrictMono phi ∧ ∃ (Phi : PointedCGHMaps Y P phi)
        (R : SmoothRiemannianMetric I P.M),
        R = P.metric ∧ RiemannianMetricComplete R ∧
        ∃ (bf : BumpFamily Phi) (hsrc : SourceIsSigmaCompact Phi)
          (htgt : TargetIsSigmaCompact Phi)
          (co : HalfLineMetricConvergenceData Phi R bf hsrc htgt),
          ConnectedSpace P.M ∧ ∀ t : ℝ, t ≤ 0 →
            MetricComplete ({ P with metric := co.gInf t } : PointedRiemannianManifold I) := by
  intro Y
  have hYcomplete : FlowMetricComplete Y :=
    poleEndpointRescaledFlowSeq_complete F hF.carrier_eq hF.regular_eq
      b hbmem tau q hsigma (fun t ht => ⟨hF.complete t ht⟩)
  have hYconnected : ∀ i, ConnectedSpace (Y.term i).M := fun _ => hF.connected
  obtain ⟨hinj⟩ := nonempty_poleEndpointRescaledFlowSeq_baseInjBound
    F hF.carrier_eq hF.regular_eq b hbmem tau q hsigma hF hancient p hbase
  have hlocal : ∀ A : ℝ, 0 < A → ∀ T : ℝ, 0 < T → ∃ K : ℝ, 0 ≤ K ∧
      ∀ᶠ i in atTop, ∀ t ∈ Icc (-T) 0, ∀ x : (Y.term i).M,
        riemannianEDistOf ((Y.term i).S.base.metric 0) (Y.term i).basepoint x ≤
          ENNReal.ofReal A → (Y.term i).rmNormSq (I := I) t x ≤ K := by
    intro A hA T _
    obtain ⟨K, hK, hcurv⟩ := exists_poleEndpointRescaledFlowSeq_local_curvature_bound
      F hF.carrier_eq hF.regular_eq b hbmem tau q hsigma
        (fun _ => kappa) hancient p hbase A hA.le
    refine ⟨K, hK, Eventually.of_forall ?_⟩
    intro i t ht x hx
    exact hcurv i t ht.2 x hx
  have hlower : ∀ T : ℝ, 0 < T → ∃ c : ℝ, 0 < c ∧
      ∀ᶠ i in atTop, ∀ t ∈ Icc (-T) 0, ∀ x : (Y.term i).M,
        ∀ v : TangentSpace I x,
          c * ((Y.term i).S.base.metric 0).inner x v v ≤
            ((Y.term i).S.base.metric t).inner x v v := by
    intro T _
    refine ⟨1, zero_lt_one, Eventually.of_forall ?_⟩
    intro i t ht x v
    have hRic : ∀ s ∈ Ioo t 0, ∀ y : (Y.term i).M, ∀ w : TangentSpace I y,
        0 ≤ (Y.term i).S.ricciAt s y (vec2 w w) := by
      intro s hs y w
      apply metricRicciAt_nonnegative_of_curvatureOperator_nonnegative
      apply (metricAlgebraicCurvatureTensorAt_mem_curvatureOperatorNonnegativeCone_iff
        (I := I) ((Y.term i).S.base.metric s) y).mpr
      intro n c a d
      simpa [SolutionFamily.rm04, metricRm04StandardAt_apply, vec4] using
        poleEndpointRescaledFlowSeq_nonnegativeCurvatureOperator
          F hF.carrier_eq hF.regular_eq b hbmem tau q hsigma
          hF.nonnegativeCurvatureOperator i hs.2.le y n c a d
    have hanti := metric_inner_antitoneOn_of_ricci_nonnegative_interior
      (Y.term i).S (Y.term i).isSolution (a := t) (b := 0)
      (fun s hs => hs.2) (fun s hs => hs.2) hRic x v
    simpa only [one_mul] using hanti ⟨le_rfl, ht.2⟩ ⟨ht.2, le_rfl⟩ ht.2
  exact exists_complete_halfLineMetricConvergenceData_of_local_curvature_bound
    Y rfl hYcomplete hYconnected hinj hlocal hlower

end Inner

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions
