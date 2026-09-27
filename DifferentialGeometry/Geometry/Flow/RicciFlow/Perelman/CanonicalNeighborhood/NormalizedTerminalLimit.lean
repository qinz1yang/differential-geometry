import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedMetricLimit
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedReindexing
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedRescaling
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalOrientation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalLimitConstruction

noncomputable section
open Filter Set
open scoped Topology Manifold ContDiff ENNReal
namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
universe u
attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

private theorem terminalCurvatureRescale_atTime_zero
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ} (X : NormalizedSequence.{u} eps kappa sigma Phi)
    (f : ℕ → ℕ) (hf : StrictMono f) (x : ∀ i, (X.term (f i)).M)
    (hQ : ∀ i, 1 ≤ (X.term (f i)).S.scalar 0 (x i)) :
    ((X.reindex f hf).terminalCurvatureRescale x hQ).toFlowSequence.atTime 0 =
      X.terminalCurvatureRescaledSequence f x (fun i => zero_lt_one.trans_le (hQ i)) := by
  simp only [FlowSequence.atTime, NormalizedSequence.terminalCurvatureRescale_toFlowSequence,
    FlowSequence.terminalCurvatureRescale,
    NormalizedSequence.terminalCurvatureRescaledSequence, NormalizedSequence.reindex,
    PointedFlowData.atTime, SolutionOn.family, parabolicSolution_metric, parabolicTime_zero]


theorem exists_noncompact_terminalLimit_of_not_boundedAtDistance
    {kappa : ℝ} (hkappa : 0 < kappa) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ sigma : ℝ, 0 < sigma → ∀ Phi : ℝ → ℝ, AdmissiblePinchingFunction Phi →
        ∀ X : NormalizedSequence.{u} eps kappa sigma Phi, ¬ BoundedAtDistance X →
          ∃ D : ℝ, 0 < D ∧ ∃ f : ℕ → ℕ, ∃ hf : StrictMono f,
            ∃ (x : ∀ i, (X.term (f i)).M) (r : ℕ → ℝ)
              (hQ : ∀ i, 1 ≤ (X.term (f i)).S.scalar 0 (x i)),
              (∀ i, 0 < r i) ∧
              Tendsto (fun i => (X.term (f i)).S.scalar 0 (x i)) atTop atTop ∧
              Tendsto (fun i => (X.term (f i)).S.scalar 0 (x i) * r i ^ 2) atTop atTop ∧
              (∀ i y, metricDistance ((X.term (f i)).S.base.metric 0) (x i) y ≤ r i →
                metricDistance ((X.term (f i)).S.base.metric 0) (X.term (f i)).basepoint y < D ∧
                (X.term (f i)).S.scalar 0 y ≤ 2 * (X.term (f i)).S.scalar 0 (x i)) ∧
              ∃ L : TerminalLimit ((X.reindex f hf).terminalCurvatureRescale x hQ),
                NoncompactSpace L.space.M ∧
                (∀ y : L.space.M, metricScalarAt L.space.metric y ≤ 2) := by
  obtain ⟨epsStar, hepsStar, hlimit⟩ :=
    exists_terminalCurvatureRescaledSequence_noncompact_metric_limit_of_not_boundedAtDistance.{u}
      hkappa
  refine ⟨epsStar, hepsStar, ?_⟩
  intro eps heps hle sigma hsigma Phi hPhi X hfail
  obtain ⟨D, hD, f, hf, x, r, hpos, hQ, hr, hlarge, hQr, hcontrol,
    P, hcanonical, hconnected, hnoncompact, hcompact, hsourceconn, hnested, _, hupper, _, hnc⟩ :=
    hlimit eps heps hle sigma hsigma Phi hPhi X hfail
  let Y := (X.reindex f hf).terminalCurvatureRescale x hQ
  have hP : ∃ P : MetricCompactLimit (Y.toFlowSequence.atTime 0),
      (∀ k, P.convergence.metrics.domain k =
        CanonicalMetricCompactness.canonicalSourceData P.maps k) ∧
      ConnectedSpace P.limit.M ∧ NoncompactSpace P.limit.M ∧
      (∀ i, IsCompact (closure (P.maps.source i))) ∧
      (∀ i, IsConnected (P.maps.source i)) ∧
      (∀ i, closure (P.maps.source i) ⊆ P.maps.source (i + 1)) ∧
      (∀ y : P.limit.M, metricScalarAt P.limit.metric y ≤ 2) ∧
      ∃ kappa' : ℝ, 0 < kappa' ∧ MetricNoncollapsed P.limit kappa' univ := by
    dsimp only [Y]
    rw [terminalCurvatureRescale_atTime_zero X f hf x hQ]
    exact ⟨P, hcanonical, hconnected, hnoncompact, hcompact, hsourceconn, hnested, hupper, hnc⟩
  obtain ⟨P, hcanonical, hconnected, hnoncompact, hcompact, hsourceconn, hnested, hupper, hnc⟩ := hP
  have hcapture := metricSourceCapture_of_metricConvergenceData P.convergence.metrics
    (fun i => by rw [hcanonical i]; rfl) P.limit_complete
  obtain ⟨s, hs, o, _, hcanonical', hcapture', hcompact', hsourceconn', hnested', horientation⟩ :=
    exists_oriented_subsequence_with_canonical_domains P.strictMono P.maps P.convergence.metrics
      hcanonical hcapture hcompact hsourceconn hnested Y.orientation
  let Q := P.compSubseq s hs
  obtain ⟨kappa', hkappa', hnc⟩ := hnc
  let L := TerminalLimit.ofMetricCompactLimit hPhi Q hcanonical' hcapture' hcompact'
    hsourceconn' hnested' o horientation ⟨2, hupper⟩
    ⟨kappa', hkappa', fun y r _ => hnc y r (mem_univ r)⟩ hconnected
  exact ⟨D, hD, f, hf, x, r, hQ, hr, hlarge, hQr, hcontrol, L, hnoncompact, hupper⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
