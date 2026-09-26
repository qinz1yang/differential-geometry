import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.LocalCurvatureInjectivity
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.StaircaseCompactnessReduction
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalLimitInjectivityTransfer
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalOrientation
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.NormalizedNoncollapse

set_option autoImplicit false
noncomputable section

open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.CheegerGromovCompactness DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

theorem NormalizedSequence.localCurvatureJetBound_atTime_zero
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) (h : TerminalDerivativeBounds X) :
    KappaSolutions.LocalCurvatureJetBound (I := I3) (X.toFlowSequence.atTime 0) := by
  intro rho hrho a
  obtain ⟨C, hC⟩ := h rho hrho a
  refine ⟨max C 0, le_max_right _ _, Filter.Eventually.of_forall fun i y hy => ?_⟩
  have hdist : metricDistance ((X.term i).S.base.metric 0) (X.term i).basepoint y ≤ rho := by
    have ht := ENNReal.toReal_mono ENNReal.ofReal_ne_top hy
    rw [ENNReal.toReal_ofReal hrho.le] at ht
    convert ht using 1
    with_unfolding_all rfl
  exact (hC i y hdist).trans (le_max_left _ _)

theorem NormalizedSequence.exists_oriented_metric_compact_limit
    {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (X : NormalizedSequence.{u} eps kappa sigma Phi) {kappa' : ℝ}
    (hnc : X.TerminalSliceNoncollapsed kappa') (hd : TerminalDerivativeBounds X) :
    ∃ P : MetricCompactLimit.{u, 0, 0} (I := I3) (X.toFlowSequence.atTime 0),
      (∀ k, P.convergence.metrics.domain k =
        CanonicalMetricCompactness.canonicalSourceData P.maps k) ∧
      ConnectedSpace P.limit.M ∧ MetricSourceCapture P.maps ∧
      (∀ i, IsCompact (closure (P.maps.partialDiffeomorph i).source)) ∧
      (∀ i, IsConnected (P.maps.partialDiffeomorph i).source) ∧
      (∀ i, closure (P.maps.partialDiffeomorph i).source ⊆
        (P.maps.partialDiffeomorph (i + 1)).source) ∧
      (∃ o : TangentOrientationSection P.limit.M,
        ∀ i y, y ∈ (P.maps.partialDiffeomorph i).source →
          ∃ hf : Function.Bijective (mfderiv I3 I3 (P.maps.partialDiffeomorph i) y),
            PreservesTangentOrientationAt o (X.orientation (P.subseq i))
              (P.maps.partialDiffeomorph i) y hf) ∧
      MetricNoncollapsed P.limit kappa' (Set.Ioc 0 1) := by
  let : NeZero (Module.finrank ℝ ThreeSpace) := ⟨by simp [ThreeSpace]⟩
  have hcomplete : SeqMetricComplete (X.toFlowSequence.atTime 0) := by
    refine ⟨fun i => X.complete i 0 ?_⟩
    rw [X.carrier_eq i]
    exact ⟨by linarith [X.depth_pos i], le_rfl⟩
  obtain ⟨P, hcanonical, hreference, hconnected, hprecompact, hsourceConnected, hnested⟩ :=
    exists_canonical_metric_compact_limit_with_source_geometry_of_local_curvature_injectivity
      (X.toFlowSequence.atTime 0) hcomplete X.connected
      (X.localCurvatureJetBound_atTime_zero hd)
      (terminalLimitBallInjectivity_of_curvatureAndNoncollapse X hnc hd)
  have hcapture := metricSourceCapture_of_metricConvergenceData P.convergence.metrics
    hreference P.limit_complete
  obtain ⟨σ, hσ, o, _, hcanonical', hcapture', hprecompact', hsourceConnected', hnested',
      horientation⟩ := exists_oriented_subsequence_with_canonical_domains
    P.strictMono P.maps P.convergence.metrics hcanonical hcapture hprecompact
    hsourceConnected hnested X.orientation
  let Q := P.compSubseq σ hσ
  refine ⟨Q, hcanonical', hconnected, hcapture', hprecompact', hsourceConnected', hnested',
    ⟨o, horientation⟩, ?_⟩
  exact X.metric_noncollapsed_of_canonical_convergence hnc Q.limit Q.subseq Q.strictMono
    Q.maps Q.convergence.metrics hcanonical' Q.limit_complete

theorem terminal_limit_compactness_frontier {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hPhi : AdmissiblePinchingFunction Phi) :
    TerminalLimitCompactnessFrontier.{u} kappa sigma Phi := by
  obtain ⟨epsNC, hepsNC, hnc⟩ := exists_terminalSliceNoncollapsed.{u} hkappa
  obtain ⟨kappa', hkappa', hncX⟩ := hnc Phi hPhi
  refine ⟨epsNC, hepsNC, fun eps heps hle X _ hd => ?_⟩
  obtain ⟨P, h1, h2, h3, h4, h5, h6, h7, h8⟩ :=
    X.exists_oriented_metric_compact_limit (hncX eps heps hle sigma X) hd
  exact ⟨P, h1, h2, h3, h4, h5, h6, h7, kappa', hkappa', h8⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
