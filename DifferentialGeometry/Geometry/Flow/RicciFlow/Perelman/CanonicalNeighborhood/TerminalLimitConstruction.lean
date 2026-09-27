import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.BlowupConvergence
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.KappaSolutions.PointedScalarConvergence

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped _root_.Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

def TerminalLimit.ofMetricCompactLimit {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} (hPhi : AdmissiblePinchingFunction Phi)
    (P : MetricCompactLimit.{u, 0, 0} (I := I3) (X.toFlowSequence.atTime 0))
    (hcanonical : ∀ k, P.convergence.metrics.domain k =
      CanonicalMetricCompactness.canonicalSourceData P.maps k)
    (capture : MetricSourceCapture P.maps)
    (precompact : ∀ i, IsCompact (closure (P.maps.partialDiffeomorph i).source))
    (connected_domains : ∀ i, IsConnected (P.maps.partialDiffeomorph i).source)
    (nested : ∀ i, closure (P.maps.partialDiffeomorph i).source ⊆
      (P.maps.partialDiffeomorph (i + 1)).source)
    (orientation : TangentOrientationSection P.limit.M)
    (orientation_preserved : ∀ i y, y ∈ (P.maps.partialDiffeomorph i).source →
      ∃ hf : Function.Bijective (mfderiv I3 I3 (P.maps.partialDiffeomorph i) y),
        PreservesTangentOrientationAt orientation (X.orientation (P.subseq i))
          (P.maps.partialDiffeomorph i) y hf)
    (scalar_bound : ∃ C : ℝ, ∀ x, metricScalarAt P.limit.metric x ≤ C)
    (noncollapse : ∃ kappa' : ℝ, 0 < kappa' ∧ MetricNoncollapsed P.limit kappa' (Set.Ioc 0 1))
    (hconnected : ConnectedSpace P.limit.M) :
    TerminalLimit X := by
  have hscalar_one : metricScalarAt P.limit.metric P.limit.basepoint = 1 :=
    DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions.pointedScalar_base_eq_of_metricCG_canonical_domains
      P.convergence.metrics hcanonical
      (c := 1) (fun k => by
        have hk := X.base_one (P.subseq k)
        simp only [PointedFlowScalarAtBase, SolutionOn.scalar, SolutionFamily.scalar] at hk ⊢
        exact hk)
  exact {
    space := P.limit
    subseq := P.subseq
    strictMono := P.strictMono
    maps := P.maps
    converges := P.convergence.metrics
    canonical_domains := hcanonical
    capture := capture
    precompact := precompact
    connected_domains := connected_domains
    nested := nested
    connected := hconnected
    orientation := orientation
    orientation_preserved := orientation_preserved
    complete := P.limit_complete
    nonnegative := blowup_limit_nonnegative X hPhi
      P.limit P.subseq P.strictMono P.maps P.convergence.metrics hcanonical
    scalar_one := hscalar_one
    scalar_bound := scalar_bound
    noncollapse := noncollapse }

theorem terminal_limit_of_metric_compact_limit {eps kappa sigma : ℝ} {Phi : ℝ → ℝ}
    {X : NormalizedSequence.{u} eps kappa sigma Phi} (hPhi : AdmissiblePinchingFunction Phi)
    (P : MetricCompactLimit.{u, 0, 0} (I := I3) (X.toFlowSequence.atTime 0))
    (hcanonical : ∀ k, P.convergence.metrics.domain k =
      CanonicalMetricCompactness.canonicalSourceData P.maps k)
    (capture : MetricSourceCapture P.maps)
    (precompact : ∀ i, IsCompact (closure (P.maps.partialDiffeomorph i).source))
    (connected_domains : ∀ i, IsConnected (P.maps.partialDiffeomorph i).source)
    (nested : ∀ i, closure (P.maps.partialDiffeomorph i).source ⊆
      (P.maps.partialDiffeomorph (i + 1)).source)
    (orientation : TangentOrientationSection P.limit.M)
    (orientation_preserved : ∀ i y, y ∈ (P.maps.partialDiffeomorph i).source →
      ∃ hf : Function.Bijective (mfderiv I3 I3 (P.maps.partialDiffeomorph i) y),
        PreservesTangentOrientationAt orientation (X.orientation (P.subseq i))
          (P.maps.partialDiffeomorph i) y hf)
    (scalar_bound : ∃ C : ℝ, ∀ x, metricScalarAt P.limit.metric x ≤ C)
    (noncollapse : ∃ kappa' : ℝ, 0 < kappa' ∧ MetricNoncollapsed P.limit kappa' (Set.Ioc 0 1))
    (hconnected : ConnectedSpace P.limit.M) :
    Nonempty (TerminalLimit X) :=
  ⟨TerminalLimit.ofMetricCompactLimit hPhi P hcanonical capture precompact connected_domains nested
    orientation orientation_preserved scalar_bound noncollapse hconnected⟩

theorem terminal_limit_global_bound_of_frontier {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hkappa : 0 < kappa) (hsigma : 0 < sigma) (hPhi : AdmissiblePinchingFunction Phi)
    (hcompactness : ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X → TerminalDerivativeBounds X →
        ∃ P : MetricCompactLimit.{u, 0, 0} (I := I3) (X.toFlowSequence.atTime 0),
          (∀ k, P.convergence.metrics.domain k =
            CanonicalMetricCompactness.canonicalSourceData P.maps k) ∧
          ConnectedSpace P.limit.M ∧
          MetricSourceCapture P.maps ∧
          (∀ i, IsCompact (closure (P.maps.partialDiffeomorph i).source)) ∧
          (∀ i, IsConnected (P.maps.partialDiffeomorph i).source) ∧
          (∀ i, closure (P.maps.partialDiffeomorph i).source ⊆
            (P.maps.partialDiffeomorph (i + 1)).source) ∧
          (∃ o : TangentOrientationSection P.limit.M,
            ∀ i y, y ∈ (P.maps.partialDiffeomorph i).source →
              ∃ hf : Function.Bijective (mfderiv I3 I3 (P.maps.partialDiffeomorph i) y),
                PreservesTangentOrientationAt o (X.orientation (P.subseq i))
                  (P.maps.partialDiffeomorph i) y hf) ∧
          (∃ C : ℝ, ∀ x, metricScalarAt P.limit.metric x ≤ C) ∧
          (∃ kappa' : ℝ, 0 < kappa' ∧ MetricNoncollapsed P.limit kappa' (Set.Ioc 0 1))) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X → TerminalDerivativeBounds X → Nonempty (TerminalLimit X) := by
  let _ := hkappa
  let _ := hsigma
  obtain ⟨epsStar, hpos, h⟩ := hcompactness
  refine ⟨epsStar, hpos, fun eps heps hle X hb hd => ?_⟩
  obtain ⟨P, hcanonical, hconn, hcap, hpre, hcd, hnested, ⟨o, hor⟩, hsb, hnc⟩ :=
    h eps heps hle X hb hd
  exact terminal_limit_of_metric_compact_limit hPhi P hcanonical hcap hpre hcd hnested o hor
    hsb hnc hconn


end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
