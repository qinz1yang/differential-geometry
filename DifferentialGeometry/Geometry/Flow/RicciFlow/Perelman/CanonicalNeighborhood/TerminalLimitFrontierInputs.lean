import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.AncientExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.TerminalBackwardExtension
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.CanonicalNeighborhood.SlabFlowBootstrap

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.Geometry.Operator
open scoped Manifold ContDiff ENNReal

universe u

attribute [local instance] PointedFlowData.topology PointedFlowData.charted
  PointedFlowData.smooth PointedFlowData.t2 PointedFlowData.sigmaCompact
  PointedFlowData.t2TangentBundle PointedRiemannianManifold.topology
  PointedRiemannianManifold.charted PointedRiemannianManifold.smooth
  PointedRiemannianManifold.t2 PointedRiemannianManifold.sigmaCompact
  PointedRiemannianManifold.t2TangentBundle

def TerminalLimitCompactnessFrontier (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
      BoundedAtDistance X → TerminalDerivativeBounds X →
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
          MetricNoncollapsed P.limit kappa Set.univ

def TerminalLimitScalarBoundFrontier (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
      BoundedAtDistance X → TerminalDerivativeBounds X →
        ∀ P : MetricCompactLimit.{u, 0, 0} (I := I3) (X.toFlowSequence.atTime 0),
          (∀ k, P.convergence.metrics.domain k =
            CanonicalMetricCompactness.canonicalSourceData P.maps k) →
          (hconn : ConnectedSpace P.limit.M) → MetricSourceCapture P.maps →
          (∀ i, IsCompact (closure (P.maps.partialDiffeomorph i).source)) →
          (∀ i, IsConnected (P.maps.partialDiffeomorph i).source) →
          (∀ i, closure (P.maps.partialDiffeomorph i).source ⊆
            (P.maps.partialDiffeomorph (i + 1)).source) →
          (∃ o : TangentOrientationSection P.limit.M,
            ∀ i y, y ∈ (P.maps.partialDiffeomorph i).source →
              ∃ hf : Function.Bijective (mfderiv I3 I3 (P.maps.partialDiffeomorph i) y),
                PreservesTangentOrientationAt o (X.orientation (P.subseq i))
                  (P.maps.partialDiffeomorph i) y hf) →
          MetricNoncollapsed P.limit kappa Set.univ →
            ∃ C : ℝ, ∀ x, metricScalarAt P.limit.metric x ≤ C

theorem terminal_limit_global_bound_of_frontiers {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (hPhi : AdmissiblePinchingFunction Phi)
    (hcompact : TerminalLimitCompactnessFrontier.{u} kappa sigma Phi)
    (hbounded : TerminalLimitScalarBoundFrontier.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X → TerminalDerivativeBounds X → Nonempty (TerminalLimit X) := by
  obtain ⟨e₁, he₁, h₁⟩ := hcompact
  obtain ⟨e₂, he₂, h₂⟩ := hbounded
  refine ⟨min e₁ e₂, lt_min he₁ he₂, fun eps heps hle X hb hd => ?_⟩
  obtain ⟨P, hcanon, hconn, hcap, hpre, hcd, hnested, hor, hnc⟩ :=
    h₁ eps heps (hle.trans (min_le_left e₁ e₂)) X hb hd
  obtain ⟨o, hor'⟩ := hor
  have hsb := h₂ eps heps (hle.trans (min_le_right e₁ e₂)) X hb hd P hcanon hconn hcap hpre
    hcd hnested ⟨o, hor'⟩ hnc
  exact terminal_limit_of_metric_compact_limit hPhi P hcanon hcap hpre hcd hnested o hor' hsb hnc
    hconn

theorem terminal_limit_compactness_frontier_of_terminal_limit_exists {kappa sigma : ℝ}
    {Phi : ℝ → ℝ}
    (h : ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ X : NormalizedSequence.{u} eps kappa sigma Phi,
        BoundedAtDistance X → TerminalDerivativeBounds X → Nonempty (TerminalLimit X)) :
    TerminalLimitCompactnessFrontier.{u} kappa sigma Phi := by
  obtain ⟨e, he, hmain⟩ := h
  refine ⟨e, he, fun eps heps hle X hb hd => ?_⟩
  obtain ⟨L⟩ := hmain eps heps hle X hb hd
  let P : MetricCompactLimit.{u, 0, 0} (I := I3) (X.toFlowSequence.atTime 0) :=
    { subseq := L.subseq
      strictMono := L.strictMono
      limit := L.space
      limit_complete := L.complete
      maps := L.maps
      convergence := { metrics := L.converges } }
  exact ⟨P, L.canonical_domains, L.connected, L.capture, L.precompact, L.connected_domains,
    L.nested, ⟨L.orientation, L.orientation_preserved⟩, L.noncollapse⟩

def SlabLimitSpatialJets {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) (delta : ℝ) (hd : 0 < delta) : Prop :=
  ∀ g : ℝ → SmoothRiemannianMetric I3 L.space.M, IsSlabLimit L delta hd g →
    ∀ (p : L.space.M) (r : ℕ) (i j : Fin (Module.finrank ℝ ThreeSpace)),
      ContinuousOn (fun q : ℝ × ThreeSpace => iteratedFDeriv ℝ r
        (chartGramOnE (I := I3) (g q.1) p i j) q.2)
        (Set.Icc (-delta) 0 ×ˢ (extChartAt I3 p).target)

theorem slabLimit_isSolutionOn_of_spatialJets {X : FlowSequence.{u}} {depthBound : ℝ}
    (L : StaticTerminalLimit X depthBound) {delta : ℝ} {hd : 0 < delta}
    (hle : delta ≤ depthBound) (hjets : SlabLimitSpatialJets L delta hd) :
    SlabLimitIsFlow L delta hd :=
  fun g hlim => IsSlabLimit.isSolutionOn_of_spatialJets L hle hlim (hjets g hlim)

def TerminalSlabJetInputs (kappa sigma : ℝ) (Phi : ℝ → ℝ) : Prop :=
  ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
    ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X),
      ∃ (depthBound delta : ℝ) (hdepth : depthBound ≤ 2 * modelDepth eps)
        (hb : TerminalSlabBounds L depthBound) (hd : 0 < delta),
        0 < depthBound ∧ delta ≤ depthBound ∧
          SlabLimitExists (L.toStatic hdepth hb) delta ∧
          SlabLimitSpatialJets (L.toStatic hdepth hb) delta hd ∧
          SlabLimitSliceGeometry (L.toStatic hdepth hb) delta hd ∧
          SlabLimitCurvatureBound (L.toStatic hdepth hb) delta hd

theorem first_backward_slab_of_terminal_slab_jetInputs {kappa sigma : ℝ} {Phi : ℝ → ℝ}
    (h : TerminalSlabJetInputs.{u} kappa sigma Phi) :
    ∃ epsStar : ℝ, 0 < epsStar ∧ ∀ eps : ℝ, 0 < eps → eps ≤ epsStar →
      ∀ (X : NormalizedSequence.{u} eps kappa sigma Phi) (L : TerminalLimit X),
        ∃ delta : ℝ, ∃ hd : 0 < delta,
          Nonempty (BackwardExtension L (RealTimeInterval.closed (-delta) 0 (by linarith))) := by
  obtain ⟨e, he, hI⟩ := h
  refine ⟨e, he, fun eps heps hle X L => ?_⟩
  obtain ⟨depthBound, delta, hdepth, hb, hd, hdpos, hdle, hexists, hjets, hgeom, hcurv⟩ :=
    hI eps heps hle X L
  have hflow : SlabLimitIsFlow (L.toStatic hdepth hb) delta hd :=
    slabLimit_isSolutionOn_of_spatialJets _ hdle hjets
  exact first_backward_slab_of_terminal L hdepth hb
    ⟨delta, hd, hdle, hexists, hflow, hgeom, hcurv⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
