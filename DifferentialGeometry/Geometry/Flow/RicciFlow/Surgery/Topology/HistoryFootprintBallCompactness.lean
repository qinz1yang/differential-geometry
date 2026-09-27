import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorFootprint
import DifferentialGeometry.Geometry.Metric.Distance.LocalPullCompactness

noncomputable section

open Set Manifold
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u

variable (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1))
  (i : Fin H.eventCount) (hle : first ≤ i.castSucc)

theorem exists_footprint_point_isCompact_terminal_closedBall
    (x : (H.event i).incoming.terminalRegularOpen) {R : ℝ} (hR : 0 < R)
    (hcompact : IsCompact (riemannianClosedBallOf (H.event i).terminal.metric x R))
    (hrange : range (H.backwardSurvivorFootprintMap first i hle
        (riemannianClosedBallOf (H.event i).terminal.metric x R)) =
      interior (riemannianClosedBallOf (H.event i).terminal.metric x R))
    (g : SmoothRiemannianMetric ThreeModel
      (H.backwardSurvivorFootprintInterior first i hle
        (riemannianClosedBallOf (H.event i).terminal.metric x R)))
    (hg : g = localPullMetric (H.event i).terminal.metric
      (H.backwardSurvivorFootprintMap first i hle
        (riemannianClosedBallOf (H.event i).terminal.metric x R))
      (H.backwardSurvivorFootprintMap_isLocalDiffeomorph first i hle
        (riemannianClosedBallOf (H.event i).terminal.metric x R))) :
    ∃ p : H.backwardSurvivorFootprintInterior first i hle
        (riemannianClosedBallOf (H.event i).terminal.metric x R),
      H.backwardSurvivorFootprintMap first i hle
        (riemannianClosedBallOf (H.event i).terminal.metric x R) p = x ∧
      ∀ r : ℝ, r < R → IsCompact (riemannianClosedBallOf g p r) := by
  have hopen : IsOpen (riemannianBallOf (H.event i).terminal.metric x R) :=
    isOpen_lt (by
      unfold riemannianEDistOf
      exact Geometry.Riemannian.continuous_riemannianEDist _ x) continuous_const
  have hball : riemannianBallOf (H.event i).terminal.metric x R ⊆
      range (H.backwardSurvivorFootprintMap first i hle
        (riemannianClosedBallOf (H.event i).terminal.metric x R)) := by
    rw [hrange]
    apply interior_maximal ?_ hopen
    intro y hy
    exact le_of_lt (show riemannianEDistOf (H.event i).terminal.metric x y <
      ENNReal.ofReal R from hy)
  obtain ⟨p, hp, hc⟩ := Geometry.Metric.exists_lift_isCompact_riemannianClosedBallOf_localPullMetric
    (H.event i).terminal.metric
    (H.backwardSurvivorFootprintMap first i hle
      (riemannianClosedBallOf (H.event i).terminal.metric x R))
    (H.backwardSurvivorFootprintMap_isLocalDiffeomorph first i hle
      (riemannianClosedBallOf (H.event i).terminal.metric x R))
    (H.backwardSurvivorFootprintMap_injective first i hle
      (riemannianClosedBallOf (H.event i).terminal.metric x R)) x hR hcompact hball
  exact ⟨p, hp, fun r hr => hg.symm ▸ hc r hr⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
