import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySurvivorFootprint
import DifferentialGeometry.Geometry.Flow.RicciFlow.Estimates.LocalPullDistanceComparison

set_option autoImplicit false
noncomputable section
open Set Manifold
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory

universe u
variable (H : ObservedHistory.{u}) (first : Fin (H.eventCount + 1))
  (i : Fin H.eventCount) (hle : first ≤ i.castSucc)

theorem isCompact_intrinsic_closedBall_backwardSurvivorFootprint
    (K : Set (H.event i).incoming.terminalRegularOpen)
    (htrace : ∀ x ∈ K, Nonempty (BackwardPointTrace H first i.castSucc hle x.val))
    (p : (H.event i).incoming.terminalRegularOpen) (hp : p ∈ interior K)
    {c : ℝ} (hcs : c ≤ H.time i.succ)
    (S : SolutionOn (I := ThreeModel)
      (M := H.backwardSurvivorFootprintInterior first i hle K)
      (RealTimeInterval.closed c (H.time i.succ) hcs))
    (hS : IsSolutionOn S)
    (hterminal : S.base.metric (H.time i.succ) = localPullMetric (H.event i).terminal.metric
      (H.backwardSurvivorFootprintMap first i hle K)
      (H.backwardSurvivorFootprintMap_isLocalDiffeomorph first i hle K))
    {C t : ℝ}
    (hRm : ∀ u ∈ Icc c (H.time i.succ),
      ∀ x : H.backwardSurvivorFootprintInterior first i hle K,
        normSq0S (S.base.metric u) x 4 (S.base.rm04 u x) ≤ C)
    (ht : t ∈ Icc c (H.time i.succ)) {r R : ℝ≥0}
    (hcompact : IsCompact {x | riemannianEDistOf (H.event i).terminal.metric p x ≤ R})
    (hball : {x | riemannianEDistOf (H.event i).terminal.metric p x ≤ R} ⊆ interior K)
    (hfit : ENNReal.ofReal (Real.exp (9 * Real.sqrt C * |t - H.time i.succ|)) *
      (r : ℝ≥0∞) ≤ R) :
    IsCompact {x : H.backwardSurvivorFootprintInterior first i hle K |
      riemannianEDistOf (S.base.metric t)
        (H.backwardSurvivorFootprintPoint first i hle K htrace p hp) x ≤ r} := by
  apply isCompact_intrinsic_closedBall_of_localPullMetric_terminal
    (H.event i).terminal.metric (H.backwardSurvivorFootprintMap first i hle K)
    (H.backwardSurvivorFootprintMap_isLocalDiffeomorph first i hle K)
    (H.backwardSurvivorFootprintMap_injective first i hle K) S hS
    Subset.rfl Subset.rfl hRm ht hterminal
  · simpa only [H.backwardSurvivorFootprintMap_point] using hcompact
  · simpa only [H.backwardSurvivorFootprintMap_point,
      H.range_backwardSurvivorFootprintMap first i hle K htrace] using hball
  · simpa [ThreeSpace, show (3 : ℝ) ^ 2 = 9 by norm_num] using hfit

theorem riemannianEDistOf_exp_bounds_backwardSurvivorFootprint
    (K : Set (H.event i).incoming.terminalRegularOpen)
    (htrace : ∀ x ∈ K, Nonempty (BackwardPointTrace H first i.castSucc hle x.val))
    (p : (H.event i).incoming.terminalRegularOpen) (hp : p ∈ interior K)
    {c : ℝ} (hcs : c ≤ H.time i.succ)
    (S : SolutionOn (I := ThreeModel)
      (M := H.backwardSurvivorFootprintInterior first i hle K)
      (RealTimeInterval.closed c (H.time i.succ) hcs))
    (hS : IsSolutionOn S)
    (hterminal : S.base.metric (H.time i.succ) = localPullMetric (H.event i).terminal.metric
      (H.backwardSurvivorFootprintMap first i hle K)
      (H.backwardSurvivorFootprintMap_isLocalDiffeomorph first i hle K))
    {C t : ℝ}
    (hRm : ∀ u ∈ Icc c (H.time i.succ),
      ∀ x : H.backwardSurvivorFootprintInterior first i hle K,
        normSq0S (S.base.metric u) x 4 (S.base.rm04 u x) ≤ C)
    (ht : t ∈ Icc c (H.time i.succ)) {R : ℝ≥0} (hR : 0 < R)
    (hball : {x | riemannianEDistOf (H.event i).terminal.metric p x < R} ⊆ interior K)
    (x : H.backwardSurvivorFootprintInterior first i hle K)
    (hx : riemannianEDistOf (H.event i).terminal.metric p
      (H.backwardSurvivorFootprintMap first i hle K x) < (R / 3 : ℝ≥0)) :
    ENNReal.ofReal (Real.exp (-(9 * Real.sqrt C * |t - H.time i.succ|))) *
        riemannianEDistOf (H.event i).terminal.metric p
          (H.backwardSurvivorFootprintMap first i hle K x) ≤
      riemannianEDistOf (S.base.metric t)
        (H.backwardSurvivorFootprintPoint first i hle K htrace p hp) x ∧
    riemannianEDistOf (S.base.metric t)
        (H.backwardSurvivorFootprintPoint first i hle K htrace p hp) x ≤
      ENNReal.ofReal (Real.exp (9 * Real.sqrt C * |t - H.time i.succ|)) *
        riemannianEDistOf (H.event i).terminal.metric p
          (H.backwardSurvivorFootprintMap first i hle K x) := by
  have hb : {x | riemannianEDistOf (H.event i).terminal.metric
      (H.backwardSurvivorFootprintMap first i hle K
        (H.backwardSurvivorFootprintPoint first i hle K htrace p hp)) x < R} ⊆
        range (H.backwardSurvivorFootprintMap first i hle K) := by
    simpa only [H.backwardSurvivorFootprintMap_point,
      H.range_backwardSurvivorFootprintMap first i hle K htrace] using hball
  have hd := riemannianEDistOf_exp_bounds_on_localPullMetric_terminal_ball
    (H.event i).terminal.metric (H.backwardSurvivorFootprintMap first i hle K)
    (H.backwardSurvivorFootprintMap_isLocalDiffeomorph first i hle K)
    (H.backwardSurvivorFootprintMap_injective first i hle K) S hS
    Subset.rfl Subset.rfl hRm ht hterminal
    (H.backwardSurvivorFootprintPoint first i hle K htrace p hp) hR hb x
    (by simpa only [H.backwardSurvivorFootprintMap_point] using hx)
  simpa [H.backwardSurvivorFootprintMap_point, ThreeSpace,
    show (3 : ℝ) ^ 2 = 9 by norm_num] using hd

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.ObservedHistory
