import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.BarrierFromWindows_S95
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.HAbs_S105

/-!
# CH12-S113, group 2a: the located event barrier at ONE event, from `¬ CAP` of the centre

`barrier_event_S113` is `located_barrier_of_noCAP_S95` + `hAbs_S105` specialised to a single event `j` and a single
centre `c` (the trace point of the centre of the test ball at that event), with the birth-shift clause `hshift` of
`hAbs_S105` weakened to the RELEVANT cap window points only (`F-S106-3`: only a retained boundary `b` whose window
carries a low-scalar point of the `20 r`-ball is used; `cap_of_lowscalar_S105` takes `hshift` per `b`).  The negated
cap predicate `hnoCap` is the S64 CAP clause of event `j` with the trace `B` fixed (`c = B.point j.succ`).
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
  DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Riemannian
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

theorem barrier_event_S113 {H : ObservedHistory.{u}} {pp : CutoffParameters} {j : Fin H.eventCount}
    (R : GeometricCutoffRecord H j pp) {Dc r K τ c₀ θ age : ℝ} {c : (H.stage j.succ).Carrier}
    (hFront : ∀ y ∈ frontier (range (H.event j).oldOutput),
      ∃ (b : (H.event j).RetainedBoundaryIndex) (x : standardCapWindow pp.modelRadius),
        (R.static b).window x = y ∧ ‖x.val‖ < Dc + 1)
    (hr : 0 < r) (hτ : 0 < τ) (hc₀ : 0 < c₀) (hτK : 9 * K * τ ≤ c₀ * θ)
    (hD : Dc + 2 ≤ pp.modelRadius) (hacc : pp.modelAccuracy ≤ 3 / 4)
    (hscale : ∀ (b : (H.event j).RetainedBoundaryIndex) (x : standardCapWindow pp.modelRadius),
      ‖x.val‖ < Dc + 1 → c₀ * (R.static b).neck.scale ≤
        metricScalarAt (H.event j).outputMetric ((R.static b).window x))
    (hshift : ∀ (b : (H.event j).RetainedBoundaryIndex) (x : standardCapWindow pp.modelRadius),
      ‖x.val‖ < Dc + 1 →
      (R.static b).window x ∈ riemannianBallOf (H.event j).outputMetric c (20 * r) →
      metricScalarAt (H.event j).outputMetric ((R.static b).window x) ≤ 9 * K / r ^ 2 →
      40 * r * Real.sqrt (R.static b).neck.scale ≤ 1)
    (hage : age < τ * r ^ 2)
    (hnoCap : ¬ ∃ (b : (H.event j).RetainedBoundaryIndex) (x : standardCapWindow pp.modelRadius),
      ‖x.val‖ < Dc + 2 ∧ (R.static b).window x = c ∧ age ≤ θ * ((R.static b).neck.scale)⁻¹)
    {U : Set (H.stage j.succ).Carrier}
    (hUb : U ⊆ riemannianBallOf (H.event j).outputMetric c (20 * r)) (hU : IsPreconnected U)
    (hs : ∀ y ∈ U, metricScalarAt (H.event j).outputMetric y ≤ 9 * K / r ^ 2)
    {x : (H.event j).incoming.terminalRegularOpen} {y : (H.stage j.succ).Carrier}
    (hy : y ∈ U) (hcross : (H.event j).RegularCrossing x.val y) :
    U ⊆ interior (range (H.event j).oldOutput) := by
  refine barrier_of_frontier_windows_S95 R hFront hU ?_ hy hcross
  intro b w hw hmem
  obtain ⟨w', hw', he, hag⟩ := cap_of_lowscalar_S105 (R.static b) hacc hr hτ hc₀ hD (hscale b)
    (hshift b w hw (hUb hmem) (hs _ hmem)) hage hτK hUb hs hw hmem
  exact hnoCap ⟨b, w', hw', he, hag⟩

end GC.LongTime.Ch12
