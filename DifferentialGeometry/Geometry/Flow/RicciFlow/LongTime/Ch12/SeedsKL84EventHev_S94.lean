import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SubTrace_S87
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84EventSeed_S94

/-!
# CH12-S94 G1: `hev_S94`, the event-time seed in the shape of the `hev` binder of `hsub86N_S87`
(tower histories, `Hp.records n`).
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
  DifferentialGeometry.Geometry.Riemannian.VolumeComparison DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow
open scoped NNReal Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

theorem hev_S94 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} (Hp : AnalyticSurgeryProfile F δ) :
    ∀ n, ∀ {a t : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon} {τ r K Λ : ℝ},
      0 < τ → 0 < r → 0 < K → 1 ≤ Λ → 2 * (9 * K) < Λ ^ 2 → Real.exp (9 * K * τ) < 2 →
      a.val = t.val - τ * r ^ 2 → ∀ (hat : a ≤ t), (F.tower.history n).toHistory.time ((F.tower.history n).toHistory.activeStage t) = t.val → 0 < t.val →
      ∀ {p y : ((F.tower.history n).toHistory.stageAt t).Carrier},
      y ∈ riemannianBallOf ((F.tower.history n).toHistory.stageMetric ((F.tower.history n).toHistory.activeStage t) t) p r →
      ∀ (Y : BackwardPointTrace (F.tower.history n).toHistory ((F.tower.history n).toHistory.activeStage a) ((F.tower.history n).toHistory.activeStage t) ((F.tower.history n).toHistory.activeStage_mono hat) y),
      (∀ (v : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon) (hav : a ≤ v) (hvt : v ≤ t),
        ∀ q ∈ riemannianBallOf ((F.tower.history n).toHistory.stageMetric ((F.tower.history n).toHistory.activeStage v) v)
          (Y.point ((F.tower.history n).toHistory.activeStage v) ((F.tower.history n).toHistory.activeStage_mono hav) ((F.tower.history n).toHistory.activeStage_mono hvt)) (20 * r),
        Real.sqrt (normSq0S ((F.tower.history n).toHistory.stageMetric ((F.tower.history n).toHistory.activeStage v) v) q 4
          (metricRm04At ((F.tower.history n).toHistory.stageMetric ((F.tower.history n).toHistory.activeStage v) v) q)) ≤ K / r ^ 2) →
      (∀ (i : Fin (F.tower.history n).toHistory.eventCount), (F.tower.history n).toHistory.activeStage a ≤ i.castSucc → i.succ ≤ (F.tower.history n).toHistory.activeStage t →
        ∀ j, (Hp.records n i).delta j ≤ 1 / 8646) →
      (∀ (i : Fin (F.tower.history n).toHistory.eventCount), (F.tower.history n).toHistory.activeStage a ≤ i.castSucc → i.succ ≤ (F.tower.history n).toHistory.activeStage t →
        ∀ h, Λ * (Hp.records n i).nominalRadius h ≤ r) →
      (F.tower.history n).toHistory.isTracedRegion t p (2 * r) (τ * r ^ 2) (K / r ^ 2) :=
  fun n => record_seed_tracedRegion_event_S94 (F.tower.history n).toHistory Hp.parameters (Hp.records n)

end GC.LongTime.Ch12
