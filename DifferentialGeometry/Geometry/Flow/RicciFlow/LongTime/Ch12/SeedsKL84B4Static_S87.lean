import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84B4Point_S87
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84TraceScalar_S74
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.SeedsKL84TopScalar_S87
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.RegularInterchange_S74
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.CutoffThreshold_CX2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch12.EnhancedProfileHypotheses

/-!
# CH12-S87 G2/G3 support: static transport pieces for the (b4) window

`rm_ball_bound_S87`: (s1)+(s2)+(b3) on the tower history: `R ≤ Mb` at `x` gives
`|Rm| ≤ C · 2 C2 Mb` on `B_v(x, (2 C2 Mb)^{-1/2})` (`v ≤ s.time`).
`window_event_S87`: a crossed event of a window `[a₂, u]` has its time in `(a₂, u]`.
-/

set_option autoImplicit false

noncomputable section

open Set Manifold DifferentialGeometry DifferentialGeometry.Topology
  DifferentialGeometry.PDE.RicciFlow.Surgery.Topology DifferentialGeometry.Geometry.Curvature
  DifferentialGeometry.Tensor0SBundle DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.PDE.RicciFlow
open scoped Manifold ContDiff ENNReal

namespace GC.LongTime.Ch12

universe u

variable {P : OrientedThreeStage.{u}} {g : P.Metric}

theorem rm_ball_bound_S87 {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ}
    (Hp : AnalyticSurgeryProfile F δ) {C : ℝ}
    (hCrm : ∀ (s : RegularSlice F.observation)
      (v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon), (v : ℝ) ≤ s.time →
      ∀ (x : ((sliceTowerHistory_CX2 s).stage ((sliceTowerHistory_CX2 s).activeStage v)).Carrier)
        (Mb : ℝ), 1 ≤ Mb →
      metricScalarAt ((sliceTowerHistory_CX2 s).stageMetric
        ((sliceTowerHistory_CX2 s).activeStage v) v) x ≤ Mb →
      Real.sqrt (normSq0S ((sliceTowerHistory_CX2 s).stageMetric
        ((sliceTowerHistory_CX2 s).activeStage v) v) x 4
        (metricRm04At ((sliceTowerHistory_CX2 s).stageMetric
          ((sliceTowerHistory_CX2 s).activeStage v) v) x)) ≤ C * Mb)
    (s : RegularSlice F.observation) (v : Icc (0 : ℝ) (sliceTowerHistory_CX2 s).horizon)
    (hvs : (v : ℝ) ≤ s.time) {Mb r : ℝ} (hMb : 1 ≤ Mb)
    (hNM : (Hp.parameters.neckRadius v ^ 2)⁻¹ ≤ Mb)
    (hr : 20 * r ≤ (Real.sqrt (2 * Hp.C2 * Mb))⁻¹)
    (x : ((sliceTowerHistory_CX2 s).stage ((sliceTowerHistory_CX2 s).activeStage v)).Carrier)
    (hx : metricScalarAt ((sliceTowerHistory_CX2 s).stageMetric
      ((sliceTowerHistory_CX2 s).activeStage v) v) x ≤ Mb) :
    ∀ q ∈ riemannianBallOf ((sliceTowerHistory_CX2 s).stageMetric
        ((sliceTowerHistory_CX2 s).activeStage v) v) x (20 * r),
      Real.sqrt (normSq0S ((sliceTowerHistory_CX2 s).stageMetric
        ((sliceTowerHistory_CX2 s).activeStage v) v) q 4
        (metricRm04At ((sliceTowerHistory_CX2 s).stageMetric
          ((sliceTowerHistory_CX2 s).activeStage v) v) q)) ≤ C * (2 * Hp.C2 * Mb) := by
  intro q hq
  have hq' := riemannianBallOf_mono _ _ hr hq
  have hlt := cn_scalar_spread_S63 _ Hp.C2_ge_one (canonical_prefix_S74 Hp s v hvs) x
    (by linarith) hNM hx q hq'
  exact hCrm s v hvs q (2 * Hp.C2 * Mb) (by nlinarith [Hp.C2_ge_one]) hlt.le

theorem window_event_S87 (H : ObservedHistory.{u}) {a₂ u : Icc (0 : ℝ) H.horizon}
    (i : Fin H.eventCount) (hf : H.activeStage a₂ ≤ i.castSucc) (hl : i.succ ≤ H.activeStage u) :
    (a₂ : ℝ) < H.time i.succ ∧ H.time i.succ ≤ (u : ℝ) := by
  refine ⟨?_, (H.time_strictMono.monotone hl).trans (H.activeStage_time_le u)⟩
  by_contra hn
  rw [not_lt] at hn
  have h1 : i.succ ≤ H.activeStage a₂ := H.le_activeStage a₂ _ hn
  exact absurd (hf.trans_lt (Fin.castSucc_lt_succ (i := i))) (not_lt.mpr h1)

end GC.LongTime.Ch12
