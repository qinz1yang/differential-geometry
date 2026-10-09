import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.TracedRegion
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CrossingRoom
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistorySlices
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.EndpointCurvatureC11G

set_option autoImplicit false

/-!
# CX-SPINE：原 history 的 scalar/HI 界支付实际 trace 的完整 Rm 控制

第一叶把 active-stage 闭窗界搬到每次实际 crossing
的 incoming terminal face；第二叶用同一 history 的 Hamilton--Ivey 数据与 trace scalar
界支付第一叶。不索取 Good、时间导数、regular-age 或 ratio 上界。
birth/horizon 保留。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace

universe u

variable {H : ObservedHistory.{u}} {a t : Icc (0 : ℝ) H.horizon} {hat : a ≤ t}
  {x : (H.stageAt t).Carrier}

/-- actual crossing 的 terminal Rm 与 post-birth Rm 相等，闭窗 active 界已足够。 -/
theorem isRmBoundedBy_of_active_time_CXSP
    (B : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
      (H.activeStage_mono hat) x) {K : ℝ}
    (hbound : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      normSq0S (H.stageMetric (H.activeStage v) v)
        (B.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) 4
        (metricRm04At (H.stageMetric (H.activeStage v) v)
          (B.point (H.activeStage v) (H.activeStage_mono hav)
            (H.activeStage_mono hvt))) ≤ K ^ 2) :
    B.isRmBoundedBy (hat := hat) K := by
  have hstage (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t)
      (j : Fin (H.eventCount + 1)) (hj : H.activeStage v = j)
      (hf : H.activeStage a ≤ j) (hl : j ≤ H.activeStage t) :
      normSq0S (H.stageMetric j v) (B.point j hf hl) 4
        (metricRm04At (H.stageMetric j v) (B.point j hf hl)) ≤ K ^ 2 := by
    subst j
    exact hbound v hav hvt
  refine ⟨hbound, ?_⟩
  intro i hf hl
  have hav : a ≤ H.stageTime i.succ := by
    change (a : ℝ) ≤ H.time i.succ
    by_contra hn
    have hj : i.succ ≤ H.activeStage a :=
      H.le_activeStage a i.succ (le_of_not_ge hn)
    exact (not_le_of_gt i.castSucc_lt_succ) (hj.trans hf)
  have hvt : H.stageTime i.succ ≤ t := by
    change H.time i.succ ≤ (t : ℝ)
    exact (H.time_strictMono.monotone hl).trans (H.activeStage_time_le t)
  have hpost := hstage (H.stageTime i.succ) hav hvt i.succ
    (H.activeStage_stageTime i.succ) (hf.trans i.castSucc_lt_succ.le) hl
  change normSq0S (H.stageMetric i.succ (H.time i.succ))
    (B.point i.succ (hf.trans i.castSucc_lt_succ.le) hl) 4
    (metricRm04At (H.stageMetric i.succ (H.time i.succ))
      (B.point i.succ (hf.trans i.castSucc_lt_succ.le) hl)) ≤ K ^ 2 at hpost
  rw [H.stageMetric_initial] at hpost
  let z : (H.event i).incoming.terminalRegularOpen :=
    ⟨B.point i.castSucc hf (i.castSucc_lt_succ.le.trans hl),
      (B.crossing i hf hl).mem_terminalRegularRegion (H.event i)⟩
  change normSq0S (H.event i).terminal.metric z 4
    (metricRm04At (H.event i).terminal.metric z) ≤ K ^ 2
  have hcross := MetricCutCapEvent.RegularCrossing.rmNormSq_eq
    (H.event i) (p := z) (B.crossing i hf hl)
  rw [hcross, H.event_output i]
  exact hpost

/-- 同一原 history 的 HI 与 trace scalar 界给完整 Rm bound，含 terminal faces。 -/
theorem isRmBoundedBy_of_scalar_and_HI_CXSP
    (B : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
      (H.activeStage_mono hat) x)
    {a₀ Q c : ℝ} (ha₀ : 0 ≤ a₀) (hQ : 0 < Q) (hc : 0 ≤ c)
    (hQa : 1 ≤ Q * (a : ℝ))
    (hHI : ∀ (v : Icc (0 : ℝ) H.horizon) (z : (H.stageAt v).Carrier),
      InFixedHamiltonIveyRegion (H.stageMetric (H.activeStage v) v) (a₀ + v) z)
    (hscalar : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      metricScalarAt (H.stageMetric (H.activeStage v) v)
        (B.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) ≤
          c * Q) :
    B.isRmBoundedBy (hat := hat)
      (2 * Real.sqrt 3 * (c / 2 + max c (2 * Real.exp 4)) * Q) := by
  apply B.isRmBoundedBy_of_active_time_CXSP
  intro v hav hvt
  have hQv : 1 ≤ Q * (v : ℝ) :=
    hQa.trans (mul_le_mul_of_nonneg_left (show (a : ℝ) ≤ v from hav) hQ.le)
  have hv : 0 < (v : ℝ) := by
    by_contra hn
    have hnprod := mul_nonpos_of_nonneg_of_nonpos hQ.le (le_of_not_gt hn)
    linarith
  have hb := ObservedHistory.sqrt_rmNormSq_le_of_HI_scalar_C11G
    (H.stageMetric (H.activeStage v) v)
    (B.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))
    ha₀ hv hQ hQv hc (hHI v _) (hscalar v hav hvt)
  exact (Real.sqrt_le_iff.mp hb).2

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace

end
