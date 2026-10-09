import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceScalarControl.TimeLocal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.CanonicalTimeControlPointSelection

set_option autoImplicit false

/-!
# CX-SPINE G8：已有 trace 上尚未出界的 Good 后缀给跨手术标量界

复用 TimeLocal:99 的实际整史截断倒数控制。对于 s<u≤t，把同一 trace 限制到 [u,t]；
所有低于 t 的测试点都严格晚于 s，终端 t 的高曲率导数前提由 R(t)≤M 排除。
总预算始终为 Ctime*M*(t-s)，不随手术次数反复放大 M。此处不生产 trace 存在性。
-/

noncomputable section

open Set DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace

universe u

/-- 对已有 trace，开后缀上的完整 Good 足以给全部严格后缀点的统一标量上界。 -/
theorem scalar_le_two_mul_of_good_suffix_CXSP
    {H : ObservedHistory.{u}} {a t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t)
    {y : (H.stageAt t).Carrier}
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
      (H.activeStage_mono hat) y)
    {ε C1 C2 q M s : ℝ} {Ctime : ℝ≥0}
    (hM : 0 < M) (hqM : q ≤ M)
    (hgood : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      s < (v : ℝ) → (v : ℝ) < t →
      q ≤ metricScalarAt (H.stageMetric (H.activeStage v) v)
        (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) →
      H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime v
        (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)))
    (hscalar : metricScalarAt (H.stageMetric (H.activeStage t) t) y ≤ M)
    (htime : Ctime * M * ((t : ℝ) - s) ≤ 1 / 2)
    (u : Icc (0 : ℝ) H.horizon) (hau : a ≤ u) (hsu : s < (u : ℝ)) (hut : u ≤ t) :
    metricScalarAt (H.stageMetric (H.activeStage u) u)
      (A.point (H.activeStage u) (H.activeStage_mono hau) (H.activeStage_mono hut)) ≤
      2 * M := by
  let B := A.restrictFirst (H.activeStage_mono hau) (H.activeStage_mono hut)
  have htimeU : Ctime * M * ((t : ℝ) - u) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left (sub_le_sub_left hsu.le t)
      (mul_nonneg Ctime.coe_nonneg hM.le)).trans htime
  have hcontrol := B.scalar_le_two_mul_of_time_local_derivative_control hut hM
    (fun v huv hvt hage htop hR => by
      rcases lt_or_eq_of_le hvt with hvlt | rfl
      · exact (hgood v (hau.trans huv) hvt
          (hsu.trans_le (show (u : ℝ) ≤ v from huv)) hvlt (hqM.trans_lt hR).le).2 hage htop
      · have hRt : M < metricScalarAt (H.stageMetric (H.activeStage v) v) y := by
          simpa only [B.endpoint_eq] using hR
        exact False.elim (not_lt_of_ge hscalar hRt)) hscalar htimeU
  exact hcontrol u le_rfl hut

/-- 窗口起点是 stage 出生时刻时，开后缀 Good 同样控制出生点本身。
该点的导数请求由正 stage-age guard 排除，未向过去假设额外 Good。 -/
theorem scalar_le_two_mul_at_birth_of_good_suffix_CXSP
    {H : ObservedHistory.{u}} {a t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t)
    {y : (H.stageAt t).Carrier}
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
      (H.activeStage_mono hat) y)
    {ε C1 C2 q M : ℝ} {Ctime : ℝ≥0}
    (hM : 0 < M) (hqM : q ≤ M) (hbirth : H.time (H.activeStage a) = (a : ℝ))
    (hgood : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      (a : ℝ) < v → (v : ℝ) < t →
      q ≤ metricScalarAt (H.stageMetric (H.activeStage v) v)
        (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) →
      H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime v
        (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)))
    (hscalar : metricScalarAt (H.stageMetric (H.activeStage t) t) y ≤ M)
    (htime : Ctime * M * ((t : ℝ) - a) ≤ 1 / 2) :
    metricScalarAt (H.stageMetric (H.activeStage a) a)
      (A.point (H.activeStage a) le_rfl (H.activeStage_mono hat)) ≤ 2 * M := by
  have hcontrol := A.scalar_le_two_mul_of_time_local_derivative_control hat hM
    (fun v hav hvt hage htop hR => by
      rcases lt_or_eq_of_le hav with havlt | heq
      · rcases lt_or_eq_of_le hvt with hvtlt | heq
        · exact (hgood v hav hvt havlt hvtlt (hqM.trans_lt hR).le).2 hage htop
        · subst v
          have hRt : M < metricScalarAt (H.stageMetric (H.activeStage t) t) y := by
            simpa only [A.endpoint_eq] using hR
          exact False.elim (not_lt_of_ge hscalar hRt)
      · subst v
        exact False.elim (not_lt_of_ge hbirth.ge hage)) hscalar htime
  exact hcontrol a le_rfl hat

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace
