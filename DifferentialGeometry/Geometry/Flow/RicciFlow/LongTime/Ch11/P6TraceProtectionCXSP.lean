import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TraceGoodSuffixCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.EndpointProtectionC11G

set_option autoImplicit false

/-!
# CX-SPINE G19：Good 后缀与实际 cap scale 支付 trace 端点保护

将原 trace 限制到每个实际 stage birth，使用同一终端标量与缩短的时间预算。
包含候选起点和终端 birth；不用 incoming metric 代替 postmetric。
绝对 cap accuracy 先于 history 选择；full Good、trace 和 record scale 仍须实际生产。
-/

noncomputable section

open Set DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace

universe u

private theorem scalar_eq_stage_CXSP
    {H : ObservedHistory.{u}} {a t : Icc (0 : ℝ) H.horizon} {hat : a ≤ t}
    {p : (H.stageAt t).Carrier}
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
    (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t)
    (j : Fin (H.eventCount + 1)) (hf : H.activeStage a ≤ j) (hl : j ≤ H.activeStage t)
    (hact : H.activeStage v = j) :
    metricScalarAt (H.stageMetric (H.activeStage v) v)
        (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) =
      metricScalarAt (H.stageMetric j v) (A.point j hf hl) := by
  subst j
  rfl

/-- 同一实际 trace 的每个后缀 birth 标量界；允许 birth 等于候选时刻或终端。 -/
theorem scalar_at_stage_time_le_two_mul_CXSP
    {H : ObservedHistory.{u}} {a t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t)
    {p : (H.stageAt t).Carrier}
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) p)
    {ε C1 C2 q M s : ℝ} {Ctime : ℝ≥0}
    (hM : 0 < M) (hqM : q ≤ M)
    (hgood : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      s < (v : ℝ) → (v : ℝ) < t →
      q ≤ metricScalarAt (H.stageMetric (H.activeStage v) v)
        (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) →
      H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime v
        (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)))
    (hscalar : metricScalarAt (H.stageMetric (H.activeStage t) t) p ≤ M)
    (htime : Ctime * M * ((t : ℝ) - s) ≤ 1 / 2)
    (j : Fin (H.eventCount + 1)) (hf : H.activeStage a ≤ j) (hl : j ≤ H.activeStage t)
    (haj : (a : ℝ) ≤ H.time j) (hsj : s ≤ H.time j) :
    metricScalarAt (H.stageMetric j (H.time j)) (A.point j hf hl) ≤ 2 * M := by
  let u := H.stageTime j
  have hau : a ≤ u := haj
  have hut : u ≤ t :=
    (H.time_strictMono.monotone hl).trans (H.activeStage_time_le t)
  let B := A.restrictFirst (H.activeStage_mono hau) (H.activeStage_mono hut)
  have hbirth : H.time (H.activeStage u) = (u : ℝ) := by
    change H.time (H.activeStage (H.stageTime j)) = H.time j
    rw [H.activeStage_stageTime]
  have htimeU : Ctime * M * ((t : ℝ) - u) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left (sub_le_sub_left hsj t)
      (mul_nonneg Ctime.coe_nonneg hM.le)).trans htime
  have hbound := B.scalar_le_two_mul_at_birth_of_good_suffix_CXSP hut hM hqM hbirth
    (fun v huv hvt huvlt hvtlt hR =>
      hgood v (hau.trans huv) hvt (hsj.trans_lt huvlt) hvtlt hR) hscalar htimeU
  dsimp only [B, restrictFirst] at hbound
  rw [scalar_eq_stage_CXSP (hat := hat) A u hau hut j hf hl
    (H.activeStage_stageTime j)] at hbound
  exact hbound

/-- 绝对 accuracy 下，Good 后缀和同一 record 的 scale gap 生产 postpoint 保护。 -/
theorem exists_trace_protection_of_good_suffix_CXSP :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ {H : ObservedHistory.{u}} {a t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t)
        {p : (H.stageAt t).Carrier}
        (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t)
          (H.activeStage_mono hat) p)
        {params : CutoffParameters}
        (records : ∀ e : Fin H.eventCount, GeometricCutoffRecord H e params),
        params.modelAccuracy ≤ ε₀ → 2 ≤ params.modelOrder →
        (∀ e b, ((records e).static b).hasCanonicalWindow) →
        StandardCap.transitionEnd + 10 < params.modelRadius →
        ∀ {ε C1 C2 q M s : ℝ} {Ctime : ℝ≥0}, 0 < M → q ≤ M →
        (∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
          s < (v : ℝ) → (v : ℝ) < t →
          q ≤ metricScalarAt (H.stageMetric (H.activeStage v) v)
            (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) →
          H.HasSpatialCanonicalTimeControl ε C1 C2 Ctime v
            (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt))) →
        metricScalarAt (H.stageMetric (H.activeStage t) t) p ≤ M →
        Ctime * M * ((t : ℝ) - s) ≤ 1 / 2 →
        ∀ (e : Fin H.eventCount) (hf : H.activeStage a ≤ e.castSucc)
          (hl : e.succ ≤ H.activeStage t), s ≤ H.time e.succ →
          ∀ b, 4 * M < ((records e).static b).neck.scale →
          A.point e.succ (hf.trans e.castSucc_lt_succ.le) hl ∉
            ((records e).static b).window ''
              {z : standardCapWindow params.modelRadius |
                ‖z.val‖ ≤ StandardCap.transitionEnd + 10} := by
  obtain ⟨ε₀, hε₀, hlow⟩ := exists_capWindow_scalar_lower_C11G.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro H a t hat p A params records hacc hm hcan hD ε C1 C2 q M s Ctime
    hM hqM hgood hscalar htime e hf hl hse b hscale
  have hae : (a : ℝ) < H.time e.succ := by
    by_contra h
    have he := H.le_activeStage a e.succ (le_of_not_gt h)
    exact (not_le_of_gt e.castSucc_lt_succ) (he.trans hf)
  have hR := A.scalar_at_stage_time_le_two_mul_CXSP hat hM hqM hgood hscalar htime
    e.succ (hf.trans e.castSucc_lt_succ.le) hl hae.le hse
  rw [H.stageMetric_succ_time_C11G] at hR
  rintro ⟨z, hz, hzEq⟩
  have hRlow := hlow (H.event e) hacc hm ((records e).static b) (hcan e b) z
    (hz.trans_lt hD)
  rw [hzEq] at hRlow
  linarith

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology.BackwardPointTrace
