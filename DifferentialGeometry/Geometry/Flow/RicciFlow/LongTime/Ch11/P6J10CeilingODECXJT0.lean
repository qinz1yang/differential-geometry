import DifferentialGeometry.Analysis.Calculus.Derivative.ClippedReciprocal
import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.BackwardTraceScalarControl.TimeLocal

/-!
# T1：ceiling ODE（CX-J10T0 G1，后缀 `_CXJT0`；R-C11-16 D-2/D-4 第一步）

R-C11-16 D-2 的 ceiling 机制：沿**既有**轨迹 `f`，导数只在 `{f > q_sel}` 上假设
（`q_sel = Cg·R*`），ceiling `B = Q_b·R*`（`q_sel ≤ B`）。在 `{f > B}` 段积分 `1/f`
（这里用截断 `(max B f)⁻¹` 的 Lipschitz 性，树内 `lipschitzOnWith_inv_max_of_quadratic_deriv_bound_Icc`），
`f ≤ B` 处**不用导数**：
* `le_div_one_sub_of_ceilingODE_CXJT0`：`C·B·(t₀−s) < 1 ⇒ f(s) ≤ B / (1 − C·B·(t₀−s))`；
* `le_two_mul_of_ceilingODE_CXJT0`：`C·B·(t₀−a) ≤ 1/2 ⇒ ∀ s ∈ [a, t₀], f(s) ≤ 2B`；
* `le_two_mul_of_ceilingODE_scaled_CXJT0`：`q_sel = Cg·R*`、`B = Q_b·R*`、`max{C_ball, Cg, 1} ≤ Q_b`、
  深度 `t₀ − a ≤ T/R*`、`2·C·Q_b·T ≤ 1`；`_doubled` 版导数常数 `2C`、`4·C·Q_b·T ≤ 1`；
* trace 版 `scalar_le_two_mul_ceiling_trace_CXJT0` / `_scaled_`：树内
  `BackwardPointTrace.scalar_le_two_mul_of_time_local_derivative_control`（导数阈值 = ceiling `M`）的
  "阈值 `q_sel ≤ M`" 形——footprint 只在 `q_sel` 以上要（小阈值 ⇒ 大阈值，单调方向正确）。
只给沿既有轨迹的上界；轨迹存在 / unscathed / 正下界另付。无 `qcap < R`，无 traced region 前提。
-/

set_option autoImplicit false

noncomputable section

open Set
open DifferentialGeometry.Geometry.Curvature
open scoped NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **ceiling ODE（锐形，`_CXJT0`）**：`f(t₀) ≤ B`，导数只在 `{f > q_sel}`（`q_sel ≤ B`）上有
`|f'| ≤ C f²` ⇒ `C·B·(t₀−s) < 1` 时 `f(s) ≤ B / (1 − C·B·(t₀−s))`。 -/
theorem le_div_one_sub_of_ceilingODE_CXJT0 {f f' : ℝ → ℝ} {a t₀ qsel B : ℝ} {C : ℝ≥0}
    (hB : 0 < B) (hqB : qsel ≤ B) (hc : ContinuousOn f (Icc a t₀))
    (hd : ∀ s ∈ Ioo a t₀, qsel < f s → HasDerivAt f (f' s) s)
    (hb : ∀ s ∈ Ioo a t₀, qsel < f s → |f' s| ≤ C * f s ^ 2) (hat : a ≤ t₀)
    (hend : f t₀ ≤ B) :
    ∀ s ∈ Icc a t₀, C * B * (t₀ - s) < 1 → f s ≤ B / (1 - C * B * (t₀ - s)) := by
  intro s hs hlt
  have hlip := DifferentialGeometry.Analysis.lipschitzOnWith_inv_max_of_quadratic_deriv_bound_Icc
    (r' := f') hB hc (fun t ht h => hd t ht (hqB.trans_lt h))
    (fun t ht h => hb t ht (hqB.trans_lt h))
  have hdist := hlip.dist_le_mul s hs t₀ ⟨hat, le_rfl⟩
  rw [Real.dist_eq, Real.dist_eq, abs_sub_comm s t₀, abs_of_nonneg (sub_nonneg.mpr hs.2),
    max_eq_left hend] at hdist
  have hlow := (abs_le.mp hdist).1
  have hpos : 0 < 1 - C * B * (t₀ - s) := by linarith
  have hmpos : 0 < max B (f s) := hB.trans_le (le_max_left _ _)
  have hinv : (1 - C * B * (t₀ - s)) / B ≤ (max B (f s))⁻¹ := by
    have he : (1 - C * B * (t₀ - s)) / B = B⁻¹ - C * (t₀ - s) := by
      field_simp
    rw [he]
    linarith
  have hle : max B (f s) ≤ B / (1 - C * B * (t₀ - s)) := by
    rw [le_div_iff₀ hpos]
    have h1 := mul_le_mul_of_nonneg_left hinv hmpos.le
    rw [mul_inv_cancel₀ hmpos.ne'] at h1
    rw [mul_div_assoc', div_le_iff₀ hB, one_mul] at h1
    linarith
  exact (le_max_right _ _).trans hle

/-- **ceiling ODE（`2B` 形，`_CXJT0`）**：`C·B·(t₀−a) ≤ 1/2 ⇒ ∀ s ∈ [a, t₀], f(s) ≤ 2B`。 -/
theorem le_two_mul_of_ceilingODE_CXJT0 {f f' : ℝ → ℝ} {a t₀ qsel B : ℝ} {C : ℝ≥0}
    (hB : 0 < B) (hqB : qsel ≤ B) (hc : ContinuousOn f (Icc a t₀))
    (hd : ∀ s ∈ Ioo a t₀, qsel < f s → HasDerivAt f (f' s) s)
    (hb : ∀ s ∈ Ioo a t₀, qsel < f s → |f' s| ≤ C * f s ^ 2) (hat : a ≤ t₀)
    (hend : f t₀ ≤ B) (htime : C * B * (t₀ - a) ≤ 1 / 2) :
    ∀ s ∈ Icc a t₀, f s ≤ 2 * B := by
  intro s hs
  have hCB : 0 ≤ (C : ℝ) * B := mul_nonneg C.coe_nonneg hB.le
  have hx : C * B * (t₀ - s) ≤ 1 / 2 :=
    (mul_le_mul_of_nonneg_left (by linarith [hs.1]) hCB).trans htime
  have h := le_div_one_sub_of_ceilingODE_CXJT0 hB hqB hc hd hb hat hend s hs (by linarith)
  refine h.trans ?_
  rw [div_le_iff₀ (by linarith)]
  nlinarith

/-- **深度形（`_CXJT0`）**：`q_sel = Cg·R*`、`B = Q_b·R*`、`max{C_ball, Cg, 1} ≤ Q_b`、
`f(t₀) ≤ C_ball·R*`、深度 `t₀ − a ≤ T/R*`、`2·C·Q_b·T ≤ 1` ⇒ `f ≤ 2·(Q_b·R*)`。 -/
theorem le_two_mul_of_ceilingODE_scaled_CXJT0 {f f' : ℝ → ℝ} {a t₀ Rs Cg Cball Qb T : ℝ}
    {C : ℝ≥0} (hRs : 0 < Rs) (hQb : max (max Cball Cg) 1 ≤ Qb) (hc : ContinuousOn f (Icc a t₀))
    (hd : ∀ s ∈ Ioo a t₀, Cg * Rs < f s → HasDerivAt f (f' s) s)
    (hb : ∀ s ∈ Ioo a t₀, Cg * Rs < f s → |f' s| ≤ C * f s ^ 2) (hat : a ≤ t₀)
    (hend : f t₀ ≤ Cball * Rs) (hdepth : t₀ - a ≤ T / Rs) (hstep : 2 * C * Qb * T ≤ 1) :
    ∀ s ∈ Icc a t₀, f s ≤ 2 * (Qb * Rs) := by
  have hQ1 : 1 ≤ Qb := (le_max_right _ _).trans hQb
  have hCg : Cg ≤ Qb := ((le_max_right _ _).trans (le_max_left _ _)).trans hQb
  have hCb : Cball ≤ Qb := ((le_max_left _ _).trans (le_max_left _ _)).trans hQb
  refine le_two_mul_of_ceilingODE_CXJT0 (mul_pos (by linarith) hRs)
    (mul_le_mul_of_nonneg_right hCg hRs.le) hc hd hb hat
    (hend.trans (mul_le_mul_of_nonneg_right hCb hRs.le)) ?_
  have hCQ : 0 ≤ (C : ℝ) * (Qb * Rs) := mul_nonneg C.coe_nonneg (by nlinarith)
  have h1 : (C : ℝ) * (Qb * Rs) * (t₀ - a) ≤ C * (Qb * Rs) * (T / Rs) :=
    mul_le_mul_of_nonneg_left hdepth hCQ
  have h2 : (C : ℝ) * (Qb * Rs) * (T / Rs) = (2 * C * Qb * T) / 2 := by
    field_simp
  linarith

/-- **深度形，导数常数放大为 `2C`（`_CXJT0`）**：`|f'| ≤ 2C f²`、`4·C·Q_b·T ≤ 1`。 -/
theorem le_two_mul_of_ceilingODE_scaled_doubled_CXJT0 {f f' : ℝ → ℝ}
    {a t₀ Rs Cg Cball Qb T : ℝ} {C : ℝ≥0} (hRs : 0 < Rs) (hQb : max (max Cball Cg) 1 ≤ Qb)
    (hc : ContinuousOn f (Icc a t₀))
    (hd : ∀ s ∈ Ioo a t₀, Cg * Rs < f s → HasDerivAt f (f' s) s)
    (hb : ∀ s ∈ Ioo a t₀, Cg * Rs < f s → |f' s| ≤ (2 * C : ℝ≥0) * f s ^ 2) (hat : a ≤ t₀)
    (hend : f t₀ ≤ Cball * Rs) (hdepth : t₀ - a ≤ T / Rs) (hstep : 4 * C * Qb * T ≤ 1) :
    ∀ s ∈ Icc a t₀, f s ≤ 2 * (Qb * Rs) :=
  le_two_mul_of_ceilingODE_scaled_CXJT0 hRs hQb hc hd hb hat hend hdepth (by
    push_cast
    linarith)

namespace BackwardPointTrace

/-- **trace 版 ceiling（`_CXJT0`）**：footprint 只在 `q_sel` 以上（`q_sel ≤ M`），端点 `≤ M`，
`C·M·(t − a) ≤ 1/2` ⇒ 沿 trace `≤ 2M`。树内 `scalar_le_two_mul_of_time_local_derivative_control`
（阈值 `M`）的小阈值形。 -/
theorem scalar_le_two_mul_ceiling_trace_CXJT0
    {H : ObservedHistory.{u}} {a t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t)
    {y : (H.stageAt t).Carrier}
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) y)
    {Ctime : ℝ≥0} {qsel M : ℝ} (hM : 0 < M) (hqM : qsel ≤ M)
    (hbound : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      H.time (H.activeStage v) < (v : ℝ) → (v : ℝ) < H.horizon →
      qsel < metricScalarAt (H.stageMetric (H.activeStage v) v)
        (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) →
      |derivWithin (fun s => metricScalarAt (H.stageMetric (H.activeStage v) s)
        (A.point (H.activeStage v) (H.activeStage_mono hav)
          (H.activeStage_mono hvt))) (Iic (v : ℝ)) v| ≤
        Ctime * metricScalarAt (H.stageMetric (H.activeStage v) v)
          (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) ^ 2)
    (hscalar : metricScalarAt (H.stageMetric (H.activeStage t) t) y ≤ M)
    (htime : Ctime * M * ((t : ℝ) - a) ≤ 1 / 2) :
    ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      metricScalarAt (H.stageMetric (H.activeStage v) v)
        (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) ≤
        2 * M :=
  BackwardPointTrace.scalar_le_two_mul_of_time_local_derivative_control hat A hM
    (fun v hav hvt h1 h2 hR => hbound v hav hvt h1 h2 (hqM.trans_lt hR)) hscalar htime

/-- **trace 版深度形（`_CXJT0`）**：`q_sel = Cg·R*`、`M = Q_b·R*`、端点 `≤ C_ball·R*`、
`t − a ≤ T/R*`、`2·Ctime·Q_b·T ≤ 1` ⇒ 沿 trace `≤ 2·(Q_b·R*)`。 -/
theorem scalar_le_two_mul_ceiling_trace_scaled_CXJT0
    {H : ObservedHistory.{u}} {a t : Icc (0 : ℝ) H.horizon} (hat : a ≤ t)
    {y : (H.stageAt t).Carrier}
    (A : BackwardPointTrace H (H.activeStage a) (H.activeStage t) (H.activeStage_mono hat) y)
    {Ctime : ℝ≥0} {Rs Cg Cball Qb T : ℝ} (hRs : 0 < Rs) (hQb : max (max Cball Cg) 1 ≤ Qb)
    (hbound : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      H.time (H.activeStage v) < (v : ℝ) → (v : ℝ) < H.horizon →
      Cg * Rs < metricScalarAt (H.stageMetric (H.activeStage v) v)
        (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) →
      |derivWithin (fun s => metricScalarAt (H.stageMetric (H.activeStage v) s)
        (A.point (H.activeStage v) (H.activeStage_mono hav)
          (H.activeStage_mono hvt))) (Iic (v : ℝ)) v| ≤
        Ctime * metricScalarAt (H.stageMetric (H.activeStage v) v)
          (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) ^ 2)
    (hscalar : metricScalarAt (H.stageMetric (H.activeStage t) t) y ≤ Cball * Rs)
    (hdepth : (t : ℝ) - a ≤ T / Rs) (hstep : 2 * Ctime * Qb * T ≤ 1) :
    ∀ (v : Icc (0 : ℝ) H.horizon) (hav : a ≤ v) (hvt : v ≤ t),
      metricScalarAt (H.stageMetric (H.activeStage v) v)
        (A.point (H.activeStage v) (H.activeStage_mono hav) (H.activeStage_mono hvt)) ≤
        2 * (Qb * Rs) := by
  have hQ1 : 1 ≤ Qb := (le_max_right _ _).trans hQb
  have hCg : Cg ≤ Qb := ((le_max_right _ _).trans (le_max_left _ _)).trans hQb
  have hCb : Cball ≤ Qb := ((le_max_left _ _).trans (le_max_left _ _)).trans hQb
  refine scalar_le_two_mul_ceiling_trace_CXJT0 hat A (mul_pos (by linarith) hRs)
    (mul_le_mul_of_nonneg_right hCg hRs.le) hbound
    (hscalar.trans (mul_le_mul_of_nonneg_right hCb hRs.le)) ?_
  have hCQ : 0 ≤ (Ctime : ℝ) * (Qb * Rs) := mul_nonneg Ctime.coe_nonneg (by nlinarith)
  have h1 : (Ctime : ℝ) * (Qb * Rs) * ((t : ℝ) - a) ≤ Ctime * (Qb * Rs) * (T / Rs) :=
    mul_le_mul_of_nonneg_left hdepth hCQ
  have h2 : (Ctime : ℝ) * (Qb * Rs) * (T / Rs) = (2 * Ctime * Qb * T) / 2 := by
    field_simp
  linarith

end BackwardPointTrace

/-- consumer（`_CXJT0` G1）：`f ≡ B/2`（无导数前提可用之处：`f ≤ q_sel` 恒成立时 `hd`/`hb` 空真）⇒ `≤ 2B`。 -/
example {a t₀ B : ℝ} (hB : 0 < B) (hat : a ≤ t₀) :
    ∀ s ∈ Icc a t₀, (fun _ : ℝ => B / 2) s ≤ 2 * B :=
  le_two_mul_of_ceilingODE_CXJT0 (f' := fun _ => 0) (C := 0) (qsel := B) hB le_rfl
    continuousOn_const (fun _ _ h => absurd h (by linarith)) (fun _ _ h => absurd h (by linarith))
    hat (by linarith) (by simp)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
