import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KdataRescaleP6X3

/-!
# `DerivativeBoundBefore` 终点 min 形：重标度与全形 ⇒ 截断形（O-CH11-KTRUNC1，`_P6KT`）

kernel 截断形槽（lead 10-08 裁定，`tK := Tn`）把 event slab / final slab 的时间导数界终点
从 `time j.succ` / `horizon` 换成 `min (time j.succ) tK` / `min horizon tK`。本文件给这一形状的
两个机械事实（无新 Prop，仍是既有 `DerivativeBoundBefore` 的终点参数化）：
* **重标度**（KTRUNC2 的 L3 用）：`∂R̃ = c²·∂R(c·)`，`Ctime` 不变、阈值 `Q ↦ c·Q`、终点
  `min a b ↦ min (a/c) (b/c)`；event 版 `eventSlabsDerivT_rescale_P6KT`
  （= `eventSlabsDerivative_rescale_P6X3`
  的截断孪生），final 版 `derivativeBoundBefore_finalSlab_min_rescale_P6KT`
  （= P6WR2 `derivativeBoundBefore_finalSlab_rescale_P6WR2` 的截断孪生，证明逐字 + 终点 `lt_min`）；
* **全形 ⇒ 截断形**（对任意 `tK`，`min_le_left` + `derivativeBoundBefore_mono`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **slab 级（`_P6KT`）**：终点 `min t₀ t₁` 的时间导数界在重标度下变成终点 `min (t₀/c) (t₁/c)`
（`Ctime` 不变、阈值 `qcan ↦ c·qcan`）。 -/
theorem OrientedThreeStage.IncomingSlab.derivativeBoundBefore_min_rescale_P6KT
    {P : OrientedThreeStage.{u}} {a s : ℝ} (G : P.IncomingSlab a s) {c : ℝ} (hc : 0 < c)
    {Ctime : ℝ≥0} {qcan t₀ t₁ : ℝ} (h : G.DerivativeBoundBefore Ctime qcan (min t₀ t₁)) :
    (G.rescale c hc).DerivativeBoundBefore Ctime (c * qcan) (min (t₀ / c) (t₁ / c)) := by
  rw [min_div_div_right hc.le]
  exact G.derivativeBoundBefore_rescale_P6X3 hc h

namespace RetainedCoreHistory

variable (K : RetainedCoreHistory.{u}) {c : ℝ} (hc : 0 < c)

/-- **event 截断形的重标度（`_P6KT`）**：`hslabKT` 形（终点 `min (time j.succ) tK`）⇒ 重标度 history
上同形（阈值 `c·Q`、截断点 `tK/c`）。= `eventSlabsDerivative_rescale_P6X3` 的截断孪生。 -/
theorem eventSlabsDerivT_rescale_P6KT {Ctime : ℝ≥0} {Q tK : ℝ}
    (h : ∀ j : Fin K.eventCount,
      (K.toHistory.event j).incoming.DerivativeBoundBefore Ctime Q (min (K.time j.succ) tK)) :
    ∀ j : Fin (K.rescale_P6N c hc).eventCount,
      ((K.rescale_P6N c hc).toHistory.event j).incoming.DerivativeBoundBefore Ctime (c * Q)
        (min ((K.rescale_P6N c hc).time j.succ) (tK / c)) :=
  fun j => (K.toHistory.event j).incoming.derivativeBoundBefore_min_rescale_P6KT hc (h j)

/-- **final 截断形的重标度（`_P6KT`）**：(D2T) 形（终点 `min horizon tK`）⇒ 重标度 history 的
final slab 同形（阈值 `c·qcan`、截断点 `tK/c`）。证明 = P6WR2 `derivativeBoundBefore_finalSlab_rescale_P6WR2`
逐字，只在 `hct` 处多一个 `lt_min`。 -/
theorem derivativeBoundBefore_finalSlab_min_rescale_P6KT {Ctime : ℝ≥0} {qcan tK : ℝ}
    (h : ∀ hK : K.time (Fin.last K.eventCount) < K.horizon,
      ((K.finalSlab hK).restrictIncoming le_rfl hK le_rfl).DerivativeBoundBefore Ctime qcan
        (min K.horizon tK))
    (hfin : (K.rescale_P6N c hc).time (Fin.last (K.rescale_P6N c hc).eventCount) <
      (K.rescale_P6N c hc).horizon) :
    OrientedThreeStage.IncomingSlab.DerivativeBoundBefore
      (((K.rescale_P6N c hc).finalSlab hfin).restrictIncoming le_rfl hfin le_rfl)
      Ctime (c * qcan) (min (K.rescale_P6N c hc).horizon (tK / c)) := by
  have h' : K.time (Fin.last K.eventCount) < K.horizon :=
    (div_lt_div_iff_of_pos_right hc).mp hfin
  have hG := h h'
  intro y t ht hq
  have hs : ∀ v, (((K.rescale_P6N c hc).finalSlab hfin).restrictIncoming le_rfl hfin
      le_rfl).flow.scalar v y =
      c * ((K.finalSlab h').restrictIncoming le_rfl h' le_rfl).flow.scalar (c * v) y := by
    intro v
    suffices key : ∀ z : (K.stage (Fin.last K.eventCount)).Carrier,
        metricScalarAt (((K.finalSlab h').rescale c hc).flow.base.metric v) z =
          c * metricScalarAt ((K.finalSlab h').flow.base.metric (c * v)) z from key y
    intro z
    rw [OrientedThreeStage.ClosedSlab.rescale_metric, metricScalarAt_scaleMetric, inv_inv]
  have hct : c * t ∈ Ioo (K.time (Fin.last K.eventCount)) (min K.horizon tK) := by
    obtain ⟨h1, h2⟩ := ht
    change K.time (Fin.last K.eventCount) / c < t at h1
    change t < min (K.horizon / c) (tK / c) at h2
    rw [div_lt_iff₀ hc] at h1
    rw [lt_min_iff, lt_div_iff₀ hc, lt_div_iff₀ hc] at h2
    exact ⟨by linarith, lt_min (by linarith [h2.1]) (by linarith [h2.2])⟩
  rw [hs] at hq
  have hq' : qcan < ((K.finalSlab h').restrictIncoming le_rfl h' le_rfl).flow.scalar (c * t) y :=
    (mul_lt_mul_iff_right₀ hc).mp hq
  have hD := hG y (c * t) hct hq'
  have hfun : (fun v => (((K.rescale_P6N c hc).finalSlab hfin).restrictIncoming le_rfl hfin
      le_rfl).flow.scalar v y) =
      fun v => c • (fun u => ((K.finalSlab h').restrictIncoming le_rfl h' le_rfl).flow.scalar u y)
        (c * v) := by
    funext v
    rw [hs, smul_eq_mul]
  rw [hfun, derivWithin_fun_const_smul_field,
    derivWithin_comp_mul_left c
      (fun u => ((K.finalSlab h').restrictIncoming le_rfl h' le_rfl).flow.scalar u y),
    LinearOrderedField.smul_Iic hc, hs, smul_eq_mul, smul_eq_mul]
  set D := derivWithin (fun u => ((K.finalSlab h').restrictIncoming le_rfl h' le_rfl).flow.scalar
    u y) (Iic (c * t)) (c * t)
  set Rz := ((K.finalSlab h').restrictIncoming le_rfl h' le_rfl).flow.scalar (c * t) y
  have hc2 : 0 < c ^ 2 := by positivity
  rw [show |c * (c * D)| = c ^ 2 * |D| by
      rw [abs_mul, abs_mul, abs_of_pos hc]; ring,
    show (Ctime : ℝ) * (c * Rz) ^ 2 = c ^ 2 * (Ctime * Rz ^ 2) by ring]
  exact (mul_le_mul_iff_of_pos_left hc2).mpr hD

/-- **全形 ⇒ event 截断形（`_P6KT`）**：`EventSlabsDerivative … (Fin.last _)` ⇒ 对任意 `tK` 的 `hslabKT` 形。 -/
theorem eventSlabsDerivT_of_full_P6KT {Ctime : ℝ≥0} {Q : ℝ}
    (h : K.EventSlabsDerivative Ctime Q (Fin.last K.eventCount)) (tK : ℝ) :
    ∀ j : Fin K.eventCount,
      (K.toHistory.event j).incoming.DerivativeBoundBefore Ctime Q (min (K.time j.succ) tK) :=
  fun j => (K.toHistory.event j).incoming.derivativeBoundBefore_mono (min_le_left _ _)
    (h j (Fin.castSucc_lt_last j))

/-- **全形 ⇒ final 截断形（`_P6KT`）**：(D2) ⇒ 对任意 `tK` 的 (D2T)。 -/
theorem finalSlabDerivT_of_full_P6KT {Ctime : ℝ≥0} {Q : ℝ}
    (h : ∀ hK : K.time (Fin.last K.eventCount) < K.horizon,
      ((K.finalSlab hK).restrictIncoming le_rfl hK le_rfl).DerivativeBoundBefore Ctime Q K.horizon)
    (tK : ℝ) :
    ∀ hK : K.time (Fin.last K.eventCount) < K.horizon,
      ((K.finalSlab hK).restrictIncoming le_rfl hK le_rfl).DerivativeBoundBefore Ctime Q
        (min K.horizon tK) :=
  fun hK => ((K.finalSlab hK).restrictIncoming le_rfl hK le_rfl).derivativeBoundBefore_mono
    (min_le_left _ _) (h hK)

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
