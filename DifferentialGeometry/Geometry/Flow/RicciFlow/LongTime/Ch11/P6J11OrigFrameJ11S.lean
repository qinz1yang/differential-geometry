import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KappaRescaleP6CK
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6VolumeRescaleCXSP

/-!
# J11 帧变换：重标度 κ 测试 ⇒ 原尺度 κ 测试（O-CH11-J11STAY G3a，后缀 `_J11S`）

hgap J11 的结论写在原尺度 `(Ho n).toHistory`、时刻 `unscaleTime σ`、基点 `uncastRescale y`、尺度
`R/c`、度量 `scaleMetric (R/c)`；κ 来源（FRESH + interior footprint）在重标度 `Kh = (Ho).rescale_P6N c`。
P6CK `volume_rescale_P6CK` 是**原 ⇒ 重标度**；本文件给反向：
* `ctrl_rescale_J11S`：原受控球 `(t, p, b)` ⇒ 重标度受控球 `(t/c, p̃, b/√c)`
  （`hasSmallParabolicCurvature_rescale_P6X3` 的 `isParabolicallyRmControlledBall` 孪生）；
* `volume_orig_of_rescale_J11S`（单个 history）：重标度 `(s, y, R)` 的 κ 测试（`b ≤ ρ`）⇒ 原尺度
  `(t, p, Ro)` 的 κ 测试（`ϱ ≤ L`，`L/√R ≤ ρ`），`κ` 原样；
* `kappa_orig_of_rescale_J11S`（`s = σ`、`p = uncastRescale y`、`Ro = R/c` 的特化，即 J11 原尺度体形）。
全 PROVED（树内 P6X / P6X3 / P6CK / CXSP 引理）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

namespace RetainedCoreHistory

variable (K : RetainedCoreHistory.{u}) {c : ℝ} (hc : 0 < c)

/-- **受控球重标度（`_J11S`）**：`(t, p, b) ↦ (t/c, p̃, b/√c)`。 -/
theorem ctrl_rescale_J11S (t : Icc (0 : ℝ) K.toHistory.horizon)
    (p : (K.toHistory.stageAt t).Carrier) {b : ℝ}
    (h : K.toHistory.isParabolicallyRmControlledBall t p b) :
    (K.rescale_P6N c hc).toHistory.isParabolicallyRmControlledBall (K.rescaleTime_P6X hc t)
      (K.castRescale_P6X hc t p) (b / Real.sqrt c) := by
  obtain ⟨hb, a, hat, ha, htr⟩ := h
  refine ⟨div_pos hb (Real.sqrt_pos.mpr hc), K.rescaleTime_P6X hc a, K.rescaleTime_mono_P6X hc hat,
    ?_, ?_⟩
  · change (a : ℝ) / c = (t : ℝ) / c - (b / Real.sqrt c) ^ 2
    rw [ha, div_pow, Real.sq_sqrt hc.le, sub_div]
  · intro xS hxS
    obtain ⟨x, rfl⟩ := K.castRescale_surj_P6CK hc t xS
    have hx : x ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage t) t) p b :=
      K.ball_of_castRescale_P6CK hc t p x hxS
    obtain ⟨tr, htr'⟩ := htr x hx
    exact ⟨K.seedTrace_rescale_P6X hc hat tr, K.isRmControlled_rescale_P6X3 hc hat tr htr'⟩

/-- 重标度 trace 在起点的点 = 原 trace 起点的 `castRescale`。 -/
theorem seedTrace_rescale_point_J11S {v t : Icc (0 : ℝ) K.toHistory.horizon} (hvt : v ≤ t)
    {x : (K.toHistory.stageAt t).Carrier}
    (tr : BackwardPointTrace K.toHistory (K.toHistory.activeStage v) (K.toHistory.activeStage t)
      (K.toHistory.activeStage_mono hvt) x)
    (h2 : (K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc v) ≤
      (K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc t)) :
    (K.seedTrace_rescale_P6X hc hvt tr).point
        ((K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc v)) le_rfl h2 =
      K.castRescale_P6X hc v
        (tr.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvt)) := by
  have ha := K.activeStage_rescaleTime_P6X hc v
  have ht := K.activeStage_rescaleTime_P6X hc t
  have h1' : K.toHistory.activeStage v ≤
      (K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc v) := ha.ge
  have h2' : (K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc v) ≤
      K.toHistory.activeStage t := h2.trans ht.le
  have hpt : (K.seedTrace_rescale_P6X hc hvt tr).point
      ((K.rescale_P6N c hc).toHistory.activeStage (K.rescaleTime_P6X hc v)) le_rfl h2 =
      tr.point _ h1' h2' :=
    trace_transfer_point_P6X3 (Hh := (K.rescale_P6N c hc).toHistory) ha.symm ht.symm
      (K.heq_castRescale_P6X hc t x).symm (K.traceToRescale_P6N c hc tr) _ le_rfl h2
  rw [hpt]
  refine eq_of_heq ((point_heq_P6CK tr ha _ _ le_rfl (K.toHistory.activeStage_mono hvt)).trans
    (K.heq_castRescale_P6X hc v _).symm)

/-- **原尺度 κ 测试 ⇐ 重标度 κ 测试（单个 history，`_J11S`，PROVED）**：`volume_rescale_P6CK` 的反向。
重标度 `(s, y, R)`（`s = t/c`、`y = p̃`、`R = c·Ro`）上半径 `≤ ρ` 的测试 ⇒ 原 `(t, p, Ro)` 上
`ϱ ≤ L` 的测试（`L/√R ≤ ρ`）。 -/
theorem volume_orig_of_rescale_J11S (t : Icc (0 : ℝ) K.toHistory.horizon)
    (p : (K.toHistory.stageAt t).Carrier) {Ro : ℝ} (hRo : 0 < Ro) {κ D L B ρ : ℝ}
    (s : Icc (0 : ℝ) (K.rescale_P6N c hc).toHistory.horizon)
    (y : ((K.rescale_P6N c hc).toHistory.stageAt s).Carrier) {R : ℝ} (hR : 0 < R)
    (hs : K.rescaleTime_P6X hc t = s) (hy : HEq (K.castRescale_P6X hc t p) y)
    (hRR : c * Ro = R) (hLρ : L / Real.sqrt R ≤ ρ)
    (hK : ∀ x ∈ riemannianBallOf ((K.rescale_P6N c hc).toHistory.stageMetric
        ((K.rescale_P6N c hc).toHistory.activeStage s) s) y (D / Real.sqrt R),
      ∀ (v : Icc (0 : ℝ) (K.rescale_P6N c hc).toHistory.horizon) (hvt : v ≤ s),
        (s : ℝ) - B / R ≤ v →
      ∀ tr : BackwardPointTrace (K.rescale_P6N c hc).toHistory
        ((K.rescale_P6N c hc).toHistory.activeStage v)
        ((K.rescale_P6N c hc).toHistory.activeStage s)
        ((K.rescale_P6N c hc).toHistory.activeStage_mono hvt) x,
      ∀ b : ℝ, 0 < b → b ≤ ρ →
        (K.rescale_P6N c hc).toHistory.isParabolicallyRmControlledBall v
          (tr.point ((K.rescale_P6N c hc).toHistory.activeStage v) le_rfl
            ((K.rescale_P6N c hc).toHistory.activeStage_mono hvt)) b →
        ENNReal.ofReal (κ * b ^ 3) ≤
          ballVolume ((K.rescale_P6N c hc).toHistory.stageMetric
            ((K.rescale_P6N c hc).toHistory.activeStage v) v)
            (tr.point ((K.rescale_P6N c hc).toHistory.activeStage v) le_rfl
              ((K.rescale_P6N c hc).toHistory.activeStage_mono hvt)) b) :
    ∀ x ∈ riemannianBallOf (K.toHistory.stageMetric (K.toHistory.activeStage t) t) p
        (D / Real.sqrt Ro),
      ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hvt : v ≤ t), (t : ℝ) - B / Ro ≤ v →
      ∀ tr : BackwardPointTrace K.toHistory (K.toHistory.activeStage v)
        (K.toHistory.activeStage t) (K.toHistory.activeStage_mono hvt) x,
      ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ L →
        K.toHistory.isParabolicallyRmControlledBall v
          (tr.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvt))
          (ϱ / Real.sqrt Ro) →
        ENNReal.ofReal (κ * ϱ ^ 3) ≤
          ballVolume (scaleMetric Ro hRo (K.toHistory.stageMetric (K.toHistory.activeStage v) v))
            (tr.point (K.toHistory.activeStage v) le_rfl (K.toHistory.activeStage_mono hvt)) ϱ := by
  subst hs hRR
  obtain rfl := eq_of_heq hy
  have hsc : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hsRo : 0 < Real.sqrt Ro := Real.sqrt_pos.mpr hRo
  have hsR : Real.sqrt (c * Ro) = Real.sqrt c * Real.sqrt Ro := Real.sqrt_mul hc.le Ro
  intro x hx v hvt hv tr ϱ hϱ hϱL hctrl
  have hx' := K.ball_castRescale_P6X hc t p x hx
  have e1 : D / Real.sqrt Ro / Real.sqrt c = D / Real.sqrt (c * Ro) := by
    rw [hsR, div_div, mul_comm]
  rw [e1] at hx'
  have hvt' : K.rescaleTime_P6X hc v ≤ K.rescaleTime_P6X hc t := K.rescaleTime_mono_P6X hc hvt
  have hv' : ((K.rescaleTime_P6X hc t : Icc (0 : ℝ) (K.rescale_P6N c hc).toHistory.horizon) : ℝ) -
      B / (c * Ro) ≤ (K.rescaleTime_P6X hc v : ℝ) := by
    change (t : ℝ) / c - B / (c * Ro) ≤ (v : ℝ) / c
    have e : B / (c * Ro) = B / Ro / c := by rw [div_div, mul_comm]
    rw [e, ← sub_div]
    exact div_le_div_of_nonneg_right hv hc.le
  set tr' := K.seedTrace_rescale_P6X hc hvt tr
  have hpt := K.seedTrace_rescale_point_J11S hc hvt tr
    ((K.rescale_P6N c hc).toHistory.activeStage_mono hvt')
  have e2 : ϱ / Real.sqrt Ro / Real.sqrt c = ϱ / Real.sqrt (c * Ro) := by
    rw [hsR, div_div, mul_comm]
  have hctrl' := K.ctrl_rescale_J11S hc v _ hctrl
  rw [e2, ← hpt] at hctrl'
  have hbρ : ϱ / Real.sqrt (c * Ro) ≤ ρ :=
    (div_le_div_of_nonneg_right hϱL (Real.sqrt_nonneg _)).trans hLρ
  have hb := hK (K.castRescale_P6X hc t x) hx' (K.rescaleTime_P6X hc v) hvt' hv' tr'
    (ϱ / Real.sqrt (c * Ro)) (div_pos hϱ (Real.sqrt_pos.mpr (mul_pos hc hRo))) hbρ hctrl'
  rw [hpt, ← e2] at hb
  have hO := (RetainedCoreHistory.le_ballVolume_castRescale_iff_CXSP hc).mp hb
  have hdim : Module.finrank ℝ ThreeSpace = 3 := by simp [ThreeSpace]
  have e3 : Real.sqrt Ro * (ϱ / Real.sqrt Ro) = ϱ := mul_div_cancel₀ ϱ hsRo.ne'
  have h := (le_ballVolume_scaleMetric_iff hdim Ro hRo
    (g := K.toHistory.stageMetric (K.toHistory.activeStage v) v) (w := κ)
    (t := ϱ / Real.sqrt Ro)).mpr hO
  rwa [e3] at h

end RetainedCoreHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
