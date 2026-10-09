import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KappaDiagonalAlignP6D2

/-!
# `Pre841` / trace-local κ ⇒ 基点种子体积 `hseed`（O-CH11-P6ANCH G4a，后缀 `_P6M`）

`ObservedHistory.false_of_not_good_extendAt_P6D2`（`Ch11/P6ClosureP6D2.lean`）的 `hseed`：
`∀ᶠ n, ofReal (w (r₀/√R n)³) ≤ Vol_{g(ts n)} B(ys n, r₀/√R n)`。两个一行级 adapter：
* `hseed_of_pre841_P6M`：`Pre841Data_C11K.volume_ge`（(K-seq)，取 `D = B = 1`、`L = r₀`、`v = ts n`、
  trace = `BackwardPointTrace.singleton`、`ϱ = r₀`）+ 尺度不变性 `le_ballVolume_scaleMetric_iff`；
  `w = d.kappa`。
* `hseed_of_tracedKappa_P6M`：P6ClosureP6D2 的 trace-local `hkappa`（`r'' = r₀/√R ≤ ρnc n`，由
  `ρnc √R → ∞` eventually）；`w = κ`。
两者唯一的几何前提：**基点受控球** `hctrl : ∀ᶠ n, isParabolicallyRmControlledBall (ts n) (ys n)
(r₀/√R n)`（`(K-seq)` / `hkappa` 只对受控球给体积；`hctrl` 显式列出，不新建 Prop）。
consumer：同一个 `Pre841` 包同时给 P6ClosureP6D2 的 `hkappa`（G0b）与 `hseed`（本文件），`κ = w = d.kappa`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Manifold ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

namespace ObservedHistory

universe u

/-- 基点属于自己的正半径球。 -/
private theorem mem_ball_self_P6M (H : ObservedHistory.{u}) (t : Icc (0 : ℝ) H.horizon)
    (y : (H.stageAt t).Carrier) {r : ℝ} (hr : 0 < r) :
    y ∈ riemannianBallOf (H.stageMetric (H.activeStage t) t) y r := by
  change riemannianEDistOf (H.stageMetric (H.activeStage t) t) y y < ENNReal.ofReal r
  rw [riemannianEDistOf_self]
  exact ENNReal.ofReal_pos.mpr hr

/-- **`Pre841` ⇒ `hseed`**：(K-seq) 在基点、`v = ts`、单点 trace、`ϱ = r₀` 处取值，再用尺度不变性把
`scaleMetric (R n)` 下半径 `r₀` 的球换回 `g(ts)` 下半径 `r₀/√R` 的球；`w = d.kappa`。 -/
theorem hseed_of_pre841_P6M {H : ℕ → ObservedHistory.{u}} {t : ∀ n, Icc (0 : ℝ) (H n).horizon}
    {y : ∀ n, ((H n).stageAt (t n)).Carrier} {R : ℕ → ℝ} {hR : ∀ n, 0 < R n}
    (d : GC.LongTime.Ch11.Pre841Data_C11K H t y R hR) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hctrl : ∀ᶠ n in atTop,
      (H n).isParabolicallyRmControlledBall (t n) (y n) (r₀ / Real.sqrt (R n))) :
    ∀ᶠ n in atTop,
      ENNReal.ofReal (d.kappa * (r₀ / Real.sqrt (R n)) ^ 3) ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel ((H n).stageAt (t n)).Carrier
          ((H n).stageMetric ((H n).activeStage (t n)) (t n))
          (riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
            (r₀ / Real.sqrt (R n))) := by
  filter_upwards [d.volume_ge 1 r₀ 1 one_pos hr₀ one_pos, hctrl] with n hn hc
  have hsR : 0 < Real.sqrt (R n) := Real.sqrt_pos.mpr (hR n)
  have hy := mem_ball_self_P6M (H n) (t n) (y n) (div_pos one_pos hsR)
  have h0 : (t n : ℝ) - 1 / R n ≤ t n := sub_le_self _ (div_pos one_pos (hR n)).le
  have hc' : (H n).isParabolicallyRmControlledBall (t n) (y n)
      (r₀ / Real.sqrt (R n)) := hc
  have h := hn (y n) hy (t n) le_rfl h0
    (BackwardPointTrace.singleton (H n) ((H n).activeStage (t n)) (y n)) r₀ hr₀ le_rfl hc'
  have hr : r₀ = Real.sqrt (R n) * (r₀ / Real.sqrt (R n)) := (mul_div_cancel₀ _ hsR.ne').symm
  rw [hr] at h
  have hfin : Module.finrank ℝ ThreeSpace = 3 := by simp
  exact (Geometry.Collapse.le_ballVolume_scaleMetric_iff hfin (R n) (hR n)).1 h

/-- **trace-local κ ⇒ `hseed`**：P6ClosureP6D2 的 `hkappa`（`D = T = 1`、`v = ts`、单点 trace）在
`r'' = r₀/√R ≤ ρnc n`（eventually，`ρnc √R → ∞`）处取值；`w = κ`。 -/
theorem hseed_of_tracedKappa_P6M {Hs : ℕ → ObservedHistory.{u}}
    {ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon} {ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier}
    {R : ℕ → ℝ} (hR : ∀ n, 0 < R n) {κ : ℝ} (ρnc : ℕ → ℝ)
    (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop)
    (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ ts n), (ts n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (ts n))
          ((Hs n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Hs n).isParabolicallyRmControlledBall v
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Hs n).stageMetric ((Hs n).activeStage v) v)
              (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) r'')
    {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hctrl : ∀ᶠ n in atTop,
      (Hs n).isParabolicallyRmControlledBall (ts n) (ys n) (r₀ / Real.sqrt (R n))) :
    ∀ᶠ n in atTop,
      ENNReal.ofReal (κ * (r₀ / Real.sqrt (R n)) ^ 3) ≤
        Integral.Measure.riemannianVolumeMeasure ThreeModel ((Hs n).stageAt (ts n)).Carrier
          ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n))
          (riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (ts n)) (ts n)) (ys n)
            (r₀ / Real.sqrt (R n))) := by
  filter_upwards [hkappa 1 1 one_pos one_pos, hctrl, hradii.eventually_ge_atTop r₀]
    with n hn hc hρ
  have hsR : 0 < Real.sqrt (R n) := Real.sqrt_pos.mpr (hR n)
  have hy := mem_ball_self_P6M (Hs n) (ts n) (ys n) (div_pos one_pos hsR)
  have h0 : (ts n : ℝ) - 1 / R n ≤ ts n := sub_le_self _ (div_pos one_pos (hR n)).le
  have hρ' : r₀ / Real.sqrt (R n) ≤ ρnc n := (div_le_iff₀ hsR).mpr hρ
  have hc' : (Hs n).isParabolicallyRmControlledBall (ts n) (ys n)
      (r₀ / Real.sqrt (R n)) := hc
  exact hn (ys n) hy (ts n) le_rfl h0
    (BackwardPointTrace.singleton (Hs n) ((Hs n).activeStage (ts n)) (ys n))
    (r₀ / Real.sqrt (R n)) (div_pos hr₀ hsR) hρ' hc'

/-- consumer：同一个 `Pre841` 包给出 P6ClosureP6D2 的 `ρnc` / `hradii` / `hkappa`（G0b，`κ = d.kappa`）
与 `hseed`（本文件，`w = d.kappa`）；唯一额外几何前提 = 基点受控球 `hctrl`。 -/
example {H : ℕ → ObservedHistory.{u}} {t : ∀ n, Icc (0 : ℝ) (H n).horizon}
    {y : ∀ n, ((H n).stageAt (t n)).Carrier} {R : ℕ → ℝ} {hR : ∀ n, 0 < R n}
    (d : GC.LongTime.Ch11.Pre841Data_C11K H t y R hR) (σ : ℕ → ℝ)
    (hσ : Tendsto (fun n => σ n * Real.sqrt (R n)) atTop atTop) {r₀ : ℝ} (hr₀ : 0 < r₀)
    (hctrl : ∀ᶠ n in atTop,
      (H n).isParabolicallyRmControlledBall (t n) (y n) (r₀ / Real.sqrt (R n))) :
    ∃ ρnc : ℕ → ℝ, (∀ n, ρnc n ≤ σ n) ∧
      Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop ∧
      ∀ᶠ n in atTop,
        ENNReal.ofReal (d.kappa * (r₀ / Real.sqrt (R n)) ^ 3) ≤
          Integral.Measure.riemannianVolumeMeasure ThreeModel ((H n).stageAt (t n)).Carrier
            ((H n).stageMetric ((H n).activeStage (t n)) (t n))
            (riemannianBallOf ((H n).stageMetric ((H n).activeStage (t n)) (t n)) (y n)
              (r₀ / Real.sqrt (R n))) := by
  obtain ⟨ρnc, hle, hradii, hkappa⟩ := exists_tracedKappa_le_of_pre841_P6D2 d σ hσ
  exact ⟨ρnc, hle, hradii, hseed_of_tracedKappa_P6M hR ρnc hradii hkappa hr₀ hctrl⟩

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
