import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Pre841AlignC11K
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KappaBridgeP6B

/-!
# `hKappaLocal ⇒ Pre841` 的 consumer（S-CH11-PRE841 G4，后缀 `_C11K`）

P6B 的 `hKappaLocal`（`LocalKappaSupply_P6B F δ α (fun _ => 0)`，即 KL 字面**全尺度**形，作为
**公开条件前提**；**不得**把 `nr := ρ` 的有下界版靠"取 `nr := 0`"消去下界得到它——R-C11-2
D-R-C11-2-4：小半径要由 Q3 的小尺度补充另供，此处不替它证）经
S7（`LargerBallAccuracySupply_C11S`）与树内 L5（`localKappaWindow_of_late_P6B`）得 window 形，
再经 L7 survival 的距离结论 `hdist`、窗口条件 `hwin` 与 `(r n / 200) √(R n) → ∞`
（即 `Q_n r_n² → ∞`）打包成 `Pre841Data_C11K`：

`LocalKappaSupply_P6B → LocalKappaWindowAt_P6B → trace-local hkappa → Pre841Data_C11K`。

**方向只能是 `hKappaLocal ⇒ Pre841`**（`Pre841AlignC11K.lean` 文件头与 design 文档给精确差距）。
末尾 `example` 把整条链闭合：`LocalKappaSupply_P6B → Pre841Data_C11K → κ`，并读出基点时刻的
`LocalKappaAt_P6B` 结论块（`eventually_localKappa_base`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter DifferentialGeometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Collapse
open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open scoped Manifold ContDiff ENNReal Topology

namespace GC.LongTime.Ch11

universe u

/-! ## (i) 与 P6B `hKappaLocal` 的对齐：`hKappaLocal ⇒ Pre841`（单向，G4） -/

/-- **P6B window 形 ⇒ `Pre841`**【单向；需前提：window 的 `κ`、`hdist`、`hwin`、坏点处种子数据、
`(r n / 200) √(R n) → ∞`；反向不成立，见 `Pre841AlignC11K` 文件头】：
`tracedKappa_of_window_P6B`（L5 window + L7 survival 距离结论 `hdist` + 窗口条件 `hwin`）
给出 trace-local `hkappa`（`ρnc n = r n / 200`），再由 `ofTracedKappa`
（要求 `(r n / 200) √(R n) → ∞`，即 `Q_n r_n² → ∞`）打包成 `Pre841` 数据；`κ` 即 window 的 `κ`。
基点序列是 `(s n, y n)`（坏点），种子是 `(t n, p n, r n)`。 -/
def pre841Data_of_window_C11K {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {A κ : ℝ} (hκ : 0 < κ)
    (hW : LocalKappaWindowAt_P6B F (fun _ => 0) A κ)
    (ind : ℕ → ℕ)
    (N : Pre841NativeData_C11K (fun n => (F.tower.history (ind n)).toHistory))
    (t : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (p : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (t n)).Carrier) (r : ℕ → ℝ)
    (hlate : Tendsto (fun n => (t n : ℝ)) atTop atTop)
    (htime : ∀ n, 2 * r n ^ 2 < (t n : ℝ))
    (hsmall : ∀ n, hasSmallParabolicCurvature (F.tower.history (ind n)).toHistory (t n) (p n)
      (r n))
    (hvol : ∀ n, ENNReal.ofReal (A⁻¹ * r n ^ 3) ≤
      ballVolume ((F.tower.history (ind n)).toHistory.stageMetric
        ((F.tower.history (ind n)).toHistory.activeStage (t n)) (t n)) (p n) (r n))
    (aSeed : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (haT : ∀ n, aSeed n ≤ t n) (hclock : ∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2)
    (seedTrace : ∀ n, BackwardPointTrace (F.tower.history (ind n)).toHistory
      ((F.tower.history (ind n)).toHistory.activeStage (aSeed n))
      ((F.tower.history (ind n)).toHistory.activeStage (t n))
      ((F.tower.history (ind n)).toHistory.activeStage_mono (haT n)) (p n))
    (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (hst : ∀ n, s n ≤ t n)
    (y : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier) (R : ℕ → ℝ)
    (hR : ∀ n, 0 < R n)
    (hradii : Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (t n : ℝ) - r n ^ 2 / 2 ≤ (s n : ℝ) - T / R n)
    (hdist : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon) (hvs : v ≤ s n),
        (s n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage v)
        ((F.tower.history (ind n)).toHistory.activeStage (s n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono hvs) x,
      ∀ hav : aSeed n ≤ v,
        riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage v) v)
          ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage v)
            ((F.tower.history (ind n)).toHistory.activeStage_mono hav)
            ((F.tower.history (ind n)).toHistory.activeStage_mono (hvs.trans (hst n))))
          (tr.point ((F.tower.history (ind n)).toHistory.activeStage v) le_rfl
            ((F.tower.history (ind n)).toHistory.activeStage_mono hvs)) <
          ENNReal.ofReal (A * r n)) :
    Pre841Data_C11K (fun n => (F.tower.history (ind n)).toHistory) s y R hR :=
  Pre841Data_C11K.ofTracedKappa N hκ hradii
    (tracedKappa_of_window_P6B hW ind t p r hlate htime hsmall hvol aSeed haT hclock seedTrace
      s hst y R hwin hdist)

/-- **`hKappaLocal` ⇒ `Pre841`**【单向；需前提 = S7 + 上一定理的全部数据前提】
（`hKappaLocal` = 全尺度形，公开条件前提、非由 `nr := 0` 推出；S7 把 envelope 形降成 late 形，
`localKappaWindow_of_late_P6B` 给 window 形）：对每个 `A > 0`，坏点序列上存在 `κ > 0` 与
`Pre841` 数据。方向只能是这一边（见文件头：`Pre841 ⇏ hKappaLocal`）。 -/
theorem pre841_of_localKappa_C11K {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ}
    (hacc : LargerBallAccuracySupply_C11S δ α)
    (hKappaLocal : LocalKappaSupply_P6B F δ α (fun _ => 0)) {A : ℝ} (hA : 0 < A)
    (ind : ℕ → ℕ)
    (N : Pre841NativeData_C11K (fun n => (F.tower.history (ind n)).toHistory))
    (t : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (p : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (t n)).Carrier) (r : ℕ → ℝ)
    (hlate : Tendsto (fun n => (t n : ℝ)) atTop atTop)
    (htime : ∀ n, 2 * r n ^ 2 < (t n : ℝ))
    (hsmall : ∀ n, hasSmallParabolicCurvature (F.tower.history (ind n)).toHistory (t n) (p n)
      (r n))
    (hvol : ∀ n, ENNReal.ofReal (A⁻¹ * r n ^ 3) ≤
      ballVolume ((F.tower.history (ind n)).toHistory.stageMetric
        ((F.tower.history (ind n)).toHistory.activeStage (t n)) (t n)) (p n) (r n))
    (aSeed : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (haT : ∀ n, aSeed n ≤ t n) (hclock : ∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2)
    (seedTrace : ∀ n, BackwardPointTrace (F.tower.history (ind n)).toHistory
      ((F.tower.history (ind n)).toHistory.activeStage (aSeed n))
      ((F.tower.history (ind n)).toHistory.activeStage (t n))
      ((F.tower.history (ind n)).toHistory.activeStage_mono (haT n)) (p n))
    (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (hst : ∀ n, s n ≤ t n)
    (y : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier) (R : ℕ → ℝ)
    (hR : ∀ n, 0 < R n)
    (hradii : Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (t n : ℝ) - r n ^ 2 / 2 ≤ (s n : ℝ) - T / R n)
    (hdist : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon) (hvs : v ≤ s n),
        (s n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage v)
        ((F.tower.history (ind n)).toHistory.activeStage (s n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono hvs) x,
      ∀ hav : aSeed n ≤ v,
        riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage v) v)
          ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage v)
            ((F.tower.history (ind n)).toHistory.activeStage_mono hav)
            ((F.tower.history (ind n)).toHistory.activeStage_mono (hvs.trans (hst n))))
          (tr.point ((F.tower.history (ind n)).toHistory.activeStage v) le_rfl
            ((F.tower.history (ind n)).toHistory.activeStage_mono hvs)) <
          ENNReal.ofReal (A * r n)) :
    ∃ κ : ℝ, 0 < κ ∧
      Nonempty (Pre841Data_C11K (fun n => (F.tower.history (ind n)).toHistory) s y R hR) := by
  obtain ⟨κ, hκ, hW⟩ := localKappaWindow_of_late_P6B
    (localKappaLateSupply_of_envelope_P6B hacc hKappaLocal) A hA
  exact ⟨κ, hκ, ⟨pre841Data_of_window_C11K hκ hW ind N t p r hlate htime hsmall hvol aSeed haT
    hclock seedTrace s hst y R hR hradii hwin hdist⟩⟩

/-- **consumer（G4）**：`hKappaLocal` ⇒ `Pre841` ⇒ 基点时刻的 `LocalKappaAt_P6B` 结论块
（`eventually_localKappa_base`）：整条链 `LocalKappaSupply_P6B → Pre841Data_C11K → κ` 闭合。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {δ : ℝ → ℝ} {α : ℝ → ℝ → ℝ}
    (hacc : LargerBallAccuracySupply_C11S δ α)
    (hKappaLocal : LocalKappaSupply_P6B F δ α (fun _ => 0)) {A : ℝ} (hA : 0 < A)
    (ind : ℕ → ℕ)
    (N : Pre841NativeData_C11K (fun n => (F.tower.history (ind n)).toHistory))
    (t : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (p : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (t n)).Carrier) (r : ℕ → ℝ)
    (hlate : Tendsto (fun n => (t n : ℝ)) atTop atTop)
    (htime : ∀ n, 2 * r n ^ 2 < (t n : ℝ))
    (hsmall : ∀ n, hasSmallParabolicCurvature (F.tower.history (ind n)).toHistory (t n) (p n)
      (r n))
    (hvol : ∀ n, ENNReal.ofReal (A⁻¹ * r n ^ 3) ≤
      ballVolume ((F.tower.history (ind n)).toHistory.stageMetric
        ((F.tower.history (ind n)).toHistory.activeStage (t n)) (t n)) (p n) (r n))
    (aSeed : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (haT : ∀ n, aSeed n ≤ t n) (hclock : ∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2)
    (seedTrace : ∀ n, BackwardPointTrace (F.tower.history (ind n)).toHistory
      ((F.tower.history (ind n)).toHistory.activeStage (aSeed n))
      ((F.tower.history (ind n)).toHistory.activeStage (t n))
      ((F.tower.history (ind n)).toHistory.activeStage_mono (haT n)) (p n))
    (s : ∀ n, Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon)
    (hst : ∀ n, s n ≤ t n)
    (y : ∀ n, ((F.tower.history (ind n)).toHistory.stageAt (s n)).Carrier) (R : ℕ → ℝ)
    (hR : ∀ n, 0 < R n)
    (hradii : Tendsto (fun n => r n / 200 * Real.sqrt (R n)) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (t n : ℝ) - r n ^ 2 / 2 ≤ (s n : ℝ) - T / R n)
    (hdist : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (F.tower.history (ind n)).toHistory.horizon) (hvs : v ≤ s n),
        (s n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (F.tower.history (ind n)).toHistory
        ((F.tower.history (ind n)).toHistory.activeStage v)
        ((F.tower.history (ind n)).toHistory.activeStage (s n))
        ((F.tower.history (ind n)).toHistory.activeStage_mono hvs) x,
      ∀ hav : aSeed n ≤ v,
        riemannianEDistOf ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage v) v)
          ((seedTrace n).point ((F.tower.history (ind n)).toHistory.activeStage v)
            ((F.tower.history (ind n)).toHistory.activeStage_mono hav)
            ((F.tower.history (ind n)).toHistory.activeStage_mono (hvs.trans (hst n))))
          (tr.point ((F.tower.history (ind n)).toHistory.activeStage v) le_rfl
            ((F.tower.history (ind n)).toHistory.activeStage_mono hvs)) <
          ENNReal.ofReal (A * r n)) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((F.tower.history (ind n)).toHistory.stageMetric
          ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) (y n)
          (A / Real.sqrt (R n)),
      ∀ ρ' : ℝ, 0 < ρ' → ρ' ≤ 1 / Real.sqrt (R n) →
        (F.tower.history (ind n)).toHistory.isParabolicallyRmControlledBall (s n) x ρ' →
        ENNReal.ofReal (κ * ρ' ^ 3) ≤
          ballVolume ((F.tower.history (ind n)).toHistory.stageMetric
            ((F.tower.history (ind n)).toHistory.activeStage (s n)) (s n)) x ρ' := by
  obtain ⟨-, -, ⟨d⟩⟩ := pre841_of_localKappa_C11K hacc hKappaLocal hA ind N t p r hlate htime hsmall
    hvol aSeed haT hclock seedTrace s hst y R hR hradii hwin hdist
  exact ⟨d.kappa, d.kappa_pos, d.eventually_localKappa_base A⟩

end GC.LongTime.Ch11
