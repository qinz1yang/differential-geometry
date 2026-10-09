import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6FirstExitFinalP6M6

/-!
# `HU_final` / `hscalW_final`：U / Anchor₀ 合同的 final-slab 版本登记（S-CH11-HSCALU2 G1，后缀 `_P6M6`）

R-C11-8 D-12 / HCLOSEF `hcloseF⁺` 的 `hclosGF`（final slab seed closure）。与 `P6HscalUContractP6M5`
（`HU_P6M5`，event slab 版）**并列**登记，**不由 event 版推出**：final slab 上 `j` 换成 `Fin.last`，
窗口 `v ∈ (time last, horizon)`、`s ∈ (time last, v]`；U 端条件标量界需要 final slab 内的 SLT /
`HasSpatialCanonicalTimeControl`，与 event slab 版是不同 slab 的独立 analytic obligation（D-3 / D-12 口径）。

* `ObservedHistory.ExitGuardFinal_P6M6`：`ExitGuard_P6M5` 的 final 版（stage `Fin.last` 的度量
  `stageMetric (Fin.last _) s`，单个时刻 `s` 的 seed-Good）。
* `ObservedHistory.HU_final_P6M6 … B`：**显式合同 Prop**（lead 授权），`HU_P6M5` 逐项换 final slab；本文件不证它。
* `hscalUF_of_HU_final_P6M6`：`(∀ B, HU_final B)` ⇒ final 版 `hscalU` 形（把 `B` 的量词挪到 `Rad` 之前）。
* **`hclosGF_of_HU_final_P6M6`**：`(∀ B, HU_final B)` + K0 种子 / pinching / 时钟数据 ⇒ HCLOSEF
  `hcloseF_plus_P6HF` 的 **`hclosGF` binder 逐字**（走 `seed_closure_firstExit_final_P6M6`）。
  `hclosGF_of_firstExit_final_P6M6` 是同一结论以 `hscalUF` 为前提的形（`hclosG_of_firstExit_P6M4` 的 final 孪生）。
* `HU_final_P6M6.mono` / `.scalar_le_at_top`：深度单调；`s = v` 顶切片已含 `R(v, x) ≤ C q_w` ⇒ 不是小叶子。
* `ObservedHistory.hscalW_final_P6M6`：Anchor₀（`hscalW`，HDISTW）的 final 版——`σ` 落在 final slab
  （`activeStage σ = last`）时的开窗单时刻 ExitGuard 标量界；与 event 版 `hscalW`（`hdistW_of_firstExit_P6DW`
  的 `hσev` 情形）并列，不由其推出。`hscalW_of_hscalW_final_P6M6`：在 `hσfin` 下展开成 `hscalW` binder 文本。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **ExitGuard（final slab，`_P6M6`）**：`x` 在时刻 `s`（final stage 度量 `g_last(s)`）仍 seed-Good：
`d_s(O_last, x) ≤ d_σ(O_σ, y) + L/√R`。只在单个时刻 `s` 要求。 -/
def ObservedHistory.ExitGuardFinal_P6M6 (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ)
    (n : ℕ) (h1 : (Kh n).activeStage (aSeed n) ≤ Fin.last (Kh n).eventCount)
    (h2 : Fin.last (Kh n).eventCount ≤ (Kh n).activeStage (Tn n)) (s : ℝ)
    (x : ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier) : Prop :=
  riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) s)
      ((seedTrace n).point (Fin.last (Kh n).eventCount) h1 h2) x ≤
    riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
        ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
          ((Kh n).activeStage_mono (hsT n))) (y n) +
      ENNReal.ofReal (L n / Real.sqrt (R n))

/-- **`HU_final_P6M6 B`：`hscalU` 的 final slab long-depth admission（D-12，`_P6M6`）**。**独立 analytic
obligation**，本文件不证它，也不由 `HU_P6M5` 推出。`q_w := R_last(v, w)`
（`= metricScalarAt (stageMetric last v) w`）；窗口 `s ∈ [v − B/q_w, v] ∩ (time last, horizon)`；
`C_U` 在 `n, v, w, x, s` 之前。 -/
def ObservedHistory.HU_final_P6M6 (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (B : ℝ) : Prop :=
  ∀ Rad σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
    ∀ (v : ℝ), (Kh n).time (Fin.last (Kh n).eventCount) < v →
      v < (Kh n).horizon → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
    ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
        (Dw / Real.sqrt (R n)),
    ∀ (hjσ : Fin.last (Kh n).eventCount ≤ (Kh n).activeStage (σ n))
      (tr : BackwardPointTrace (Kh n) (Fin.last (Kh n).eventCount) ((Kh n).activeStage (σ n))
        hjσ x₁),
    ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ Fin.last (Kh n).eventCount)
      (h2 : Fin.last (Kh n).eventCount ≤ (Kh n).activeStage (Tn n))
      (w : ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier),
      riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
          ((seedTrace n).point (Fin.last (Kh n).eventCount) h1 h2) w ≤
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
              ((Kh n).activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
      riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
          (tr.point (Fin.last (Kh n).eventCount) le_rfl hjσ) w <
        ENNReal.ofReal (Dd / Real.sqrt (R n)) →
      R n ≤ metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w →
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w
          (Rad / Real.sqrt (metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w)),
      ∀ s : ℝ, v - B / metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w ≤ s →
        s ≤ v → (Kh n).time (Fin.last (Kh n).eventCount) < s →
        ObservedHistory.ExitGuardFinal_P6M6 Kh Tn aSeed σ haT hsT has pT seedTrace y R L n h1 h2
          s x →
        ∀ z : ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier,
          riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) s) x z <
              ENNReal.ofReal
                (1 / Real.sqrt
                  (C * metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w)) →
            metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) s) z ≤
              C * metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w

/-- **`hscalUF_of_HU_final_P6M6`**：`(∀ B, HU_final_P6M6 … B)` ⇒ `hclosGF_of_firstExit_final_P6M6`
的 `hscalUF` binder 逐字（把 `ExitGuardFinal_P6M6` 展开、把 `B` 的量词挪到 `Rad` 之前）。 -/
theorem ObservedHistory.hscalUF_of_HU_final_P6M6 (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ)
    (hU : ∀ B : ℝ, ObservedHistory.HU_final_P6M6 Kh Tn aSeed σ haT hsT has pT seedTrace y R L B) :
    ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
      ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
      ∀ (v : ℝ), (Kh n).time (Fin.last (Kh n).eventCount) < v →
        v < (Kh n).horizon → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : Fin.last (Kh n).eventCount ≤ (Kh n).activeStage (σ n))
        (tr : BackwardPointTrace (Kh n) (Fin.last (Kh n).eventCount) ((Kh n).activeStage (σ n))
          hjσ x₁),
      ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ Fin.last (Kh n).eventCount)
        (h2 : Fin.last (Kh n).eventCount ≤ (Kh n).activeStage (Tn n))
        (w : ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier),
        riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
            ((seedTrace n).point (Fin.last (Kh n).eventCount) h1 h2) w ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
            (tr.point (Fin.last (Kh n).eventCount) le_rfl hjσ) w <
          ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w →
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w
            (Rad / Real.sqrt
              (metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w)),
        ∀ s : ℝ,
          v - B / metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w ≤ s →
          s ≤ v → (Kh n).time (Fin.last (Kh n).eventCount) < s →
          riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) s)
              ((seedTrace n).point (Fin.last (Kh n).eventCount) h1 h2) x ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)) →
          ∀ z : ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier,
            riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) s) x z <
                ENNReal.ofReal
                  (1 / Real.sqrt
                    (C * metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w)) →
              metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) s) z ≤
                C * metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w :=
  fun Rad B σ₁ σ₂ h12 hσ₂ Dw Dd hDw hDd => hU B Rad σ₁ σ₂ h12 hσ₂ Dw Dd hDw hDd

/-- **DF-1 final `hclosGF` ⇐ 首出时刻（`_P6M6`）**：`hclosG_of_firstExit_P6M4` 的 final slab 孪生。结论逐字 =
HCLOSEF `hcloseF_plus_P6HF` 的 `hclosGF` binder；唯一残余 = U 端条件标量界 `hscalUF`（深度 `B/Q`、
条件于 seed-Good；`HU_final_P6M6` 的展开形）。证明 = `seed_closure_firstExit_final_P6M6` 逐 history。 -/
theorem ObservedHistory.hclosGF_of_firstExit_final_P6M6 (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (r : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hlate : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, 1 ≤ R n * ((σ n : ℝ) - T / R n))
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (a₀ + τ') x)
    (hscalUF : ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
      ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
      ∀ (v : ℝ), (Kh n).time (Fin.last (Kh n).eventCount) < v →
        v < (Kh n).horizon → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : Fin.last (Kh n).eventCount ≤ (Kh n).activeStage (σ n))
        (tr : BackwardPointTrace (Kh n) (Fin.last (Kh n).eventCount) ((Kh n).activeStage (σ n))
          hjσ x₁),
      ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ Fin.last (Kh n).eventCount)
        (h2 : Fin.last (Kh n).eventCount ≤ (Kh n).activeStage (Tn n))
        (w : ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier),
        riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
            ((seedTrace n).point (Fin.last (Kh n).eventCount) h1 h2) w ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
            (tr.point (Fin.last (Kh n).eventCount) le_rfl hjσ) w <
          ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w →
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w
            (Rad / Real.sqrt
              (metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w)),
        ∀ s : ℝ,
          v - B / metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w ≤ s →
          s ≤ v → (Kh n).time (Fin.last (Kh n).eventCount) < s →
          riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) s)
              ((seedTrace n).point (Fin.last (Kh n).eventCount) h1 h2) x ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)) →
          ∀ z : ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier,
            riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) s) x z <
                ENNReal.ofReal
                  (1 / Real.sqrt
                    (C * metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w)) →
              metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) s) z ≤
                C * metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w) :
    ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
      ∀ᶠ n in atTop,
      ∀ (v : ℝ), (Kh n).time (Fin.last (Kh n).eventCount) < v →
        v < (Kh n).horizon → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : Fin.last (Kh n).eventCount ≤ (Kh n).activeStage (σ n))
        (tr : BackwardPointTrace (Kh n) (Fin.last (Kh n).eventCount) ((Kh n).activeStage (σ n))
          hjσ x₁),
      ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ Fin.last (Kh n).eventCount)
        (h2 : Fin.last (Kh n).eventCount ≤ (Kh n).activeStage (Tn n))
        (w : ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier),
        riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
            ((seedTrace n).point (Fin.last (Kh n).eventCount) h1 h2) w ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
            (tr.point (Fin.last (Kh n).eventCount) le_rfl hjσ) w <
          ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w →
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w
            (Rad / Real.sqrt
              (metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w)),
        ∀ τ : ℝ,
          v - B / metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w ≤ τ →
          τ ≤ v → (Kh n).time (Fin.last (Kh n).eventCount) < τ →
          riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) τ)
              ((seedTrace n).point (Fin.last (Kh n).eventCount) h1 h2) x ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)) := by
  intro Rad B σ₁ σ₂ h12 hσ₂ Dw Dd hDw hDd
  obtain ⟨C, hC, hev⟩ := hscalUF Rad B σ₁ σ₂ h12 hσ₂ Dw Dd hDw hDd
  have hθ : 0 < max B 0 - σ₁ + 1 := by
    have := le_max_right B 0
    linarith
  filter_upwards [hev, hwin _ hθ, hlate _ hθ,
    hL.eventually_ge_atTop (2 * max Rad 0 +
      16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) * max B 0),
    hRr.eventually_ge_atTop
      (2500 * max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4))))]
    with n hn hwn hln hLn hrn
  intro v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w hwseed hwnear hRw x hx τ hτ hτv hτ1
  have hRn := hR n
  have hQ : 0 < metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w :=
    hRn.trans_le hRw
  have hB : B / metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w ≤
      max B 0 / R n :=
    (div_le_div_of_nonneg_right (le_max_left _ _) hQ.le).trans
      (div_le_div_of_nonneg_left (le_max_right _ _) hRn hRw)
  have e1 : (max B 0 - σ₁ + 1) / R n = max B 0 / R n - σ₁ / R n + 1 / R n := by ring
  have hR1 : 0 < 1 / R n := by positivity
  have hθR : (σ n : ℝ) - (max B 0 - σ₁ + 1) / R n ≤ τ := by linarith
  have hpos : 0 < (σ n : ℝ) - (max B 0 - σ₁ + 1) / R n := by
    by_contra hneg
    have hle := not_lt.mp hneg
    nlinarith
  have hτ0 : 0 ≤ τ := by linarith
  have hQτ : 1 ≤ metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w * τ :=
    calc (1 : ℝ) ≤ R n * ((σ n : ℝ) - (max B 0 - σ₁ + 1) / R n) := hln
      _ ≤ R n * τ := mul_le_mul_of_nonneg_left hθR hRn.le
      _ ≤ metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w * τ :=
        mul_le_mul_of_nonneg_right hRw hτ0
  have haτ : (aSeed n : ℝ) ≤ τ := hwn.trans hθR
  have hσT : (σ n : ℝ) ≤ Tn n := hsT n
  have hvT : v ≤ (Tn n : ℝ) := by
    have : σ₂ / R n < 0 := div_neg_of_neg_of_pos hσ₂ hRn
    linarith
  by_cases htop : riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
      ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
        ((Kh n).activeStage_mono (hsT n))) (y n) = ⊤
  · rw [htop, top_add]
    exact le_top
  exact (Kh n).seed_closure_firstExit_final_P6M6 (haT n) (hsmall n) (hclock n) (seedTrace n) ha₀
    (hpin n) h1 h2 w x (ENNReal.ofReal_toReal htop).symm ENNReal.toReal_nonneg hRn hRw hC
    hrn hLn hwseed hx hτ hτv hτ1 hv2 haτ hvT hQτ
    (hn v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w hwseed hwnear hRw x hx)

/-- **`hclosGF_of_HU_final_P6M6`**：`(∀ B, HU_final_P6M6 … B)` + K0 种子 / 时钟 / Hamilton–Ivey pinching
⇒ HCLOSEF `hcloseF_plus_P6HF` 的 `hclosGF` binder 逐字。`HU_final_P6M6` 与 `HU_P6M5` 并列、互不推出（D-12）。 -/
theorem ObservedHistory.hclosGF_of_HU_final_P6M6 (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (r : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hlate : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, 1 ≤ R n * ((σ n : ℝ) - T / R n))
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (a₀ + τ') x)
    (hU : ∀ B : ℝ, ObservedHistory.HU_final_P6M6 Kh Tn aSeed σ haT hsT has pT seedTrace y R L B) :
    ∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
      ∀ᶠ n in atTop,
      ∀ (v : ℝ), (Kh n).time (Fin.last (Kh n).eventCount) < v →
        v < (Kh n).horizon → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : Fin.last (Kh n).eventCount ≤ (Kh n).activeStage (σ n))
        (tr : BackwardPointTrace (Kh n) (Fin.last (Kh n).eventCount) ((Kh n).activeStage (σ n))
          hjσ x₁),
      ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ Fin.last (Kh n).eventCount)
        (h2 : Fin.last (Kh n).eventCount ≤ (Kh n).activeStage (Tn n))
        (w : ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier),
        riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
            ((seedTrace n).point (Fin.last (Kh n).eventCount) h1 h2) w ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
            (tr.point (Fin.last (Kh n).eventCount) le_rfl hjσ) w <
          ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w →
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w
            (Rad / Real.sqrt
              (metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w)),
        ∀ τ : ℝ,
          v - B / metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w ≤ τ →
          τ ≤ v → (Kh n).time (Fin.last (Kh n).eventCount) < τ →
          riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) τ)
              ((seedTrace n).point (Fin.last (Kh n).eventCount) h1 h2) x ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n)) :=
  ObservedHistory.hclosGF_of_firstExit_final_P6M6 Kh Tn aSeed σ haT hsT has pT seedTrace y R L hR r
    hL hsmall hclock hRr hwin hlate ha₀ hpin
    (ObservedHistory.hscalUF_of_HU_final_P6M6 Kh Tn aSeed σ haT hsT has pT seedTrace y R L hU)

/-- **深度单调（`_P6M6`）**：`B ≤ B'` 时 `HU_final_P6M6 … B'` ⇒ `HU_final_P6M6 … B`（窗口 `[v − B/q_w, v]`
变小，同一 `C_U`）。需要 `0 < R n`（`q_w ≥ R n > 0`）。 -/
theorem ObservedHistory.HU_final_P6M6.mono (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    {B B' : ℝ} (hBB : B ≤ B')
    (h : ObservedHistory.HU_final_P6M6 Kh Tn aSeed σ haT hsT has pT seedTrace y R L B') :
    ObservedHistory.HU_final_P6M6 Kh Tn aSeed σ haT hsT has pT seedTrace y R L B := by
  intro Rad σ₁ σ₂ h12 hσ₂ Dw Dd hDw hDd
  obtain ⟨C, hC, hev⟩ := h Rad σ₁ σ₂ h12 hσ₂ Dw Dd hDw hDd
  refine ⟨C, hC, hev.mono ?_⟩
  intro n hn v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w hwseed hwnear hRw x hx s hs1 hsv hs3
    hg z hz
  have hQ : 0 < metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w :=
    (hR n).trans_le hRw
  have hle : v - B' / metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w ≤
      v - B / metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w :=
    sub_le_sub_left (div_le_div_of_nonneg_right hBB hQ.le) v
  exact hn v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w hwseed hwnear hRw x hx s
    (hle.trans hs1) hsv hs3 hg z hz

/-- **`s = v, z = x` 已含 `R_last(v, x) ≤ C_U q_w`（`_P6M6`）**：`B ≥ 0` 的 `HU_final_P6M6 … B` 在顶切片
`s = v` 给出 `∀ x ∈ B_{g_last(v)}(w, Rad/√q_w)`，`R(v, x) ≤ C_U q_w`。`ExitGuardFinal(v, x)` 在 `s = v`
自动成立（三角不等式 + `L ≥ 2 max Rad 0`）。故 `HU_final_P6M6` **不是**比 final slab SLT 明显更轻的小叶子。 -/
theorem ObservedHistory.HU_final_P6M6.scalar_le_at_top (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hL : Tendsto L atTop atTop) {B : ℝ} (hB : 0 ≤ B)
    (h : ObservedHistory.HU_final_P6M6 Kh Tn aSeed σ haT hsT has pT seedTrace y R L B)
    (Rad σ₁ σ₂ : ℝ) (h12 : σ₁ ≤ σ₂) (hσ₂ : σ₂ < 0) (Dw Dd : ℝ) (hDw : 0 < Dw) (hDd : 0 < Dd) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
      ∀ (v : ℝ), (Kh n).time (Fin.last (Kh n).eventCount) < v →
        v < (Kh n).horizon → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : Fin.last (Kh n).eventCount ≤ (Kh n).activeStage (σ n))
        (tr : BackwardPointTrace (Kh n) (Fin.last (Kh n).eventCount) ((Kh n).activeStage (σ n))
          hjσ x₁),
      ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ Fin.last (Kh n).eventCount)
        (h2 : Fin.last (Kh n).eventCount ≤ (Kh n).activeStage (Tn n))
        (w : ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier),
        riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
            ((seedTrace n).point (Fin.last (Kh n).eventCount) h1 h2) w ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
            (tr.point (Fin.last (Kh n).eventCount) le_rfl hjσ) w <
          ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w →
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w
            (Rad / Real.sqrt
              (metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w)),
          metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) x ≤
            C * metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w := by
  obtain ⟨C, hC, hev⟩ := h Rad σ₁ σ₂ h12 hσ₂ Dw Dd hDw hDd
  refine ⟨C, hC, ?_⟩
  filter_upwards [hev, hL.eventually_ge_atTop (2 * max Rad 0)] with n hn hLn
  intro v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w hwseed hwnear hRw x hx
  have hRn := hR n
  have hQ : 0 < metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w :=
    hRn.trans_le hRw
  have hsqR : 0 < Real.sqrt (R n) := Real.sqrt_pos.mpr hRn
  have hsq : Real.sqrt (R n) ≤
      Real.sqrt (metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w) :=
    Real.sqrt_le_sqrt hRw
  have hRad : Rad / Real.sqrt
        (metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w) ≤
      L n / 2 / Real.sqrt (R n) :=
    calc Rad / Real.sqrt (metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w)
        ≤ max Rad 0 /
            Real.sqrt (metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w) :=
          div_le_div_of_nonneg_right (le_max_left _ _) (Real.sqrt_nonneg _)
      _ ≤ max Rad 0 / Real.sqrt (R n) :=
          div_le_div_of_nonneg_left (le_max_right _ _) hsqR hsq
      _ ≤ L n / 2 / Real.sqrt (R n) :=
          div_le_div_of_nonneg_right (by linarith) hsqR.le
  have hL0 : 0 ≤ L n / 2 / Real.sqrt (R n) := by
    have := le_max_right Rad 0
    have : 0 ≤ L n := by linarith
    positivity
  have hguard : ObservedHistory.ExitGuardFinal_P6M6 Kh Tn aSeed σ haT hsT has pT seedTrace y R L n
      h1 h2 v x := by
    unfold ObservedHistory.ExitGuardFinal_P6M6
    calc riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
          ((seedTrace n).point (Fin.last (Kh n).eventCount) h1 h2) x
        ≤ riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
            ((seedTrace n).point (Fin.last (Kh n).eventCount) h1 h2) w +
          riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w x :=
          riemannianEDistOf_triangle _ _ _ _
      _ ≤ (riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n))) +
          ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) :=
          add_le_add hwseed (hx.le.trans (ENNReal.ofReal_le_ofReal hRad))
      _ = riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) := by
          rw [add_assoc, ← ENNReal.ofReal_add hL0 hL0]
          congr 2
          ring
  have hBQ : 0 ≤ B / metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w :=
    div_nonneg hB hQ.le
  have hCQ : 0 < C * metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w :=
    mul_pos (lt_of_lt_of_le one_pos hC) hQ
  have hxx : riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) x x <
      ENNReal.ofReal (1 / Real.sqrt
        (C * metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w)) := by
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (one_div_pos.mpr (Real.sqrt_pos.mpr hCQ))
  exact hn v hv1 hv2 hvσ1 hvσ2 x₁ hx₁ hjσ tr h1 h2 w hwseed hwnear hRw x hx v
    (by linarith) le_rfl hv1 hguard x hxx

/-- **`hscalW_final_P6M6`（Anchor₀ 的 final 版，`_P6M6`）**：`σ` 落在 final slab（`activeStage σ = last`）时，
基点窗口的开窗单时刻 ExitGuard 标量界——`hdistW_of_firstExit_P6DW` 的 `hscalW`（event 版，`hσev` 情形）的
并列义务，**不由 event 版推出**（`time last < s < σ`，度量 `stageMetric last s`）。`σ` 在 final slab 的情形
`hdistW` 的 final 孪生（`distW_transport` 的 final 版）见 DELIVERIES 块的 repair target。独立 analytic
obligation，本文件不证它（`s → σ⁻` 的极限含 SLT anchor 的 σ 时刻结论 ⇒ 不是小叶子）。 -/
def ObservedHistory.hscalW_final_P6M6 (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) : Prop :=
  ∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
    (Kh n).activeStage (σ n) = Fin.last (Kh n).eventCount →
    ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
        (D / Real.sqrt (R n)),
    ∀ s : ℝ, (σ n : ℝ) - T / R n < s → s < σ n →
      (Kh n).time (Fin.last (Kh n).eventCount) < s →
      riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s)
          ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
            ((Kh n).activeStage_mono (hsT n))) x ≤
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
            ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
              ((Kh n).activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / Real.sqrt (R n)) →
      ∀ z : ((Kh n).stageAt (σ n)).Carrier,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) x z <
            ENNReal.ofReal (1 / Real.sqrt (C * R n)) →
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) z ≤ C * R n

/-- **`hscalW_of_hscalW_final_P6M6`**：`σ` 全在 final slab（`hσfin`）时，`hscalW_final_P6M6` 展开成
`hdistW_of_firstExit_P6DW` 的 `hscalW` binder 文本（`time (activeStage σ) < s` 由 `hσfin` 改写）。 -/
theorem ObservedHistory.hscalW_of_hscalW_final_P6M6 (Kh : ℕ → ObservedHistory.{u})
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ)
    (hσfin : ∀ n, (Kh n).activeStage (σ n) = Fin.last (Kh n).eventCount)
    (h : ObservedHistory.hscalW_final_P6M6 Kh Tn aSeed σ haT hsT has pT seedTrace y R L) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ s : ℝ, (σ n : ℝ) - T / R n < s → s < σ n → (Kh n).time ((Kh n).activeStage (σ n)) < s →
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s)
            ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
              ((Kh n).activeStage_mono (hsT n))) x ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        ∀ z : ((Kh n).stageAt (σ n)).Carrier,
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) x z <
              ENNReal.ofReal (1 / Real.sqrt (C * R n)) →
            metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) s) z ≤ C * R n := by
  intro D T hD hT
  obtain ⟨C, hC, hev⟩ := h D T hD hT
  refine ⟨C, hC, hev.mono ?_⟩
  intro n hn x hx s hs1 hs2 hs3 hg z hz
  have hs3' : (Kh n).time (Fin.last (Kh n).eventCount) < s := by
    rw [← hσfin n]
    exact hs3
  exact hn (hσfin n) x hx s hs1 hs2 hs3' hg z hz

/-- **consumer（`_P6M6`）**：`hU : ∀ B, HU_final_P6M6 … B` 同时喂 `hclosGF_of_HU_final_P6M6`
（final seed closure）与 `scalar_le_at_top`（`B = 0` 顶切片 `R(v, x) ≤ C_U q_w`）。 -/
example (Kh : ℕ → ObservedHistory.{u}) (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (r : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hlate : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, 1 ≤ R n * ((σ n : ℝ) - T / R n))
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (a₀ + τ') x)
    (hU : ∀ B : ℝ, ObservedHistory.HU_final_P6M6 Kh Tn aSeed σ haT hsT has pT seedTrace y R L B) :
    (∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
      ∀ᶠ n in atTop,
      ∀ (v : ℝ), (Kh n).time (Fin.last (Kh n).eventCount) < v →
        v < (Kh n).horizon → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : Fin.last (Kh n).eventCount ≤ (Kh n).activeStage (σ n))
        (tr : BackwardPointTrace (Kh n) (Fin.last (Kh n).eventCount) ((Kh n).activeStage (σ n))
          hjσ x₁),
      ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ Fin.last (Kh n).eventCount)
        (h2 : Fin.last (Kh n).eventCount ≤ (Kh n).activeStage (Tn n))
        (w : ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier),
        riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
            ((seedTrace n).point (Fin.last (Kh n).eventCount) h1 h2) w ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
            (tr.point (Fin.last (Kh n).eventCount) le_rfl hjσ) w <
          ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w →
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w
            (Rad / Real.sqrt
              (metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w)),
        ∀ τ : ℝ,
          v - B / metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w ≤ τ →
          τ ≤ v → (Kh n).time (Fin.last (Kh n).eventCount) < τ →
          riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) τ)
              ((seedTrace n).point (Fin.last (Kh n).eventCount) h1 h2) x ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / Real.sqrt (R n))) ∧
    (∀ Rad σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
      ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
      ∀ (v : ℝ), (Kh n).time (Fin.last (Kh n).eventCount) < v →
        v < (Kh n).horizon → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
      ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (Dw / Real.sqrt (R n)),
      ∀ (hjσ : Fin.last (Kh n).eventCount ≤ (Kh n).activeStage (σ n))
        (tr : BackwardPointTrace (Kh n) (Fin.last (Kh n).eventCount) ((Kh n).activeStage (σ n))
          hjσ x₁),
      ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ Fin.last (Kh n).eventCount)
        (h2 : Fin.last (Kh n).eventCount ≤ (Kh n).activeStage (Tn n))
        (w : ((Kh n).stage (Fin.last (Kh n).eventCount)).Carrier),
        riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
            ((seedTrace n).point (Fin.last (Kh n).eventCount) h1 h2) w ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
        riemannianEDistOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v)
            (tr.point (Fin.last (Kh n).eventCount) le_rfl hjσ) w <
          ENNReal.ofReal (Dd / Real.sqrt (R n)) →
        R n ≤ metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w →
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w
            (Rad / Real.sqrt
              (metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w)),
          metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) x ≤
            C * metricScalarAt ((Kh n).stageMetric (Fin.last (Kh n).eventCount) v) w) :=
  ⟨ObservedHistory.hclosGF_of_HU_final_P6M6 Kh Tn aSeed σ haT hsT has pT seedTrace y R L hR r hL
      hsmall hclock hRr hwin hlate ha₀ hpin hU,
    fun Rad σ₁ σ₂ h12 hσ₂ Dw Dd hDw hDd =>
      ObservedHistory.HU_final_P6M6.scalar_le_at_top Kh Tn aSeed σ haT hsT has pT seedTrace y R L hR
        hL le_rfl (hU 0) Rad σ₁ σ₂ h12 hσ₂ Dw Dd hDw hDd⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
