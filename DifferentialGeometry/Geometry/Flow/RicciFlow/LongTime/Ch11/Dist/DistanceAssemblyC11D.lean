import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.SurgeryNoShortcutC11D

/-!
# P6 距离线 G4：(D1) 装配 + consumers（O-CH11-DIST，后缀 `_C11D`）

把 G2（(D3)，`hsmooth_of_rmNorm_le_C11D`）与 G3（(D4)，`hevent_of_records_C11D`）在序列层按尺度
`ℓ_n = ℓ/√R_n`、`|Rm| ≤ K R_n` 装配，喂 G1 的三个出口：

* `rate_scaled_eq_C11D`：`8/(ℓ/√R) = (8/ℓ)√R`（速率 `Λ_n = c√R_n`，`c = 8/ℓ`）。
* **`hrate_of_endpoint_bounds_C11D`**：G1 `hD1_of_stage_bounds_C11D` 的 `hrate`，由
  `hgeom`（对每个 `D, T`：`∃ ℓ K, Kℓ² ≤ 1`，eventually 末 stage 端点 `|Rm| ≤ K R_n`、event 段端点
  `Ric ≤ 3R_n/ℓ²`、端点保护）+ late records（`T₀ n ≤ s_n − T/R_n` eventually）给出。
* **`hD1_of_endpoint_bounds_C11D`（(D1) 装配）**：+ 中心界 ⇒ P6B2 `hdist_fixed_of_D1_P6B2` 的 `hD1`。
* **`hwit_of_selection_C11D`**：P6D2 `false_of_not_good_extendAt_P6D2` 的 `hwit`（`qs n = 4 R_n`、
  `C1s = C1'`、`C2s = C2'`），由 selection 末项 `hgood`（`L_n → ∞`）+ (D2) 窗口 `aSeed ≤ s − T/R` +
  G1 形 `hrate` 经 P6CON L9 给出——**相对形**链（不需中心界）。
* consumer（文件末 `example`）：`hD1_of_endpoint_bounds_C11D` → `hdist_fixed_of_D1_P6B2` →
  `tracedKappa_of_window_margin_P6B2`（P6B bridge，`A_* = A₀ + 1`）。

所有几何输入（端点 `|Rm|` / Ricci 界、端点保护、records、中心界、selection `hgood`）仍是显式前提：
D-7 种子端由 K0、另一端由严格内部曲率 + pinching（G2 `sqrt_rmNormSq_stage_le_of_pinched_C11D`）；
D-8 保护条件另证。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- 速率换尺度：`8/(ℓ/√R) = (8/ℓ)√R`。 -/
theorem rate_scaled_eq_C11D (ℓ R : ℝ) : 8 / (ℓ / Real.sqrt R) = 8 / ℓ * Real.sqrt R := by
  rw [div_div_eq_mul_div, mul_div_right_comm]

/-! ## 序列层 `hrate` -/

/-- **G1 `hrate` 的生产（`_C11D`）**：对每个 `D, T > 0` 有 `ℓ > 0`、`K`（`Kℓ² ≤ 1`），eventually：
(i) 末 stage 窗口内种子点与 `x ∈ B(y_n, D/√R_n)` 的 `ℓ/√R_n`-球上 `|Rm| ≤ K R_n`；(ii) 端点保护；
(iii) event 段端点 `ℓ/√R_n`-球 `Ric ≤ (3/(ℓ/√R_n)²) g`。加 late records（`T₀ n ≤ s_n − T/R_n`
eventually）⇒ G1 形 `hrate`（`c = 8/ℓ`）。 -/
theorem hrate_of_endpoint_bounds_C11D (Hs : ℕ → ObservedHistory.{u})
    (t : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (p : ∀ n, ((Hs n).stageAt (t n)).Carrier)
    (aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (haT : ∀ n, aSeed n ≤ t n)
    (seedTrace : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aSeed n))
      ((Hs n).activeStage (t n)) ((Hs n).activeStage_mono (haT n)) (p n))
    (s : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (hst : ∀ n, s n ≤ t n) (has : ∀ n, aSeed n ≤ s n)
    (y : ∀ n, ((Hs n).stageAt (s n)).Carrier) (R : ℕ → ℝ) (hR : ∀ᶠ n in atTop, 0 < R n)
    (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ)
    (records : ∀ n (e : Fin (Hs n).eventCount), T₀ n ≤ (Hs n).time e.succ →
      GeometricCutoffRecord (Hs n) e (q n))
    (hOld : ∀ n (e : Fin (Hs n).eventCount), T₀ n ≤ (Hs n).time e.succ →
      ((Hs n).event e).old = ((Hs n).event e).transition.trace.retainedCore)
    (hcan : ∀ n (e : Fin (Hs n).eventCount) (he : T₀ n ≤ (Hs n).time e.succ) b,
      ((records n e he).static b).hasCanonicalWindow)
    (hacc : ∀ n, (q n).modelAccuracy ≤ 1 / 2)
    (hDm : ∀ n, StandardCap.transitionEnd + 10 < (q n).modelRadius)
    (hT₀ : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀ n ≤ (s n : ℝ) - T / R n)
    (hgeom : ∀ D T : ℝ, 0 < D → 0 < T → ∃ ℓ K : ℝ, 0 < ℓ ∧ K * ℓ ^ 2 ≤ 1 ∧ ∀ᶠ n in atTop,
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ τ : ℝ, (s n : ℝ) - T / R n < τ → (Hs n).time ((Hs n).activeStage (s n)) < τ →
          τ < s n →
        ∀ z : ((Hs n).stageAt (s n)).Carrier,
          (riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ)
              ((seedTrace n).point ((Hs n).activeStage (s n))
                ((Hs n).activeStage_mono (has n)) ((Hs n).activeStage_mono (hst n))) z <
              ENNReal.ofReal (ℓ / Real.sqrt (R n)) ∨
            riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) x z <
              ENNReal.ofReal (ℓ / Real.sqrt (R n))) →
          Real.sqrt (normSq0S ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) z 4
            (metricRm04At ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) z)) ≤ K * R n) ∧
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aSeed n ≤ v) (hvs : v ≤ s n),
          (s n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
          ((Hs n).activeStage_mono hvs) x,
        ∀ (e : Fin (Hs n).eventCount) (h1 : (Hs n).activeStage (aSeed n) ≤ e.castSucc)
          (h2 : e.succ ≤ (Hs n).activeStage (t n)) (h3 : (Hs n).activeStage v ≤ e.castSucc)
          (h4 : e.succ ≤ (Hs n).activeStage (s n)), (v : ℝ) < (Hs n).time e.succ →
        ∀ (he : T₀ n ≤ (Hs n).time e.succ) b,
          (seedTrace n).point e.succ (h1.trans e.castSucc_lt_succ.le) h2 ∉
              ((records n e he).static b).window ''
                {z : standardCapWindow (q n).modelRadius |
                  ‖z.val‖ ≤ StandardCap.transitionEnd + 10} ∧
            tr.point e.succ (h3.trans e.castSucc_lt_succ.le) h4 ∉
              ((records n e he).static b).window ''
                {z : standardCapWindow (q n).modelRadius |
                  ‖z.val‖ ≤ StandardCap.transitionEnd + 10}) ∧
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aSeed n ≤ v) (hvs : v ≤ s n),
          (s n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
          ((Hs n).activeStage_mono hvs) x,
        ∀ (e : Fin (Hs n).eventCount) (h1 : (Hs n).activeStage (aSeed n) ≤ e.castSucc)
          (h2 : e.succ ≤ (Hs n).activeStage (t n)) (h3 : (Hs n).activeStage v ≤ e.castSucc)
          (h4 : e.succ ≤ (Hs n).activeStage (s n)) (t' : ℝ),
          (v : ℝ) < t' → (Hs n).time e.castSucc < t' → t' < (Hs n).time e.succ →
        ∀ z : ((Hs n).stage e.castSucc).Carrier, ∀ ξ : TangentSpace ThreeModel z,
          (riemannianEDistOf ((Hs n).stageMetric e.castSucc t')
              ((seedTrace n).point e.castSucc h1 (e.castSucc_lt_succ.le.trans h2)) z <
              ENNReal.ofReal (ℓ / Real.sqrt (R n)) ∨
            riemannianEDistOf ((Hs n).stageMetric e.castSucc t')
              (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) z <
              ENNReal.ofReal (ℓ / Real.sqrt (R n))) →
          ricciTensor ((Hs n).stageMetric e.castSucc t') z ξ ξ ≤
            (3 / (ℓ / Real.sqrt (R n)) ^ 2) *
              ((Hs n).stageMetric e.castSucc t').inner z ξ ξ)) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ n in atTop,
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ τ : ℝ, (s n : ℝ) - T / R n ≤ τ → (Hs n).time ((Hs n).activeStage (s n)) ≤ τ →
          τ ≤ s n →
        riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ)
            ((seedTrace n).point ((Hs n).activeStage (s n)) ((Hs n).activeStage_mono (has n))
              ((Hs n).activeStage_mono (hst n))) x ≤
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n))
              ((seedTrace n).point ((Hs n).activeStage (s n))
                ((Hs n).activeStage_mono (has n)) ((Hs n).activeStage_mono (hst n))) x +
            ENNReal.ofReal (c * Real.sqrt (R n) * ((s n : ℝ) - τ))) ∧
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aSeed n ≤ v) (hvs : v ≤ s n),
          (s n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
          ((Hs n).activeStage_mono hvs) x,
        ∀ (e : Fin (Hs n).eventCount) (h1 : (Hs n).activeStage (aSeed n) ≤ e.castSucc)
          (h2 : e.succ ≤ (Hs n).activeStage (t n)) (h3 : (Hs n).activeStage v ≤ e.castSucc)
          (h4 : e.succ ≤ (Hs n).activeStage (s n)) (τ : ℝ),
          (v : ℝ) ≤ τ → (Hs n).time e.castSucc ≤ τ → τ < (Hs n).time e.succ →
        riemannianEDistOf ((Hs n).stageMetric e.castSucc τ)
            ((seedTrace n).point e.castSucc h1 (e.castSucc_lt_succ.le.trans h2))
            (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) ≤
          riemannianEDistOf ((Hs n).stageMetric e.succ ((Hs n).time e.succ))
              ((seedTrace n).point e.succ (h1.trans e.castSucc_lt_succ.le) h2)
              (tr.point e.succ (h3.trans e.castSucc_lt_succ.le) h4) +
            ENNReal.ofReal (c * Real.sqrt (R n) * ((Hs n).time e.succ - τ))) := by
  intro D T hD hT
  obtain ⟨ℓ, K, hℓ, hKℓ, hev⟩ := hgeom D T hD hT
  refine ⟨8 / ℓ, div_nonneg (by norm_num) hℓ.le, ?_⟩
  filter_upwards [hev, hR, hT₀ T hT] with n hn hRn hT₀n
  obtain ⟨hRm, hprot, hRic⟩ := hn
  have hsq : 0 < Real.sqrt (R n) := Real.sqrt_pos.2 hRn
  have hℓn : 0 < ℓ / Real.sqrt (R n) := div_pos hℓ hsq
  have hKn : K * R n * (ℓ / Real.sqrt (R n)) ^ 2 ≤ 1 := by
    have h : K * R n * (ℓ / Real.sqrt (R n)) ^ 2 = K * ℓ ^ 2 := by
      rw [div_pow, Real.sq_sqrt hRn.le]
      field_simp
    rw [h]
    exact hKℓ
  refine ⟨fun x hx τ h1 h2 h3 => ?_, fun x hx v hav hvs hθv tr e h1 h2 h3 h4 τ hτ1 hτ2 hτ3 => ?_⟩
  · have h := (Hs n).hsmooth_of_rmNorm_le_C11D (haT n) (hst n) (has n) (seedTrace n) (y n) hℓn
      hKn hRm x hx τ h1 h2 h3
    rwa [rate_scaled_eq_C11D] at h
  · have h := (Hs n).hevent_of_records_C11D (haT n) (seedTrace n) (y n) hℓn hT₀n (records n)
      (hOld n) (hcan n) (hacc n) (hDm n) hprot hRic x hx v hav hvs hθv tr e h1 h2 h3 h4 τ hτ1
      hτ2 hτ3
    rwa [rate_scaled_eq_C11D] at h

/-! ## (D1) 装配（P6B2 `hD1`） -/

/-- **(D1) 装配（`_C11D`）**：`hrate_of_endpoint_bounds_C11D` + 中心界 `y_n ∈ B(O_n, A₀ r_n)` ⇒ P6B2
`hdist_fixed_of_D1_P6B2` 的 `hD1`：`d_v(O_v, x_v) < A₀ r_n + C_{D,T}/√R_n`。 -/
theorem hD1_of_endpoint_bounds_C11D (Hs : ℕ → ObservedHistory.{u}) {A₀ : ℝ}
    (t : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (p : ∀ n, ((Hs n).stageAt (t n)).Carrier)
    (r : ℕ → ℝ)
    (aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (haT : ∀ n, aSeed n ≤ t n)
    (seedTrace : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aSeed n))
      ((Hs n).activeStage (t n)) ((Hs n).activeStage_mono (haT n)) (p n))
    (s : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (hst : ∀ n, s n ≤ t n) (has : ∀ n, aSeed n ≤ s n)
    (y : ∀ n, ((Hs n).stageAt (s n)).Carrier) (R : ℕ → ℝ) (hR : ∀ᶠ n in atTop, 0 < R n)
    (hcenter : ∀ᶠ n in atTop, y n ∈ riemannianBallOf
      ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n))
      ((seedTrace n).point ((Hs n).activeStage (s n)) ((Hs n).activeStage_mono (has n))
        ((Hs n).activeStage_mono (hst n))) (A₀ * r n))
    (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ)
    (records : ∀ n (e : Fin (Hs n).eventCount), T₀ n ≤ (Hs n).time e.succ →
      GeometricCutoffRecord (Hs n) e (q n))
    (hOld : ∀ n (e : Fin (Hs n).eventCount), T₀ n ≤ (Hs n).time e.succ →
      ((Hs n).event e).old = ((Hs n).event e).transition.trace.retainedCore)
    (hcan : ∀ n (e : Fin (Hs n).eventCount) (he : T₀ n ≤ (Hs n).time e.succ) b,
      ((records n e he).static b).hasCanonicalWindow)
    (hacc : ∀ n, (q n).modelAccuracy ≤ 1 / 2)
    (hDm : ∀ n, StandardCap.transitionEnd + 10 < (q n).modelRadius)
    (hT₀ : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀ n ≤ (s n : ℝ) - T / R n)
    (hgeom : ∀ D T : ℝ, 0 < D → 0 < T → ∃ ℓ K : ℝ, 0 < ℓ ∧ K * ℓ ^ 2 ≤ 1 ∧ ∀ᶠ n in atTop,
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ τ : ℝ, (s n : ℝ) - T / R n < τ → (Hs n).time ((Hs n).activeStage (s n)) < τ →
          τ < s n →
        ∀ z : ((Hs n).stageAt (s n)).Carrier,
          (riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ)
              ((seedTrace n).point ((Hs n).activeStage (s n))
                ((Hs n).activeStage_mono (has n)) ((Hs n).activeStage_mono (hst n))) z <
              ENNReal.ofReal (ℓ / Real.sqrt (R n)) ∨
            riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) x z <
              ENNReal.ofReal (ℓ / Real.sqrt (R n))) →
          Real.sqrt (normSq0S ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) z 4
            (metricRm04At ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) z)) ≤ K * R n) ∧
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aSeed n ≤ v) (hvs : v ≤ s n),
          (s n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
          ((Hs n).activeStage_mono hvs) x,
        ∀ (e : Fin (Hs n).eventCount) (h1 : (Hs n).activeStage (aSeed n) ≤ e.castSucc)
          (h2 : e.succ ≤ (Hs n).activeStage (t n)) (h3 : (Hs n).activeStage v ≤ e.castSucc)
          (h4 : e.succ ≤ (Hs n).activeStage (s n)), (v : ℝ) < (Hs n).time e.succ →
        ∀ (he : T₀ n ≤ (Hs n).time e.succ) b,
          (seedTrace n).point e.succ (h1.trans e.castSucc_lt_succ.le) h2 ∉
              ((records n e he).static b).window ''
                {z : standardCapWindow (q n).modelRadius |
                  ‖z.val‖ ≤ StandardCap.transitionEnd + 10} ∧
            tr.point e.succ (h3.trans e.castSucc_lt_succ.le) h4 ∉
              ((records n e he).static b).window ''
                {z : standardCapWindow (q n).modelRadius |
                  ‖z.val‖ ≤ StandardCap.transitionEnd + 10}) ∧
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aSeed n ≤ v) (hvs : v ≤ s n),
          (s n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
          ((Hs n).activeStage_mono hvs) x,
        ∀ (e : Fin (Hs n).eventCount) (h1 : (Hs n).activeStage (aSeed n) ≤ e.castSucc)
          (h2 : e.succ ≤ (Hs n).activeStage (t n)) (h3 : (Hs n).activeStage v ≤ e.castSucc)
          (h4 : e.succ ≤ (Hs n).activeStage (s n)) (t' : ℝ),
          (v : ℝ) < t' → (Hs n).time e.castSucc < t' → t' < (Hs n).time e.succ →
        ∀ z : ((Hs n).stage e.castSucc).Carrier, ∀ ξ : TangentSpace ThreeModel z,
          (riemannianEDistOf ((Hs n).stageMetric e.castSucc t')
              ((seedTrace n).point e.castSucc h1 (e.castSucc_lt_succ.le.trans h2)) z <
              ENNReal.ofReal (ℓ / Real.sqrt (R n)) ∨
            riemannianEDistOf ((Hs n).stageMetric e.castSucc t')
              (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) z <
              ENNReal.ofReal (ℓ / Real.sqrt (R n))) →
          ricciTensor ((Hs n).stageMetric e.castSucc t') z ξ ξ ≤
            (3 / (ℓ / Real.sqrt (R n)) ^ 2) *
              ((Hs n).stageMetric e.castSucc t').inner z ξ ξ)) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∃ C : ℝ, ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvs : v ≤ s n), (s n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
        ((Hs n).activeStage_mono hvs) x,
      ∀ hav : aSeed n ≤ v,
        riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage v) v)
            ((seedTrace n).point ((Hs n).activeStage v) ((Hs n).activeStage_mono hav)
              ((Hs n).activeStage_mono (hvs.trans (hst n))))
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvs)) <
          ENNReal.ofReal (A₀ * r n + C / Real.sqrt (R n)) :=
  hD1_of_stage_bounds_C11D Hs t p r aSeed haT seedTrace s hst has y R hR hcenter
    (hrate_of_endpoint_bounds_C11D Hs t p aSeed haT seedTrace s hst has y R hR q T₀ records hOld
      hcan hacc hDm hT₀ hgeom)

/-! ## P6D2 `hwit`（相对形链 + P6CON L9） -/

/-- **P6D2 `hwit` 的生产（`_C11D`）**：selection 末项 `hgood`（每个 `n` 充分大；`Q = R_n`、`L_n → ∞`）
+ (D2) 窗口 `aSeed ≤ s − T/R` + G1 形 `hrate` ⇒ `false_of_not_good_extendAt_P6D2` 的 `hwit`
（`qs n = 4 R_n`、`ε = eps`、`C1s = C1'`、`C2s = C2'`）。证明：P6CON L9
`hasSpatialCanonicalTimeControl_on_window_traces_P6N`，其 `hdist` 取 G1 相对形
`hdist_rel_of_stage_bounds_C11D`（数值条件 `D + cT ≤ L_n` eventually），取 Good 的 witness 分量。 -/
theorem hwit_of_selection_C11D (Hs : ℕ → ObservedHistory.{u}) {eps C1' C2' : ℝ}
    {Ctime' : ℝ≥0}
    (t : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (p : ∀ n, ((Hs n).stageAt (t n)).Carrier)
    (aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (haT : ∀ n, aSeed n ≤ t n)
    (seedTrace : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aSeed n))
      ((Hs n).activeStage (t n)) ((Hs n).activeStage_mono (haT n)) (p n))
    (s : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (hst : ∀ n, s n ≤ t n) (has : ∀ n, aSeed n ≤ s n)
    (y : ∀ n, ((Hs n).stageAt (s n)).Carrier) (R L : ℕ → ℝ) (hR : ∀ᶠ n in atTop, 0 < R n)
    (hL : Tendsto L atTop atTop)
    (hgood : ∀ᶠ n in atTop, ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hav : aSeed n ≤ v)
      (hvs : v ≤ s n), (s n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((Hs n).stageAt v).Carrier,
        riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage v) v)
            ((seedTrace n).point ((Hs n).activeStage v) ((Hs n).activeStage_mono hav)
              ((Hs n).activeStage_mono (hvs.trans (hst n)))) z ≤
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n))
              ((seedTrace n).point ((Hs n).activeStage (s n)) ((Hs n).activeStage_mono (has n))
                ((Hs n).activeStage_mono (hst n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        4 * R n ≤ metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v) z →
        (Hs n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ (s n : ℝ) - T / R n)
    (hrate : ∀ D T : ℝ, 0 < D → 0 < T → ∃ c : ℝ, 0 ≤ c ∧ ∀ᶠ n in atTop,
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ τ : ℝ, (s n : ℝ) - T / R n ≤ τ → (Hs n).time ((Hs n).activeStage (s n)) ≤ τ →
          τ ≤ s n →
        riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ)
            ((seedTrace n).point ((Hs n).activeStage (s n)) ((Hs n).activeStage_mono (has n))
              ((Hs n).activeStage_mono (hst n))) x ≤
          riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n))
              ((seedTrace n).point ((Hs n).activeStage (s n))
                ((Hs n).activeStage_mono (has n)) ((Hs n).activeStage_mono (hst n))) x +
            ENNReal.ofReal (c * Real.sqrt (R n) * ((s n : ℝ) - τ))) ∧
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aSeed n ≤ v) (hvs : v ≤ s n),
          (s n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
          ((Hs n).activeStage_mono hvs) x,
        ∀ (e : Fin (Hs n).eventCount) (h1 : (Hs n).activeStage (aSeed n) ≤ e.castSucc)
          (h2 : e.succ ≤ (Hs n).activeStage (t n)) (h3 : (Hs n).activeStage v ≤ e.castSucc)
          (h4 : e.succ ≤ (Hs n).activeStage (s n)) (τ : ℝ),
          (v : ℝ) ≤ τ → (Hs n).time e.castSucc ≤ τ → τ < (Hs n).time e.succ →
        riemannianEDistOf ((Hs n).stageMetric e.castSucc τ)
            ((seedTrace n).point e.castSucc h1 (e.castSucc_lt_succ.le.trans h2))
            (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) ≤
          riemannianEDistOf ((Hs n).stageMetric e.succ ((Hs n).time e.succ))
              ((seedTrace n).point e.succ (h1.trans e.castSucc_lt_succ.le) h2)
              (tr.point e.succ (h3.trans e.castSucc_lt_succ.le) h4) +
            ENNReal.ofReal (c * Real.sqrt (R n) * ((Hs n).time e.succ - τ)))) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ s n), (s n : ℝ) - T / R n ≤ v →
      (v : ℝ) < s n → (Hs n).time ((Hs n).activeStage v) < v →
      ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
        ((Hs n).activeStage_mono hvt) x,
        4 * R n < metricScalarAt ((Hs n).stageMetric ((Hs n).activeStage v) v)
          (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) →
        ∃ Wt : SpatialCanonicalWitness ((Hs n).stageMetric ((Hs n).activeStage v) v) eps C1' C2'
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)),
          Wt.capTubeHasNeckChart eps := by
  intro D T hD hT
  obtain ⟨c, hc, hev⟩ := hrate D T hD hT
  filter_upwards [hev, hgood, hwin T hT, hR, hL.eventually_ge_atTop (D + c * T),
    ObservedHistory.eventually_window_scale_le_P6N hL T D] with n hn hgn hwn hRn hLn hθn
  obtain ⟨hsm, hevt⟩ := hn
  intro x hx v hvt hθv _ _ tr hq
  have hsq : 0 < Real.sqrt (R n) := Real.sqrt_pos.2 hRn
  have hΛ : 0 ≤ c * Real.sqrt (R n) := mul_nonneg hc hsq.le
  have hnum : D / Real.sqrt (R n) + c * Real.sqrt (R n) * (T / R n) ≤
      L n / Real.sqrt (R n) := by
    have h2 : c * Real.sqrt (R n) * (T / R n) = c * T / Real.sqrt (R n) := by
      have h := Real.sqrt_div_self' (x := R n)
      calc c * Real.sqrt (R n) * (T / R n) = c * T * (Real.sqrt (R n) / R n) := by ring
        _ = c * T * (1 / Real.sqrt (R n)) := by rw [h]
        _ = c * T / Real.sqrt (R n) := by ring
    rw [h2, ← add_div]
    exact div_le_div_of_nonneg_right hLn hsq.le
  have hdist := (Hs n).hdist_rel_of_stage_bounds_C11D (haT n) (hst n) (has n) (seedTrace n) (y n)
    hΛ hnum hsm hevt
  have hW := (Hs n).hasSpatialCanonicalTimeControl_on_window_traces_P6N (haT n) (hst n) (has n)
    (seedTrace n) (y n) hRn hgn hθn.1 hwn hdist x hx v hvt hθv tr hq.le
  exact hW.1

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

/-! ## consumer：(D1) → P6B2 固定 `A_*` → P6B bridge -/

namespace GC.LongTime.Ch11

open DifferentialGeometry.PDE.RicciFlow DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **consumer（G4）**：`hD1_of_endpoint_bounds_C11D`（G1–G3 装配的 (D1)）→ `hdist_fixed_of_D1_P6B2`
（`A_* = A₀ + 1`）→ `tracedKappa_of_window_margin_P6B2`（P6B bridge，window κ 在 `A₀ + 1`、种子体积在
`A_s ≤ A₀ + 1`）。序列写成 `Hs`，`hHs : Hs = fun n => (F.tower.history (ind n)).toHistory` 后 `subst`。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {A₀ As κ : ℝ} (hAs : 0 < As) (hAsle : As ≤ A₀ + 1) (ind : ℕ → ℕ)
    (hW : LocalKappaWindowAt_P6B F (fun _ => 0) (A₀ + 1) κ)
    (Hs : ℕ → ObservedHistory.{u}) (hHs : Hs = fun n => (F.tower.history (ind n)).toHistory)
    (t : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (p : ∀ n, ((Hs n).stageAt (t n)).Carrier)
    (r : ℕ → ℝ) (hr : ∀ n, 0 < r n)
    (hlate : Tendsto (fun n => (t n : ℝ)) atTop atTop)
    (htime : ∀ n, 2 * r n ^ 2 < (t n : ℝ))
    (hsmall : ∀ n, hasSmallParabolicCurvature (Hs n) (t n) (p n) (r n))
    (hvol : ∀ n, ENNReal.ofReal (As⁻¹ * r n ^ 3) ≤
      Geometry.Collapse.ballVolume ((Hs n).stageMetric ((Hs n).activeStage (t n)) (t n)) (p n)
        (r n))
    (aSeed : ∀ n, Icc (0 : ℝ) (Hs n).horizon)
    (haT : ∀ n, aSeed n ≤ t n) (hclock : ∀ n, (aSeed n : ℝ) = (t n : ℝ) - r n ^ 2)
    (seedTrace : ∀ n, BackwardPointTrace (Hs n) ((Hs n).activeStage (aSeed n))
      ((Hs n).activeStage (t n)) ((Hs n).activeStage_mono (haT n)) (p n))
    (s : ∀ n, Icc (0 : ℝ) (Hs n).horizon) (hst : ∀ n, s n ≤ t n) (has : ∀ n, aSeed n ≤ s n)
    (y : ∀ n, ((Hs n).stageAt (s n)).Carrier) (R : ℕ → ℝ) (hR : ∀ᶠ n in atTop, 0 < R n)
    (hX : Tendsto (fun n => R n * r n ^ 2) atTop atTop)
    (hmargin : Tendsto (fun n => R n * ((s n : ℝ) - ((t n : ℝ) - r n ^ 2 / 2))) atTop atTop)
    (hcenter : ∀ᶠ n in atTop, y n ∈ riemannianBallOf
      ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n))
      ((seedTrace n).point ((Hs n).activeStage (s n)) ((Hs n).activeStage_mono (has n))
        ((Hs n).activeStage_mono (hst n))) (A₀ * r n))
    (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ)
    (records : ∀ n (e : Fin (Hs n).eventCount), T₀ n ≤ (Hs n).time e.succ →
      GeometricCutoffRecord (Hs n) e (q n))
    (hOld : ∀ n (e : Fin (Hs n).eventCount), T₀ n ≤ (Hs n).time e.succ →
      ((Hs n).event e).old = ((Hs n).event e).transition.trace.retainedCore)
    (hcan : ∀ n (e : Fin (Hs n).eventCount) (he : T₀ n ≤ (Hs n).time e.succ) b,
      ((records n e he).static b).hasCanonicalWindow)
    (hacc : ∀ n, (q n).modelAccuracy ≤ 1 / 2)
    (hDm : ∀ n, StandardCap.transitionEnd + 10 < (q n).modelRadius)
    (hT₀ : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀ n ≤ (s n : ℝ) - T / R n)
    (hgeom : ∀ D T : ℝ, 0 < D → 0 < T → ∃ ℓ K : ℝ, 0 < ℓ ∧ K * ℓ ^ 2 ≤ 1 ∧ ∀ᶠ n in atTop,
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ τ : ℝ, (s n : ℝ) - T / R n < τ → (Hs n).time ((Hs n).activeStage (s n)) < τ →
          τ < s n →
        ∀ z : ((Hs n).stageAt (s n)).Carrier,
          (riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ)
              ((seedTrace n).point ((Hs n).activeStage (s n))
                ((Hs n).activeStage_mono (has n)) ((Hs n).activeStage_mono (hst n))) z <
              ENNReal.ofReal (ℓ / Real.sqrt (R n)) ∨
            riemannianEDistOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) x z <
              ENNReal.ofReal (ℓ / Real.sqrt (R n))) →
          Real.sqrt (DifferentialGeometry.Tensor0SBundle.normSq0S
            ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) z 4
            (metricRm04At ((Hs n).stageMetric ((Hs n).activeStage (s n)) τ) z)) ≤ K * R n) ∧
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aSeed n ≤ v) (hvs : v ≤ s n),
          (s n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
          ((Hs n).activeStage_mono hvs) x,
        ∀ (e : Fin (Hs n).eventCount) (h1 : (Hs n).activeStage (aSeed n) ≤ e.castSucc)
          (h2 : e.succ ≤ (Hs n).activeStage (t n)) (h3 : (Hs n).activeStage v ≤ e.castSucc)
          (h4 : e.succ ≤ (Hs n).activeStage (s n)), (v : ℝ) < (Hs n).time e.succ →
        ∀ (he : T₀ n ≤ (Hs n).time e.succ) b,
          (seedTrace n).point e.succ (h1.trans e.castSucc_lt_succ.le) h2 ∉
              ((records n e he).static b).window ''
                {z : standardCapWindow (q n).modelRadius |
                  ‖z.val‖ ≤ StandardCap.transitionEnd + 10} ∧
            tr.point e.succ (h3.trans e.castSucc_lt_succ.le) h4 ∉
              ((records n e he).static b).window ''
                {z : standardCapWindow (q n).modelRadius |
                  ‖z.val‖ ≤ StandardCap.transitionEnd + 10}) ∧
      (∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (_hav : aSeed n ≤ v) (hvs : v ≤ s n),
          (s n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
          ((Hs n).activeStage_mono hvs) x,
        ∀ (e : Fin (Hs n).eventCount) (h1 : (Hs n).activeStage (aSeed n) ≤ e.castSucc)
          (h2 : e.succ ≤ (Hs n).activeStage (t n)) (h3 : (Hs n).activeStage v ≤ e.castSucc)
          (h4 : e.succ ≤ (Hs n).activeStage (s n)) (t' : ℝ),
          (v : ℝ) < t' → (Hs n).time e.castSucc < t' → t' < (Hs n).time e.succ →
        ∀ z : ((Hs n).stage e.castSucc).Carrier, ∀ ξ : TangentSpace ThreeModel z,
          (riemannianEDistOf ((Hs n).stageMetric e.castSucc t')
              ((seedTrace n).point e.castSucc h1 (e.castSucc_lt_succ.le.trans h2)) z <
              ENNReal.ofReal (ℓ / Real.sqrt (R n)) ∨
            riemannianEDistOf ((Hs n).stageMetric e.castSucc t')
              (tr.point e.castSucc h3 (e.castSucc_lt_succ.le.trans h4)) z <
              ENNReal.ofReal (ℓ / Real.sqrt (R n))) →
          ricciTensor ((Hs n).stageMetric e.castSucc t') z ξ ξ ≤
            (3 / (ℓ / Real.sqrt (R n)) ^ 2) *
              ((Hs n).stageMetric e.castSucc t').inner z ξ ξ)) :
    ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Hs n).stageMetric ((Hs n).activeStage (s n)) (s n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Hs n).horizon) (hvt : v ≤ s n), (s n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Hs n) ((Hs n).activeStage v) ((Hs n).activeStage (s n))
        ((Hs n).activeStage_mono hvt) x,
      ∀ r'' : ℝ, 0 < r'' → r'' ≤ r n / 200 →
        (Hs n).isParabolicallyRmControlledBall v
          (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) r'' →
        ENNReal.ofReal (κ * r'' ^ 3) ≤
          Geometry.Collapse.ballVolume ((Hs n).stageMetric ((Hs n).activeStage v) v)
            (tr.point ((Hs n).activeStage v) le_rfl ((Hs n).activeStage_mono hvt)) r'' := by
  subst hHs
  exact tracedKappa_of_window_margin_P6B2 hAs hAsle hW ind t p r hlate htime hsmall hvol aSeed
    haT hclock seedTrace s hst y R hR hmargin
    (hdist_fixed_of_D1_P6B2 ind t p r hr aSeed haT seedTrace s hst y R hR hX
      (hD1_of_endpoint_bounds_C11D (fun n => (F.tower.history (ind n)).toHistory) t p r aSeed
        haT seedTrace s hst has y R hR hcenter q T₀ records hOld hcan hacc hDm hT₀ hgeom))

end GC.LongTime.Ch11
