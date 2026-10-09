import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DistCFinalP6DC2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HIPropagationP6HP

/-!
# final 帧条件形 `hdistC` ⇐ producer 自有数据（O-CH11-FINALQ G1，后缀 `_P6FQ`）

`hgapJF{,8}_loc_P6KT2` 的 `hdistQ` 合取是**无条件**形（全深度 traced region，与 max-depth driver 循环；
本件不付）。下游 final kernel 的 rings 装配只按条件形消费它（`P6KernelFinalRingsP6JK2` l.567 / l.660；
前者有条件孪生 `hwitC_hderivC_of_hdistC_Cg_P6CD`）。本文件给出条件形 `hdistC`（FINCOND
`hgapJF_cond_noJ10_P6JK` 的同名合取、余量 `L/4`、`r := 1`）的 producer，前提全部是 hgapJF producer
∃ 元组里自己已有的数据：
* (SEP) `hsepWK` ⇐ J6 `(n+1)·max(n+1, Q) ≤ scale` + `R ≤ Q`（`sepWK_of_scaleK_final_P6FQ`）。
  `R ≤ Q` 在 producer 里由槽前提 `R ≤ ρ̃(Tn)⁻²` 与 `Q := c·Qs_loc ≥ c·ρ(Tno)⁻²`
  （`neckRadius_rescale_inv_sq_P6X`）给出——方向是 `R ≤ Q`，**不是** J10 的 `Q < R`；
* `hpin`（`a₀ := 0`）⇐ 全事件 `recordsF` + 初始 HI（`hiActive_of_records_P6HP` + `hpin_of_hpinX_P6HP`）；
* `hT₀` ⇐ `T₀ ≤ aSeed` + 窗口 `hwin`。
主定理 `hdistC_final_of_scaleK_P6FQ` = HDISTC2 `hdistC_of_sep_pin_final_P6DC2` 在 `t := σ`、`r := 1` 处。
PROVED，无 binder。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Manifold
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Tensor0SBundle
open scoped Manifold ContDiff Topology ENNReal NNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- 数值核：`n + 1 > max 245 (2C)`、`0 < R ≤ Q` ⇒ `2·max(3/(1/100)², C·R) < (n+1)·max(n+1, Q)`。 -/
theorem two_max_lt_of_scaleK_P6FQ {n C R Q : ℝ} (hn : max 245 (2 * C) < n + 1) (hR : 0 < R)
    (hRQ : R ≤ Q) : 2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R) < (n + 1) * max (n + 1) Q := by
  have h245 : (245 : ℝ) < n + 1 := lt_of_le_of_lt (le_max_left _ _) hn
  have h2C : 2 * C < n + 1 := lt_of_le_of_lt (le_max_right _ _) hn
  have hn0 : (0 : ℝ) < n + 1 := by linarith
  have hM1 : n + 1 ≤ max (n + 1) Q := le_max_left _ _
  have hMQ : Q ≤ max (n + 1) Q := le_max_right _ _
  have h3 : (3 : ℝ) / ((1 : ℝ) / 100) ^ 2 = 30000 := by norm_num
  rw [h3]
  rcases le_total 30000 (C * R) with h | h
  · rw [max_eq_right h]
    have h1 : 2 * C * R < (n + 1) * R := mul_lt_mul_of_pos_right h2C hR
    have h2 : (n + 1) * R ≤ (n + 1) * max (n + 1) Q :=
      mul_le_mul_of_nonneg_left (hRQ.trans hMQ) hn0.le
    linarith
  · rw [max_eq_left h]
    have h1 : (n + 1) * (n + 1) ≤ (n + 1) * max (n + 1) Q :=
      mul_le_mul_of_nonneg_left hM1 hn0.le
    nlinarith

/-- **(SEP) `hsepWK`（`r := 1`）⇐ J6 + `R ≤ Q`（`_P6FQ`，PROVED）**：形 = `hdistC_of_sep_pin_final_P6DC2`
的 `hsepWK` 前提在 `r := fun _ => 1` 处逐字（窗口前件不消费）。 -/
theorem sepWK_of_scaleK_final_P6FQ {K : ℕ → RetainedCoreHistory.{u}} {T₀ Q R : ℕ → ℝ}
    {σ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n))
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hRpos : ∀ n, 0 < R n) (hRQ : ∀ n, R n ≤ Q n) :
    ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) b,
        σ n - T / R n < (K n).time i.succ →
        2 * max (3 / ((fun _ : ℕ => (1 : ℝ)) n / 100) ^ 2) (C * R n) <
          ((recordsK n i hi).static b).neck.scale := by
  intro T _ C _
  obtain ⟨N, hN⟩ := exists_nat_gt (max 245 (2 * C))
  filter_upwards [eventually_ge_atTop N] with n hn
  intro i hi b _
  have hnN : (N : ℝ) ≤ n := by exact_mod_cast hn
  have hlt : max 245 (2 * C) < (n : ℝ) + 1 := by linarith
  exact (two_max_lt_of_scaleK_P6FQ hlt (hRpos n) (hRQ n)).trans_le (hscaleK n i hi b)

/-- **final 条件形 `hdistC` ⇐ producer 数据（`_P6FQ`，PROVED）**：结论 = FINCOND
`hgapJF_cond_noJ10_P6JK` 的 `hdistC` 合取（余量 `L/4`、traced 前提沿子列 `φ`），`Kh := (K ·).toHistory`。
前提逐项是 `hgapJF{,8}_loc_P6KT2` 的槽前提（seed 组 `r = 1`、`hroom`、final 位置）与其 ∃ 元组分量
（`recordsF`、`a₀` + 初始 HI、`recordsK` + canonical window + 参数三界、J6、`T₀ ≤ aSeed`），另加
producer 内部可证的 `0 < a₀ n`、`2 < Tn`、`R ≤ Q`。 -/
theorem hdistC_final_of_scaleK_P6FQ {K : ℕ → RetainedCoreHistory.{u}}
    (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon)
    (y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier) (R : ℕ → ℝ)
    (hfin : ∀ n, (K n).time (Fin.last (K n).eventCount) < (σ n : ℝ) ∧
      (σ n : ℝ) < (K n).horizon)
    (hRpos : ∀ n, 0 < R n) (hR1 : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hroom : ∀ n, (Tn n : ℝ) - 1 ^ 2 / 2 ≤ σ n - L n ^ 2 / R n)
    (htime : ∀ n, 2 * (1 : ℝ) ^ 2 < (Tn n : ℝ))
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) 1)
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - 1 ^ 2)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    {pF : ℕ → CutoffParameters}
    (recordsF : ∀ n i, GeometricCutoffRecord (K n).toHistory i (pF n))
    {a₀ : ℕ → ℝ} (ha₀ : ∀ n, 0 < a₀ n)
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((K n).initialMetric 0) (a₀ n) x ∧
      -3 / a₀ n ≤ metricScalarAt ((K n).initialMetric 0) x)
    {p : ℕ → CutoffParameters} {T₀ Q : ℕ → ℝ}
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n))
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hRQ : ∀ n, R n ≤ Q n) (hT₀a : ∀ n, T₀ n ≤ (aSeed n : ℝ)) :
    ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n)
        (2 * D / Real.sqrt (R n)) (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
          (σ n)) (y n) (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v)
          ((K n).toHistory.activeStage (σ n)) ((K n).toHistory.activeStage_mono hvs) x,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v)
              ((K n).toHistory.activeStage_mono hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((K n).toHistory.activeStage v) le_rfl
              ((K n).toHistory.activeStage_mono hvs)) ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n))
              (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)) := by
  have hpin := hpin_of_hpinX_P6HP (fun n => (K n).toHistory) a₀ (fun n => (ha₀ n).le)
    (fun n => ObservedHistory.hiActive_of_records_P6HP (K n).toHistory (recordsF n) (ha₀ n)
      (hHI n))
  have hRlim : Tendsto R atTop atTop := tendsto_atTop_mono hR1
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hRr : Tendsto (fun n => R n * (fun _ : ℕ => (1 : ℝ)) n ^ 2) atTop atTop := by
    simpa using hRlim
  have hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n := by
    intro B
    rcases le_or_gt B 0 with hB0 | hB0
    · refine Eventually.of_forall fun n => ?_
      have h1 : (aSeed n : ℝ) ≤ σ n := has n
      have h2 : B / R n ≤ 0 := div_nonpos_of_nonpos_of_nonneg hB0 (hRpos n).le
      linarith [hT₀a n]
    · filter_upwards [hwin B hB0] with n hn
      linarith [hT₀a n]
  exact hdistC_of_sep_pin_final_P6DC2 (t := fun n => (σ n : ℝ)) (fun n => (hfin n).1)
    (fun n => (hfin n).2) rfl σ y R (fun _ => rfl) hRpos (le_refl (0 : ℝ)) hpin Tn aSeed haT
    hsT has pT seedTrace (fun _ => 1) L hL hroom htime hsmall hclock hRr recordsK hcanK hacc
    hrad hord hT₀ (sepWK_of_scaleK_final_P6FQ recordsK hscaleK hRpos hRQ)

/-- consumer：`φ := id` 子列上、traced region 已知时直接取用（条件形，不升级为无条件）。 -/
example {K : ℕ → RetainedCoreHistory.{u}} {T₀ Q R : ℕ → ℝ} {p : ℕ → CutoffParameters}
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n))
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hRpos : ∀ n, 0 < R n) (hRQ : ∀ n, R n ≤ Q n) :
    ∀ᶠ n in atTop, ∀ i hi b, (fun _ : ℕ => (0 : ℝ)) n - 1 / R n < (K n).time i.succ →
      2 * max (3 / ((fun _ : ℕ => (1 : ℝ)) n / 100) ^ 2) (1 * R n) <
        ((recordsK n i hi).static b).neck.scale :=
  sepWK_of_scaleK_final_P6FQ (σ := fun _ => 0) recordsK hscaleK hRpos hRQ 1 one_pos 1 zero_le_one

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
