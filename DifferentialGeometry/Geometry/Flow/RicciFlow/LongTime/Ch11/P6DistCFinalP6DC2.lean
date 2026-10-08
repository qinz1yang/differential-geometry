import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Dist.HdistCondAnySeedC11G3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6ClosedResidualCondP6CD
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SepTnP6SN

/-!
# final slab 条件形 `hdistC`（HDISTC 的 final 孪生；O-CH11-HDISTC2，后缀 `_P6DC2`）

event 侧 S-CH11-HDISTC：`hdistC_of_traced_C11G3`（G0）把 K 层 traced region 搬到 E 层
`Hs := K.eventPrefix j t`，经 P6CE `exists_hscal_of_isTracedRegion_P6E` + P6PFX uniform kernel
`hdist_rel_pointwise_radius_uniform_C11G2`（`Hs` 泛型）+ E → K 搬运；`hdistC_of_traced_anySeed_C11G3`（G2）
再用 `earlier_seed_small_on_half_depth_C11G3` 把 K0 种子从 `Tn` 回推到 `σ`。

**final 孪生的关键观察**：eventPrefix 截断在 event 侧只有一个作用——把 uniform kernel 要的 (SEP)
（窗口 `σ − T/R < time e.succ` 内**全部** event 的 scale 下界）限到 `i < j`（event `j` 及以后的 scale
没有供给）。final 位置 `time last < t < horizon` 时，(SEP) 前提本身已对**全部** `i` 给出
（hdistC_final.txt 改动 (2)），所以 E 层直接取 `Hs := Kh = (K n).toHistory`，不需要 final 截断 history，
也不需要 K ↔ E 的 traced / 种子 / records 搬运（全部是恒等）。于是：
* `hdistC_of_traced_final_P6DC2`（G0 孪生）：traced region `(2D, T, Kc)` 沿 `φ` ⇒
  `ℓ₀ := min 1 (D e^{-9KcT})` ⇒ `hscal`（P6CE，`Hs := Kh ∘ φ`）⇒ uniform kernel 在子列 `K ∘ φ` 上取值；
* **`hdistC_final_P6DC2`**（G1 主定理）：陈述 = `build-logs/scratch/O-CH11-FINCOND/hdistC_final.txt` 逐字
  （只把占位名 `hdistC_of_traced_anySeed_final_P6HC` 换成本名；生成器 `build-logs/scratch/O-CH11-HDISTC2/g1.py`
  断言）；证明 = G2 `hdistC_of_traced_anySeed_C11G3` 逐字重放（半深度回推 + `hwin / hlate` 由 `R r² → ∞` 推出）。
  final 位置参数 `_htl / _htK` 与 `σ ≤ t` 保留为合同位置参数，证明不消费（见上）。
* traced-conditional（D-9）：结论只在 driver 给出 traced region 的子列 `φ`、有限深度 `T / R` 上取值，
  **不**升级为无条件 TR；无 PROVISIONAL binder。

G2 consumer（`hgapJF_cond` / `hgapJF8_cond` 的 `hdistC` 合取项，余量 `L/4`、`r := 1`、尾移位）见
`hdistC_of_sep_pin_final_P6DC2`（`hdistC_of_sep_pin_P6CK` 的 final 孪生）；(SEP) 前提的 at-Tn 核 final 孪生
`sepWK_of_smallAtTn_final_P6DC2`（供 SEP′ / hnomId owner）。
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

/-- **G0 final 孪生（`_P6DC2`）**：`hdistC_of_traced_C11G3` 去掉 event 位置与 `Tn ≤ t`，(SEP) 对全部
event；E 层 = `Kh` 本身（无截断）。traced region `(2D, T, Kc)` 沿 `φ` eventually ⇒ 相对 hdist `(D, T)`。 -/
theorem hdistC_of_traced_final_P6DC2 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (K : ℕ → RetainedCoreHistory.{u}),
    let Kh : ℕ → ObservedHistory.{u} := fun n => (K n).toHistory
    ∀ (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
      (R r L : ℕ → ℝ) (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
      (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
      (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
      (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
        ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n)),
      (∀ᶠ n in atTop, 0 < R n) → Tendsto L atTop atTop →
      (∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n)) →
      (∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2) →
      Tendsto (fun n => R n * r n ^ 2) atTop atTop →
      ∀ {a₀ : ℝ}, 0 ≤ a₀ →
      (∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
        InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (a₀ + τ') x) →
    ∀ (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ)
      (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (q n)),
      (∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) b,
        ((recordsK n i hi).static b).hasCanonicalWindow) →
      (∀ n, (q n).modelAccuracy ≤ ε₀) → (∀ n, 2 ≤ (q n).modelOrder) →
      (∀ n, StandardCap.transitionEnd + 10 < (q n).modelRadius) →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ (σ n : ℝ) - T / R n) →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, 1 ≤ R n * ((σ n : ℝ) - T / R n)) →
      (∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
        ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) b,
          (σ n : ℝ) - T / R n < (K n).time i.succ →
          2 * max (3 / r n ^ 2) (C * R n) < ((recordsK n i hi).static b).neck.scale) →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - T / R n) →
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) := by
  obtain ⟨ε₀, hε₀, hC⟩ := hdist_rel_pointwise_radius_uniform_C11G2.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro K Kh σ y R r L Tn aSeed haT hsT has pT seedTrace hR hL hsmallK hclockK hRr a₀ ha₀ hpinK
    q T₀ recordsK hcanK hacc0 hm hDm hwin hlate hsepWK hT₀ φ hφ D T Kc hD hT hKc htr
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  obtain ⟨ℓ₀, hℓ₀, hℓ₀1, hℓD⟩ := exists_radius_C11G3 (T := T) (Kc := Kc) hD
  have hRφ : ∀ᶠ m in atTop, 0 < R (φ m) := hφt.eventually hR
  have htrφ : ∀ᶠ m in atTop, (Kh (φ m)).isTracedRegion (σ (φ m)) (y (φ m))
      (2 * D / Real.sqrt (R (φ m))) (T / R (φ m)) (Kc * R (φ m)) :=
    Filter.eventually_map.mp htr
  have hscal := ObservedHistory.exists_hscal_of_isTracedRegion_P6E
    (Hs := fun m => Kh (φ m)) (s := fun m => σ (φ m)) (y := fun m => y (φ m))
    (aSeed := fun m => aSeed (φ m)) (R := fun m => R (φ m)) hRφ hKc hℓ₀ hℓD htrφ
  have hmain := hC ℓ₀ hℓ₀ hℓ₀1 (fun m => Kh (φ m)) (fun m => Tn (φ m)) (fun m => pT (φ m))
    (fun m => aSeed (φ m)) (fun m => haT (φ m)) (fun m => seedTrace (φ m)) (fun m => σ (φ m))
    (fun m => hsT (φ m)) (fun m => has (φ m)) (fun m => y (φ m)) (fun m => R (φ m))
    (fun m => r (φ m)) (fun m => L (φ m)) hRφ (hL.comp hφt) (fun m => hsmallK (φ m))
    (fun m => hclockK (φ m)) (hRr.comp hφt) ha₀ (fun m => hpinK (φ m)) (fun m => q (φ m))
    (fun m => T₀ (φ m)) (fun m => recordsK (φ m)) (fun m => hcanK (φ m))
    (fun m => hacc0 (φ m)) (fun m => hm (φ m)) (fun m => hDm (φ m)) D T hD hT
    (hφt.eventually (hwin T hT)) (hφt.eventually (hlate T hT)) hscal
    (fun C hC' => hφt.eventually (hsepWK T hT C hC')) (hφt.eventually (hT₀ T hT))
  exact Filter.eventually_map.mpr hmain

/-- **final slab 条件形 `hdistC`（G1 主定理，`_P6DC2`）**：陈述 = `hdistC_final.txt` 逐字（HDISTC
`hdistC_of_traced_anySeed_C11G3` 的 final 孪生：event 位置 → `time last < t < horizon`；(SEP) 对全部 `i`）。
证明 = G2 逐字重放：半深度回推 `earlier_seed_small_on_half_depth_C11G3`（新半径 `r/100`、新时钟
`a' = σ − (r/100)²`、新 trace 逐点相等）+ G0 final 孪生 `hdistC_of_traced_final_P6DC2`；`hwin / hlate` 由
`R r² → ∞` 推出。final 位置 `_htl / _htK` 与 `σ ≤ t` 不被消费（E 层 = `Kh`，无截断）。 -/
theorem hdistC_final_P6DC2 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ (K : ℕ → RetainedCoreHistory.{u}) (t : ℕ → ℝ)
      (_htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n)
      (_htK : ∀ n, t n < (K n).horizon),
    let Kh : ℕ → ObservedHistory.{u} := fun n => (K n).toHistory
    ∀ (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
      (R r L : ℕ → ℝ) (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
      (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
      (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
      (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
        ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n)),
      (∀ n, (σ n : ℝ) ≤ t n) →
      (∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ)) → (∀ n, 2 * r n ^ 2 < (Tn n : ℝ)) →
      (∀ᶠ n in atTop, 0 < R n) → Tendsto L atTop atTop →
      (∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n)) →
      (∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2) →
      Tendsto (fun n => R n * r n ^ 2) atTop atTop →
      ∀ {a₀ : ℝ}, 0 ≤ a₀ →
      (∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
        InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (a₀ + τ') x) →
    ∀ (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ)
      (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
        GeometricCutoffRecord (K n).toHistory i (q n)),
      (∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) b,
        ((recordsK n i hi).static b).hasCanonicalWindow) →
      (∀ n, (q n).modelAccuracy ≤ ε₀) → (∀ n, 2 ≤ (q n).modelOrder) →
      (∀ n, StandardCap.transitionEnd + 10 < (q n).modelRadius) →
      (∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
        ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) b,
          (σ n : ℝ) - T / R n < (K n).time i.succ →
          2 * max (3 / (r n / 100) ^ 2) (C * R n) < ((recordsK n i hi).static b).neck.scale) →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - T / R n) →
      ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) := by
  obtain ⟨ε₀, hε₀, hC⟩ := hdistC_of_traced_final_P6DC2.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro K _t _htl _htK Kh σ y R r L Tn aSeed haT hsT has pT seedTrace _hσt hhalf htime hR hL
    hsmallK hclockK hRr a₀ ha₀ hpinK q T₀ recordsK hcanK hacc0 hm hDm hsepWK hT₀ φ hφ D T Kc hD hT
    hKc htr
  have hφt : Tendsto φ atTop atTop := hφ.tendsto_atTop
  have hshift := fun n => GC.LongTime.Ch11.earlier_seed_small_on_half_depth_C11G3 (haT n) (pT n)
    (r n) (htime n) (hclockK n) (hsmallK n) (seedTrace n) (σ n) (has n) (hsT n) (hhalf n)
  choose a' haa' hav' tr' hclk' hsm' hR2' hpt' using hshift
  have hRr' : Tendsto (fun n => R n * (r n / 100) ^ 2) atTop atTop := by
    refine ((hRr.atTop_div_const (by norm_num : (0 : ℝ) < 10000)).congr fun n => ?_)
    ring
  have hwin' : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (a' n : ℝ) ≤ (σ n : ℝ) - T / R n := by
    intro T hT
    filter_upwards [hR, hRr'.eventually_ge_atTop T] with n hRn hn
    rw [hclk' n]
    have : T / R n ≤ (r n / 100) ^ 2 := by
      rw [div_le_iff₀ hRn]
      linarith
    linarith
  have hlate' : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, 1 ≤ R n * ((σ n : ℝ) - T / R n) := by
    intro T hT
    filter_upwards [hR, hRr'.eventually_ge_atTop (T + 1)] with n hRn hn
    have h1 : R n * (2 * (r n / 100) ^ 2) < R n * (σ n : ℝ) :=
      mul_lt_mul_of_pos_left (hR2' n) hRn
    have h2 : R n * ((σ n : ℝ) - T / R n) = R n * (σ n : ℝ) - T := by
      field_simp
    rw [h2]
    linarith
  have hmain := hC K σ y R (fun n => r n / 100) L σ a' hav' (fun n => le_rfl) hav'
    (fun n => (seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
      ((Kh n).activeStage_mono (hsT n))) tr' hR hL hsm' hclk' hRr' ha₀ hpinK q T₀ recordsK
    hcanK hacc0 hm hDm hwin' hlate' hsepWK hT₀ φ hφ D T Kc hD hT hKc htr
  filter_upwards [hmain, Filter.Eventually.filter_mono hφt (hwin' T hT)] with n hn hw
  intro x hx v hav hvs hvT tr
  have hav'' : a' n ≤ v := by
    have h1 : (a' n : ℝ) ≤ v := hw.trans hvT
    exact h1
  have h := hn x hx v hav'' hvs hvT tr
  rw [hpt' n v hav'' hvs, hpt' n (σ n) (hav' n) le_rfl] at h
  exact h

/-- **G1 consumer（P6ANCH2 条件形接口，final 位置）**：`hdistC_final_P6DC2` 的结论（`Kh := toHistory`，
原 `aSeed` / 原 `seedTrace`）逐字就是 `hwitC_hderivC_of_hdistC_P6M2` 的 `hdistC` binder（event 侧
`hdistC_of_traced_anySeed_C11G3` 的 consumer 的 final 孪生：`(j, hjt, htj)` → `(t, htl, htK)`，
(SEP) 无 `i < j`）。 -/
example {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
    (K : ℕ → RetainedCoreHistory.{u}) (t : ℕ → ℝ)
    (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) (htK : ∀ n, t n < (K n).horizon)
    (Kh : ℕ → ObservedHistory.{u}) (hKh : Kh = fun n => (K n).toHistory)
    (Tn aSeed σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon)
    (haT : ∀ n, aSeed n ≤ Tn n) (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (p : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (p n))
    (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) (R r L : ℕ → ℝ) (hR : ∀ n, 0 < R n)
    (hL : Tendsto L atTop atTop)
    (hgood : ∀ n, ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
      (σ n : ℝ) - L n ^ 2 / R n ≤ (v : ℝ) →
      ∀ z : ((Kh n).stageAt v).Carrier,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n)))) z ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) →
        4 * R n ≤ metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage v) v) z →
        (Kh n).HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hσt : ∀ n, ((σ n : Icc (0 : ℝ) (Kh n).horizon) : ℝ) ≤ t n)
    (hhalf : ∀ n, ((Tn n : Icc (0 : ℝ) (Kh n).horizon) : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ))
    (htime : ∀ n, 2 * r n ^ 2 < ((Tn n : Icc (0 : ℝ) (Kh n).horizon) : ℝ))
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (p n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop) {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (a₀ + τ') x)
    (q : ℕ → CutoffParameters) (T₀ : ℕ → ℝ)
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (q n)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ((∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) b,
        ((recordsK n i hi).static b).hasCanonicalWindow) →
      (∀ n, (q n).modelAccuracy ≤ ε₀) → (∀ n, 2 ≤ (q n).modelOrder) →
      (∀ n, StandardCap.transitionEnd + 10 < (q n).modelRadius) →
      (∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
        ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) b,
          (σ n : ℝ) - T / R n < (K n).time i.succ →
          2 * max (3 / (r n / 100) ^ 2) (C * R n) < ((recordsK n i hi).static b).neck.scale) →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - T / R n) → True) := by
  subst hKh
  obtain ⟨ε₀, hε₀, hC⟩ := hdistC_final_P6DC2.{u}
  refine ⟨ε₀, hε₀, fun hcan hacc hord hrad hsep hT₀ => ?_⟩
  have _hwit := ObservedHistory.hwitC_hderivC_of_hdistC_P6M2 (eps := eps) (C1' := C1')
    (C2' := C2') (Ctime' := Ctime') (fun n => (K n).toHistory) Tn aSeed σ haT hsT has p seedTrace y
    R L hR hL hgood hwin
    (hC K t htl htK σ y R r L Tn aSeed haT hsT has p seedTrace hσt hhalf htime
      (Filter.Eventually.of_forall hR) hL hsmall hclock hRr ha₀ hpin q T₀ recordsK hcan hacc hord
      hrad hsep hT₀)
  trivial

/-- **G2 consumer（`hdistC_of_sep_pin_P6CK` 的 final 孪生，`_P6DC2`）**：
`hgapJF_cond / hgapJF8_cond` 的 `hdistC` 合取项（余量 `L/4`）⇐ G1 `hdistC_final_P6DC2` 在
`L := L/4`、`σ = t`（`hσt := le_of_eq`）处 + **尾移位**（精度 `≤ 1/(n+1)`、半径 `n + 1 ≤ modelRadius`
只在尾部 `≥ N` 达到 `ε₀` / `transitionEnd + 10`：整列平移 `n ↦ n + N`，子列
`φ ↦ (m ↦ φ (m + N) − N)`，`eventually_map_shift_P6CD` 来回）。event 位置 `(j, hjt, htj)` 换成
final 位置 `(htl, htK)`；(SEP) `hsepWK` 对全部 event（无 `i < j`），新半径 `r/100` 阈值。 -/
theorem hdistC_of_sep_pin_final_P6DC2 {K : ℕ → RetainedCoreHistory.{u}} {t : ℕ → ℝ}
    (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n)
    (htK : ∀ n, t n < (K n).horizon)
    {Kh : ℕ → ObservedHistory.{u}} (hKh : Kh = fun n => (K n).toHistory)
    (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier)
    (R : ℕ → ℝ) (hσ : ∀ n, (σ n : ℝ) = t n) (hRpos : ∀ n, 0 < R n)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (a₀ + τ') x)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
      ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
    (r L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hroom : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ σ n - L n ^ 2 / R n)
    (htime : ∀ n, 2 * r n ^ 2 < (Tn n : ℝ))
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop)
    {p : ℕ → CutoffParameters} {T₀ : ℕ → ℝ}
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n))
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (hsepWK : ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) b,
        (σ n : ℝ) - T / R n < (K n).time i.succ →
        2 * max (3 / (r n / 100) ^ 2) (C * R n) < ((recordsK n i hi).static b).neck.scale) :
    ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (Kh n).isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvs) x,
        riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage v) v)
            ((seedTrace n).point ((Kh n).activeStage v) ((Kh n).activeStage_mono hav)
              ((Kh n).activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvs)) ≤
          riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
              ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                ((Kh n).activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)) := by
  subst hKh
  obtain ⟨ε₀, hε₀, hC⟩ := hdistC_final_P6DC2.{u}
  obtain ⟨N, hN⟩ := exists_tail_index_P6R2 hε₀ (StandardCap.transitionEnd + 10)
  have hhalf : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ (σ n : ℝ) := fun n => by
    have : 0 ≤ L n ^ 2 / R n := div_nonneg (sq_nonneg _) (hRpos n).le
    linarith [hroom n]
  have hLsh : Tendsto (fun m => L (m + N) / 4) atTop atTop :=
    (tendsto_add_atTop_iff_nat (f := fun n => L n / 4) N).2 (hL.atTop_div_const (by norm_num))
  have hRrsh : Tendsto (fun m => R (m + N) * r (m + N) ^ 2) atTop atTop :=
    (tendsto_add_atTop_iff_nat (f := fun n => R n * r n ^ 2) N).2 hRr
  have hacc' : ∀ m : ℕ, (p (m + N)).modelAccuracy ≤ ε₀ := fun m =>
    (hacc (m + N)).trans (hN m).1
  have hord' : ∀ m : ℕ, 2 ≤ (p (m + N)).modelOrder := fun m => by
    have := hord (m + N)
    omega
  have hrad' : ∀ m : ℕ, StandardCap.transitionEnd + 10 < (p (m + N)).modelRadius := fun m =>
    (hN m).2.trans_le (hrad (m + N))
  intro φ hφ D T Kc hD hT hKc htr
  have hφ' : StrictMono (fun m => φ (m + N) - N) := fun a b hab => by
    have h1 : φ (a + N) < φ (b + N) := hφ (Nat.add_lt_add_right hab N)
    have h2 : a + N ≤ φ (a + N) := hφ.id_le (a + N)
    exact Nat.sub_lt_sub_right ((Nat.le_add_left N a).trans h2) h1
  have htr' := (eventually_map_shift_P6CD N hφ).1 htr
  have key := hC (fun m => K (m + N)) (fun m => t (m + N)) (fun m => htl (m + N))
    (fun m => htK (m + N)) (fun m => σ (m + N)) (fun m => y (m + N))
    (fun m => R (m + N)) (fun m => r (m + N)) (fun m => L (m + N) / 4) (fun m => Tn (m + N))
    (fun m => aSeed (m + N)) (fun m => haT (m + N)) (fun m => hsT (m + N))
    (fun m => has (m + N)) (fun m => pT (m + N)) (fun m => seedTrace (m + N))
    (fun m => (hσ (m + N)).le) (fun m => hhalf (m + N)) (fun m => htime (m + N))
    (Eventually.of_forall fun m => hRpos (m + N)) hLsh (fun m => hsmall (m + N))
    (fun m => hclock (m + N)) hRrsh ha₀
    (fun m => hpin (m + N)) (fun m => p (m + N)) (fun m => T₀ (m + N))
    (fun m => recordsK (m + N)) (fun m => hcanK (m + N)) hacc' hord' hrad'
    (fun T' hT' C hC' => (tendsto_add_atTop_nat N).eventually (hsepWK T' hT' C hC'))
    (fun T' _ => (tendsto_add_atTop_nat N).eventually (hT₀ T')) _ hφ' D T Kc hD hT hKc htr'
  refine (eventually_map_shift_P6CD N hφ).2 ?_
  exact key

/-- **(SEP) at-Tn 核的 final 孪生（`sepWK_of_smallAtTn_P6SN` → `_P6DC2`；供 SEP′ / hnomId owner）**：
final 位置 `time last < t ≤ Tn` 下，**全部** event 的 `time i.succ ≤ time last < t ≤ Tn`（event 版用
`i < j`），其余逐字：(DLT) `hδ` + late records 小性 `hsm`（`Tn` 窗口 `[Tn/2, Tn]`）+ prefix ceiling `hsel4`
⇒ `hdistC_final_P6DC2` / `hdistC_of_sep_pin_final_P6DC2` 的 (SEP) 前提（新半径 `r/100` 阈值）。 -/
theorem sepWK_of_smallAtTn_final_P6DC2 {K : ℕ → RetainedCoreHistory.{u}} {T₀ : ℕ → ℝ}
    {p : ℕ → CutoffParameters}
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n))
    {s t Tn r R ρn : ℕ → ℝ}
    (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) (htT : ∀ n, t n ≤ Tn n)
    (hhalf : ∀ n, Tn n - r n ^ 2 / 2 ≤ s n) (htime : ∀ n, 2 * r n ^ 2 < Tn n)
    (hRpos : ∀ n, 0 < R n) (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop)
    (hsel4 : ∀ n, R n ≤ (ρn n ^ 2)⁻¹)
    (hδ : ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount),
      (K n).time i.succ ∈ Icc (Tn n / 2) (Tn n) →
      (p n).recenterConstant * (p n).delta ((K n).time i.succ) ≤ 1 / 2)
    (hsm : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount),
      (K n).time i.succ ∈ Icc (Tn n / 2) (Tn n) → ∀ (hi : T₀ n ≤ (K n).time i.succ) h,
        (recordsK n i hi).nominalRadius h ≤ ε * ρn n) :
    ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) b,
        s n - T / R n < (K n).time i.succ →
        2 * max (3 / (r n / 100) ^ 2) (C * R n) < ((recordsK n i hi).static b).neck.scale := by
  intro T _ C _
  set M : ℝ := max C 1 with hMdef
  have hM1 : 1 ≤ M := le_max_right _ _
  have hM0 : 0 < M := by linarith
  set ε : ℝ := 1 / (4 * M) with hεdef
  have hε : 0 < ε := by positivity
  have h4 : 4 * M * ε = 1 := by
    rw [hεdef]
    field_simp
  have hε1 : ε < 1 := by nlinarith
  filter_upwards [hsm ε hε, hδ, hRr.eventually_ge_atTop (max 30000 (4 * T))] with n hsmn hδn hRrn
  intro i hi b hwin
  have hR := hRpos n
  have hx : 30000 ≤ R n * r n ^ 2 := (le_max_left _ _).trans hRrn
  have hx4 : 4 * T ≤ R n * r n ^ 2 := (le_max_right _ _).trans hRrn
  have hr2 : 0 < r n ^ 2 := by
    rcases (sq_nonneg (r n)).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hx
      linarith
  have hTR : T / R n ≤ r n ^ 2 / 4 := by
    rw [div_le_iff₀ hR]
    nlinarith
  have hle : i.succ ≤ Fin.last (K n).eventCount := Fin.le_last _
  have hti_hi : (K n).time i.succ ≤ Tn n :=
    ((K n).time_strictMono.monotone hle).trans ((htl n).le.trans (htT n))
  have hti_lo : Tn n / 2 ≤ (K n).time i.succ := by
    have h1 := hhalf n
    have h2 := htime n
    have h3 := sq_nonneg (r n)
    linarith
  have hnom := hsmn i ⟨hti_lo, hti_hi⟩ hi ⟨b.1.1⟩
  have hS := static_scale_ge_of_recenter_P6CD (recordsK n i hi) (hδn i ⟨hti_lo, hti_hi⟩) b
  set rn := (recordsK n i hi).nominalRadius ⟨b.1.1⟩
  have hrn : 0 < rn := (recordsK n i hi).nominal_pos _
  set ρ0 := ρn n
  have hερ : 0 < ε * ρ0 := hrn.trans_le hnom
  have hρ : 0 < ρ0 := pos_of_mul_pos_right hερ hε.le
  have hRρ : R n * ρ0 ^ 2 ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right (hsel4 n) (sq_nonneg ρ0)
    rwa [inv_mul_cancel₀ (pow_pos hρ 2).ne'] at h
  have hrn2 : rn ^ 2 ≤ ε ^ 2 * ρ0 ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hrn.le hnom 2
  have h3 : 3 / (r n / 100) ^ 2 ≤ R n := by
    have hpos : 0 < (r n / 100) ^ 2 := by
      have e : (r n / 100) ^ 2 = r n ^ 2 / 10000 := by ring
      rw [e]
      exact div_pos hr2 (by norm_num)
    rw [div_le_iff₀ hpos]
    have e : R n * (r n / 100) ^ 2 = R n * r n ^ 2 / 10000 := by ring
    rw [e]
    linarith
  have hmax : max (3 / (r n / 100) ^ 2) (C * R n) ≤ M * R n :=
    max_le (h3.trans (le_mul_of_one_le_left hR.le hM1))
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hR.le)
  have hkey : 2 * (M * R n) * (2 * rn ^ 2) < 1 := by
    have h4MR : 0 ≤ 4 * M * R n := mul_nonneg (mul_nonneg (by norm_num) hM0.le) hR.le
    calc 2 * (M * R n) * (2 * rn ^ 2) = 4 * M * R n * rn ^ 2 := by ring
      _ ≤ 4 * M * R n * (ε ^ 2 * ρ0 ^ 2) := mul_le_mul_of_nonneg_left hrn2 h4MR
      _ = (4 * M * ε) * ε * (R n * ρ0 ^ 2) := by ring
      _ ≤ (4 * M * ε) * ε * 1 :=
        mul_le_mul_of_nonneg_left hRρ (mul_nonneg (by rw [h4]; norm_num) hε.le)
      _ = ε := by rw [h4]; ring
      _ < 1 := hε1
  have hpos2 : 0 < 2 * rn ^ 2 := mul_pos two_pos (pow_pos hrn 2)
  have hlt : 2 * (M * R n) < (2 * rn ^ 2)⁻¹ := by
    rw [← one_div]
    exact (lt_div_iff₀ hpos2).2 hkey
  calc 2 * max (3 / (r n / 100) ^ 2) (C * R n) ≤ 2 * (M * R n) := by linarith
    _ < (2 * rn ^ 2)⁻¹ := hlt
    _ ≤ ((recordsK n i hi).static b).neck.scale := hS


end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
