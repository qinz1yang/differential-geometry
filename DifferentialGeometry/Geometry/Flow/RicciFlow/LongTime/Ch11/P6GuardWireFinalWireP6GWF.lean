import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GuardWireFinalSeedP6GWF
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GuardWireFinalScalP6GWF
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GuardWireFinalP6GW

/-!
# GUARDWIRE-FINAL G4：三核喂 `hseedG` ⇒ hdistW final 全链消去 hseedTop / hseedG（`_P6GWF`）

1. `RetainedCoreHistory.windowSeed_pointAnchor_final_P6GWF`：WSBASE
   `ObservedHistory.windowSeed_pointAnchor_C11WB` 的 final-slab 孪生（证明体逐字；closure 步 = G2
   `seed_closure_firstExit_stopped_final_P6GWF`，`hscal` = G3
   `windowScal_of_pickedTop_local_final_P6GWF`）。
2. `hseedG_final_top_P6GWF` / `hseedG_final_seq_P6GWF`：GUARDWIRE G1
   `pickedBallWindowSeedGuarded_top_P6GW` / `hseedTopGuarded_seq_P6GW` 的 final 孪生，结论**直接**是
   GW G2b `hseedG` 槽的形（stageMetric /
   `activeStage σ` 形；final 支 `activeStage σ = last`，经 `stageMetric_last_restrict_P6HF` 落到 restrict
   final slab flow）。常数同 event：`θ := 1/(2·Ct·Cg)`、`C := max (max 1 (6Cg)) (2Cg/ρ_lp(C2)²)`、
   `Lc := max (2·Rad) (2 + 16√K₀·θ)`。
3. `hdistW_finalSlab_pointAnchor_P6GWF`（主定理）：GW G2b `hdistW_finalSlab_guarded_P6GW` 的陈述去掉 `hseedG`、
   加 `0 ≤ C2g`；结论 = final hdistW 槽逐字。

## binder 表（R-C11-19 D-19-3 口径：point-anchor 完整前提逐项，相对 GW G2b final 全链原表）
（每项：point-anchor 前提 — final 链来源 — 状态）
* `hxG`（ExitGuard `d_σ(O, x) ≤ dσ + (Lc/2)/√R_n`）— 三角不等式 + `x ∈ B_σ(y, Rad/√R_n)`、`2Rad ≤ Lc`
  — 内部证出（无 binder）。
* `hxv`（anchor `R(σ, x) ≤ Λq`）— `q := M/Cg`、`M := max(R(σ, x), Cg·R_n)`，恒真 — 内部证出。
* 窗口包含 `σ − θ/q ≤ s ≤ σ`、`time last < s` — guard `2·Ct·M·(σ − s) ≤ 1` + `θ = 1/(2·Ct·Cg)`；
  槽自带 `s < σ`、`time last < s` — 内部证出。
* hgood（`HgoodCg_C11SH`，区域 `L/√R`、阈值 `Cg·R`）— 原表 `hgood` — 原表已有。
* seed：`hsmall` / `hclock` / `seedTrace` / `haT hsT has` — 原表 K0 + 选择数据 — 原表已有。
* pinching `hpin`（`a₁`、`0 ≤ a₁`）— 原表 HI `hpin` / `ha₁` — 原表已有。
* 曲率—半径预算 `hRr`（`2500·K₀ ≤ R·r²`）— 原表 `hRr : R·r² → ∞`（eventually）— 原表已有。
* 晚时刻 `hlate`（`1 ≤ R·(σ − θ/R)`）— 原表 `hRt`（`R(t, yG)·t → ∞`，经 `hRn`）— 原表已有。
* 窗口深度 `hav`（`aSeed ≤ σ − θ/R`）— 原表 `hwin θ` — 原表已有。
* `Lc / L` 裕量 `hL`、`hρL`、`θ ≤ L²` — 原表 `hL : L → ∞`（eventually）— 原表已有。
* 时间导数预算 `Ctg·Cg·θ ≤ 1/2`、`1 ≤ 2·Ct·Cg·θ` — `Ct := Ctime + Ctg + 1`（`0 < Ct`、`Ctg ≤ Ct` 自动）
  — 内部证出。
* `0 < Cg` — 原表 — 原表已有。
* `0 ≤ C2g`（witness 梯度常数符号，`localPropagationRadius_pos` 需要）— 无 — **新增**（平凡常数条件）。
* `hseedG`（GW G2b）— 本文件 `hseedG_final_seq_P6GWF` — **消去**。

净变化（final 支）：`hseedG` → `0 ≤ C2g`（与 event 支 GW G2 的 hseedTop → `0 ≤ C2g` 同形）。剩余 binder 表 = GW G2b
原表去 `hseedG`：`hdepthAF`（⇐ J10GEN2A final）、`hslabSel`（J10 残余，owner SLTLOCAL）、final `hkappa`、hgood、
FINCOND 层 supplies（`records / hcan / hqcan / hpar / hscale / hθcap / hpinch / hnot / hT₀ / hRt`）、
K0 / HI、`hR / hRlim`、`C2g ≤ Cgrad`、`0 ≤ C2g`。
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.Geometry.Metric
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

section PointAnchorFinal

/-- **point-anchor 窗口 seed closure（final slab，`_P6GWF`，PROVED，无 binder）**：WSBASE
`windowSeed_pointAnchor_C11WB` 的 final 孪生。窗口尺度 `q` 泛型；anchor 只在 `x` 一点（`R(v, x) ≤ Λq`），
ExitGuard 只在 `x`（`d_v(O, x) ≤ dσ + (Lc/2)/√R`）；结论：`v′ ∈ [v − β/q, v]`（`time last < v′`）⇒
`d_{v′}(O, x) ≤ dσ + L/√R`（restrict final slab flow）。证明体逐字（closure = G2，`hscal` = G3）。 -/
theorem RetainedCoreHistory.windowSeed_pointAnchor_final_P6GWF {eps C1' C2' : ℝ} {Ctime' : ℝ≥0}
    {Cg : ℝ} (hC2 : 0 ≤ C2') (K : RetainedCoreHistory.{u})
    (h : K.time (Fin.last K.eventCount) < K.horizon) {Tn aSeed σ : Icc (0 : ℝ) K.toHistory.horizon}
    (haT : aSeed ≤ Tn) (hsT : σ ≤ Tn) (has : aSeed ≤ σ) {pT : (K.toHistory.stageAt Tn).Carrier}
    {r : ℝ} (hsmall : GC.LongTime.hasSmallParabolicCurvature K.toHistory Tn pT r)
    (hclock : (aSeed : ℝ) = (Tn : ℝ) - r ^ 2)
    (seedTrace : BackwardPointTrace K.toHistory (K.toHistory.activeStage aSeed)
      (K.toHistory.activeStage Tn) (K.toHistory.activeStage_mono haT) pT)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (t : Icc (0 : ℝ) K.toHistory.horizon) (x : (K.toHistory.stageAt t).Carrier),
      InFixedHamiltonIveyRegion (K.toHistory.stageMetric (K.toHistory.activeStage t) t) (a₀ + t) x)
    (y : (K.toHistory.stageAt σ).Carrier) {R L Lc : ℝ} (hR : 0 < R)
    (hgood : ∀ (v : Icc (0 : ℝ) K.toHistory.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ 2 / R ≤ (v : ℝ) →
      ∀ z : (K.toHistory.stageAt v).Carrier,
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage v) v)
            (seedTrace.point (K.toHistory.activeStage v) (K.toHistory.activeStage_mono hav)
              (K.toHistory.activeStage_mono (hvs.trans hsT))) z ≤
          riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
              (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
                (K.toHistory.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        Cg * R ≤ metricScalarAt (K.toHistory.stageMetric (K.toHistory.activeStage v) v) z →
        K.toHistory.HasSpatialCanonicalTimeControl eps C1' C2' Ctime' v z)
    (h1 : K.toHistory.activeStage aSeed ≤ Fin.last K.eventCount)
    (h2 : Fin.last K.eventCount ≤ K.toHistory.activeStage Tn)
    {v q Λ β C : ℝ} (hv2 : v < K.horizon) (hRq : R ≤ q) (hΛ : 0 < Λ)
    (hCgΛ : Cg * R ≤ Λ * q) (hbud : (Ctime' : ℝ) * Λ * β ≤ 1 / 2) (hC1 : 1 ≤ C)
    (hΛC : 6 * Λ ≤ C) (hρC : 2 * Λ ≤ localPropagationRadius C2' ^ 2 * C)
    (hRr : 2500 * max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4))) ≤ R * r ^ 2)
    (hL : 2 + 16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) *
      max β 0 ≤ Lc)
    (hρL : Lc + 2 * (localPropagationRadius C2' / Real.sqrt (2 * Λ)) ≤ L)
    (hav : (aSeed : ℝ) ≤ v - β / q) (hvσ : v ≤ σ) (hσL : (σ : ℝ) - L ^ 2 / R ≤ v - β / q)
    (hlate : 1 ≤ R * (v - β / q)) (x : (K.stage (Fin.last K.eventCount)).Carrier)
    (hxG : riemannianEDistOf
      (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric v)
      (seedTrace.point (Fin.last K.eventCount) h1 h2) x ≤
        riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
            (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
              (K.toHistory.activeStage_mono hsT)) y +
          ENNReal.ofReal (Lc / 2 / Real.sqrt R))
    (hxv : ((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.scalar v x ≤ Λ * q)
    (v' : ℝ) (hwin : v - β / q ≤ v') (hv'v : v' ≤ v)
    (hv'1 : K.time (Fin.last K.eventCount) < v') :
    riemannianEDistOf (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric v')
        (seedTrace.point (Fin.last K.eventCount) h1 h2) x ≤
      riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
          (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
            (K.toHistory.activeStage_mono hsT)) y +
        ENNReal.ofReal (L / Real.sqrt R) := by
  have hq : 0 < q := hR.trans_le hRq
  have hsR : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  have hLc0 : 0 ≤ Lc := by
    have h0 : 0 ≤ 16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) *
        max β 0 := mul_nonneg (by positivity) (le_max_right _ _)
    linarith
  have hLcL : Lc / Real.sqrt R ≤ L / Real.sqrt R := by
    have : 0 ≤ 2 * (localPropagationRadius C2' / Real.sqrt (2 * Λ)) := by
      have := localPropagationRadius_pos hC2
      positivity
    exact div_le_div_of_nonneg_right (by linarith) hsR.le
  have hL' : 2 * max 1 0 +
      16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) * max β 0 ≤
        Lc := by
    rw [max_eq_left zero_le_one]
    linarith
  have hxx : x ∈ riemannianBallOf
      (((K.finalSlab h).restrictIncoming le_rfl h le_rfl).flow.base.metric v) x
      (1 / Real.sqrt q) := by
    change riemannianEDistOf _ x x < ENNReal.ofReal _
    rw [riemannianEDistOf_self]
    exact ENNReal.ofReal_pos.mpr (by positivity)
  set dσ := riemannianEDistOf (K.toHistory.stageMetric (K.toHistory.activeStage σ) σ)
    (seedTrace.point (K.toHistory.activeStage σ) (K.toHistory.activeStage_mono has)
      (K.toHistory.activeStage_mono hsT)) y
    with hdσdef
  rcases eq_or_ne dσ ⊤ with hT | hT
  · rw [hT, top_add]
    exact le_top
  have hdσ : dσ = ENNReal.ofReal dσ.toReal := (ENNReal.ofReal_toReal hT).symm
  have hlate' : ∀ s : ℝ, v - β / q ≤ s → 1 ≤ q * s := by
    intro s hs
    have hpos : 0 < v - β / q := by
      by_contra hneg
      have hle := not_lt.mp hneg
      nlinarith
    have hRs : R * (v - β / q) ≤ R * s := mul_le_mul_of_nonneg_left hs hR.le
    have hqs : R * s ≤ q * s := mul_le_mul_of_nonneg_right hRq (hpos.le.trans hs)
    linarith
  have hcl := K.seed_closure_firstExit_stopped_final_P6GWF h haT hsmall hclock seedTrace ha₀
    hpin h1 h2 x x hdσ ENNReal.toReal_nonneg hR hRq hC1 hRr hL' hxG hxx hwin hv'v hv'1 hv2
    (hav.trans hwin) (hvσ.trans hsT) (hlate' v' hwin)
    (fun s hs1 hsv hs0 hG z hz => windowScal_of_pickedTop_local_final_P6GWF hC2 K h haT hsT
      has seedTrace y hR hgood h1 h2 hv2 hq hRq hΛ hCgΛ hbud hΛC hρC hρL hLc0 hvσ x
      hxv s hs1 hsv hs0 (hav.trans hs1) (hσL.trans hs1) (fun r hr => (hG r hr).le) z hz)
  exact hcl.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal hLcL))

end PointAnchorFinal

section SeedGFinal

/-- **`hseedG` 在 `n` 处（final top 点，`_P6GWF`，PROVED，无 binder）**：GUARDWIRE G1
`pickedBallWindowSeedGuarded_top_P6GW` 的 final 孪生，结论直接是 GW G2b `hseedG` 槽在 `n` 处的体
（stageMetric / `activeStage σ` 形）。point-anchor（final）在 top 点逐点实例化：anchor 时刻 `v := σ_n`、
`M := max(R(σ, x), Cg·R_n)`、`q := M/Cg`、`Λ := Cg`、深度 `θ`（`1 ≤ 2·Ct·Cg·θ`、`Ctg·Cg·θ ≤ 1/2`）；guard ⇒
`σ − s ≤ θ/q`；ExitGuard ⇐ 三角不等式 + `x ∈ B_σ(y, Rad/√R_n)`、`2Rad ≤ Lc`。不需要 `hanchor0` / hpick /
`hdistW` 槽。 -/
theorem hseedG_final_top_P6GWF {Cg β Rad : ℝ} {Ct : ℝ≥0}
    (K : ℕ → RetainedCoreHistory.{u})
    {Tn aSeed σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {haT : ∀ n, aSeed n ≤ Tn n} {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
    {pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier}
    {seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n)}
    {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R L : ℕ → ℝ} {eps C1 C2 : ℝ}
    {Ctg : ℝ≥0}
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L eps C1 C2 Ctg)
    (hC2 : 0 ≤ C2) (n : ℕ) (hR : 0 < R n)
    (hv1 : (K n).time (Fin.last (K n).eventCount) < σ n) (hv2 : (σ n : ℝ) < (K n).horizon)
    {r : ℝ} (hsmall : GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) r)
    (hclock : (aSeed n : ℝ) = (Tn n : ℝ) - r ^ 2)
    {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ (τ' : Icc (0 : ℝ) (K n).toHistory.horizon)
      (x : ((K n).toHistory.stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ') τ')
        (a₀ + τ') x)
    {θ C Lc : ℝ} (hCg : 0 < Cg) (hCt : 0 < (Ct : ℝ)) (hθ : 0 ≤ θ)
    (hθ2 : 1 ≤ 2 * (Ct : ℝ) * Cg * θ) (hbud : (Ctg : ℝ) * Cg * θ ≤ 1 / 2) (hC1 : 1 ≤ C)
    (hΛC : 6 * Cg ≤ C) (hρC : 2 * Cg ≤ localPropagationRadius C2 ^ 2 * C)
    (hRr : 2500 * max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4))) ≤ R n * r ^ 2)
    (hL : 2 + 16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) *
      max θ 0 ≤ Lc)
    (hρL : Lc + 2 * (localPropagationRadius C2 / Real.sqrt (2 * Cg)) ≤ L n)
    (hRadLc : 2 * Rad ≤ Lc)
    (hav : (aSeed n : ℝ) ≤ σ n - θ / R n) (hθL : θ ≤ L n ^ 2)
    (hlate : 1 ≤ R n * ((σ n : ℝ) - θ / R n)) :
    ∀ x ∈ riemannianBallOf
        ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
        (Rad / Real.sqrt (R n)),
    ∀ s : ℝ, (σ n : ℝ) - β / R n ≤ s → s < σ n →
      (K n).toHistory.time ((K n).toHistory.activeStage (σ n)) < s →
      Cg * R n < metricScalarAt
        ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s) x →
      GuardKX_C11KX
        (metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)))
        (Cg * R n) Ct (σ n) s x →
      riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s)
          ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
            ((K n).toHistory.activeStage_mono (has n))
            ((K n).toHistory.activeStage_mono (hsT n))) x ≤
        riemannianEDistOf
            ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
            ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
              ((K n).toHistory.activeStage_mono (has n))
              ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / Real.sqrt (R n)) := by
  intro x hx s _ hs2 hts hRx hg
  have hfin : (K n).time (Fin.last (K n).eventCount) < (K n).horizon := hv1.trans hv2
  have hact : (K n).toHistory.activeStage (σ n) = Fin.last (K n).eventCount :=
    (K n).toHistory.activeStage_eq_last_of_time_last_le (σ n) hv1.le
  have hsq : 0 < Real.sqrt (R n) := Real.sqrt_pos.2 hR
  set D0 := riemannianEDistOf
    ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
    ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
      ((K n).toHistory.activeStage_mono (has n))
      ((K n).toHistory.activeStage_mono (hsT n))) (y n) with hD0
  have ktri : ∀ (k : Fin ((K n).eventCount + 1)) (hk : (K n).toHistory.activeStage (σ n) = k)
      (h1' : (K n).toHistory.activeStage (aSeed n) ≤ k)
      (h2' : k ≤ (K n).toHistory.activeStage (Tn n)) (x' yk : ((K n).toHistory.stage k).Carrier),
      HEq (y n) yk →
      x' ∈ riemannianBallOf ((K n).toHistory.stageMetric k (σ n)) yk (Rad / Real.sqrt (R n)) →
      riemannianEDistOf ((K n).toHistory.stageMetric k (σ n)) ((seedTrace n).point k h1' h2') x' ≤
        D0 + ENNReal.ofReal (Rad / Real.sqrt (R n)) := by
    intro k hk
    subst hk
    intro h1' h2' x' yk hy hx'
    obtain rfl := eq_of_heq hy
    exact (riemannianEDistOf_triangle _ _ _ _).trans (add_le_add le_rfl hx'.le)
  have key : ∀ (k : Fin ((K n).eventCount + 1)) (hk : k = Fin.last (K n).eventCount)
      (h1' : (K n).toHistory.activeStage (aSeed n) ≤ k)
      (h2' : k ≤ (K n).toHistory.activeStage (Tn n)) (x' yk : ((K n).toHistory.stage k).Carrier),
      HEq (y n) yk →
      x' ∈ riemannianBallOf ((K n).toHistory.stageMetric k (σ n)) yk (Rad / Real.sqrt (R n)) →
      (K n).toHistory.time k < s →
      Cg * R n < metricScalarAt ((K n).toHistory.stageMetric k s) x' →
      GuardKX_C11KX (metricScalarAt ((K n).toHistory.stageMetric k (σ n))) (Cg * R n) Ct
        (σ n) s x' →
      riemannianEDistOf ((K n).toHistory.stageMetric k s) ((seedTrace n).point k h1' h2') x' ≤
        D0 + ENNReal.ofReal (L n / Real.sqrt (R n)) := by
    intro k hk
    subst hk
    intro h1' h2' x' yk hy hx' hts' _ hg'
    have hxG0 := ktri (Fin.last (K n).eventCount) hact h1' h2' x' yk hy hx'
    simp only [(K n).stageMetric_last_restrict_P6HF hfin] at hxG0 hg' ⊢
    unfold GuardKX_C11KX at hg'
    have hqM : Cg * R n ≤ max (metricScalarAt ((((K n).finalSlab hfin).restrictIncoming le_rfl
        hfin le_rfl).flow.base.metric (σ n)) x') (Cg * R n) :=
      le_max_right _ _
    have hxM : metricScalarAt ((((K n).finalSlab hfin).restrictIncoming le_rfl hfin
        le_rfl).flow.base.metric (σ n)) x' ≤ max (metricScalarAt ((((K n).finalSlab
        hfin).restrictIncoming le_rfl hfin le_rfl).flow.base.metric (σ n)) x') (Cg * R n) :=
      le_max_left _ _
    set M := max (metricScalarAt ((((K n).finalSlab hfin).restrictIncoming le_rfl hfin
      le_rfl).flow.base.metric (σ n)) x') (Cg * R n) with hMdef
    have hM : 0 < M := (mul_pos hCg hR).trans_le hqM
    have hCM : Cg * (M / Cg) = M := by field_simp
    have hRq : R n ≤ M / Cg := by
      rw [le_div_iff₀ hCg]
      linarith
    have hθq : θ / (M / Cg) ≤ θ / R n := div_le_div_of_nonneg_left hθ hR hRq
    have hθR : θ / R n ≤ L n ^ 2 / R n := div_le_div_of_nonneg_right hθL hR.le
    have hwin : (σ n : ℝ) - θ / (M / Cg) ≤ s := by
      have hkey : M * ((σ n : ℝ) - s) ≤ θ * Cg := by
        have h2'' : 2 * (Ct : ℝ) * (M * ((σ n : ℝ) - s)) ≤ 2 * (Ct : ℝ) * (θ * Cg) := by
          have := hg'.trans hθ2
          linarith
        exact le_of_mul_le_mul_left h2'' (by positivity)
      have hdiv : (σ n : ℝ) - s ≤ θ * Cg / M := by
        rw [le_div_iff₀ hM]
        linarith
      rw [div_div_eq_mul_div]
      linarith
    have hlate' : 1 ≤ R n * ((σ n : ℝ) - θ / (M / Cg)) := by
      have := mul_le_mul_of_nonneg_left (sub_le_sub_left hθq (σ n : ℝ)) hR.le
      linarith
    have hxG : riemannianEDistOf ((((K n).finalSlab hfin).restrictIncoming le_rfl hfin
        le_rfl).flow.base.metric (σ n))
        ((seedTrace n).point (Fin.last (K n).eventCount) h1' h2') x' ≤
          D0 + ENNReal.ofReal (Lc / 2 / Real.sqrt (R n)) :=
      hxG0.trans (add_le_add le_rfl (ENNReal.ofReal_le_ofReal
        (div_le_div_of_nonneg_right (by linarith) hsq.le)))
    have hxv : (((K n).finalSlab hfin).restrictIncoming le_rfl hfin le_rfl).flow.scalar (σ n) x' ≤
        Cg * (M / Cg) := by
      rw [hCM]
      exact hxM
    have hav' : (aSeed n : ℝ) ≤ (σ n : ℝ) - θ / (M / Cg) := by linarith
    have hσL : (σ n : ℝ) - L n ^ 2 / R n ≤ (σ n : ℝ) - θ / (M / Cg) := by linarith
    exact RetainedCoreHistory.windowSeed_pointAnchor_final_P6GWF hC2 (K n) hfin (haT n) (hsT n)
      (has n) hsmall hclock (seedTrace n) ha₀ hpin (y n) hR (hgood n) h1' h2'
      (v := (σ n : ℝ)) (q := M / Cg) (Λ := Cg) (β := θ) (C := C) hv2 hRq hCg
      (by rw [hCM]; exact hqM) hbud hC1 hΛC hρC hRr hL hρL hav' le_rfl hσL hlate' x' hxG hxv s
      hwin hs2.le hts'
  exact key ((K n).toHistory.activeStage (σ n)) hact _ _ x (y n) HEq.rfl hx hts hRx hg

/-- **`hseedG`（final，序列版，`_P6GWF`，PROVED，无 binder）**：GUARDWIRE G1 `hseedTopGuarded_seq_P6GW` 的
final 孪生；结论 = GW G2b `hseedG` 槽（guard 常数 `Ct ≥ Ctg`、`Ct > 0`）。常数与 event 同：`θ := 1/(2·Ct·Cg)`、
`C := max (max 1 (6Cg)) (2Cg/ρ_lp(C2)²)`、`Lc := max (2·Rad) (…)`；eventually 条件由 `hwin θ`、`L → ∞`、
`R·r² → ∞`、`R·t → ∞` 给出。前提全部在 GW G2b final 全链原表里，新增只有 `0 ≤ C2`。 -/
theorem hseedG_final_seq_P6GWF {Cg β : ℝ} {Ct : ℝ≥0}
    (K : ℕ → RetainedCoreHistory.{u})
    {Tn aSeed σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {haT : ∀ n, aSeed n ≤ Tn n} {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
    {pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier}
    {seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n)}
    {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R L : ℕ → ℝ} {eps C1 C2 : ℝ}
    {Ctg : ℝ≥0}
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L eps C1 C2 Ctg)
    (hC2 : 0 ≤ C2) {t : ℕ → ℝ}
    (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) (htK : ∀ n, t n < (K n).horizon)
    (hσ : ∀ n, (σ n : ℝ) = t n)
    (hRpos : ∀ n, 0 < R n) (hRt : Tendsto (fun n => R n * t n) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hL : Tendsto L atTop atTop) {r : ℕ → ℝ}
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop) {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ n (τ' : Icc (0 : ℝ) (K n).toHistory.horizon)
      (x : ((K n).toHistory.stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ') τ')
        (a₀ + τ') x)
    (hCg : 0 < Cg) (hCt : 0 < (Ct : ℝ)) (hCtg : (Ctg : ℝ) ≤ Ct) :
    ∀ Rad : ℝ, ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf
          ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
          (Rad / Real.sqrt (R n)),
      ∀ s : ℝ, (σ n : ℝ) - β / R n ≤ s → s < σ n →
        (K n).toHistory.time ((K n).toHistory.activeStage (σ n)) < s →
        Cg * R n < metricScalarAt
          ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s) x →
        GuardKX_C11KX
          (metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)))
          (Cg * R n) Ct (σ n) s x →
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s)
            ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
              ((K n).toHistory.activeStage_mono (has n))
              ((K n).toHistory.activeStage_mono (hsT n))) x ≤
          riemannianEDistOf
              ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) := by
  intro Rad
  have hlpr := localPropagationRadius_pos hC2
  set θ : ℝ := 1 / (2 * (Ct : ℝ) * Cg) with hθdef
  have hθ0 : 0 < θ := by positivity
  have hθ1 : 2 * (Ct : ℝ) * Cg * θ = 1 := mul_one_div_cancel (by positivity)
  have hbud : (Ctg : ℝ) * Cg * θ ≤ 1 / 2 := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCtg hCg.le) hθ0.le
    linarith
  set C : ℝ := max (max 1 (6 * Cg)) (2 * Cg / localPropagationRadius C2 ^ 2) with hCdef
  have hC1 : 1 ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have hΛC : 6 * Cg ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hρC : 2 * Cg ≤ localPropagationRadius C2 ^ 2 * C := by
    have hl2 : 0 < localPropagationRadius C2 ^ 2 := by positivity
    have h := (le_max_right (max 1 (6 * Cg)) (2 * Cg / localPropagationRadius C2 ^ 2))
    rw [← hCdef, div_le_iff₀ hl2] at h
    linarith
  set Lc : ℝ := max (2 * Rad)
    (2 + 16 * Real.sqrt (max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))) * max θ 0)
    with hLcdef
  filter_upwards [hwin θ hθ0, hL.eventually_ge_atTop (max θ 1),
    hL.eventually_ge_atTop (Lc + 2 * (localPropagationRadius C2 / Real.sqrt (2 * Cg))),
    hRr.eventually_ge_atTop (2500 * max 1 (2 * Real.sqrt 3 * (C / 2 + max C (2 * Real.exp 4)))),
    hRt.eventually_ge_atTop (1 + θ)] with n ha hLθ hLc hRrn hRtn
  have hL1 : 1 ≤ L n := (le_max_right θ 1).trans hLθ
  have hθL : θ ≤ L n ^ 2 := by nlinarith [le_max_left θ 1]
  have hRθ : R n * (θ / R n) = θ := by field_simp [(hRpos n).ne']
  have hlate : 1 ≤ R n * ((σ n : ℝ) - θ / R n) := by
    rw [mul_sub, hRθ, hσ n]
    linarith
  have hv1 : (K n).time (Fin.last (K n).eventCount) < σ n := by
    rw [hσ n]
    exact htl n
  have hv2 : ((σ n : ℝ)) < (K n).horizon := by
    rw [hσ n]
    exact htK n
  exact hseedG_final_top_P6GWF K hgood hC2 n (hRpos n) hv1 hv2 (hsmall n) (hclock n) ha₀
    (hpin n) hCg hCt hθ0.le (le_of_eq hθ1.symm) hbud hC1 hΛC hρC hRrn (le_max_right _ _) hLc
    (le_max_left _ _) ha hθL hlate

end SeedGFinal

section FinalChainPointAnchor

/-- **G4 `hdistW_finalSlab_pointAnchor_P6GWF`（`_P6GWF`，PROVISIONAL：binder = GW G2b 原表去
`hseedG`、加 `0 ≤ C2g`；即 `hdepthAF`（⇐ J10GEN2A final）+ `hslabSel`（J10 残余，owner SLTLOCAL）+
final `hkappa` + hgood + FINCOND 层 supplies + K0 / HI + `hR / hRlim` + `C2g ≤ Cgrad` + `0 ≤ C2g`；
**无 hseedTop、无 hseedG**、无 `hqR`）**：GUARDWIRE G2b `hdistW_finalSlab_guarded_P6GW` 的 `hseedG` 由
`hseedG_final_seq_P6GWF`（point-anchor 三核 final 孪生，guard 常数 `Ctime + Ctg + 1`）付。
结论 = final hdistW 槽逐字。 -/
theorem hdistW_finalSlab_pointAnchor_P6GWF :
      ∀ {Ctime : ℝ≥0} {phi : ℝ → ℝ},
      (hphi : Perelman.AdmissiblePinchingFunction phi) →
      {K : ℕ → RetainedCoreHistory.{u}} → {t : ℕ → ℝ} →
      (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) →
      (htK : ∀ n, t n < (K n).horizon) →
      {G : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).IncomingSlab
        ((K n).time (Fin.last (K n).eventCount)) (K n).horizon} →
      (hG : ∀ n, G n = ((K n).finalSlab ((htl n).trans (htK n))).restrictIncoming le_rfl
        ((htl n).trans (htK n)) le_rfl) →
      {D θcap qcan T₀ : ℕ → ℝ} → {p : ℕ → CutoffParameters} → {δb : ℕ → ℝ} →
      {records : ∀ n (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount),
        T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ →
        GeometricCutoffRecord ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i (p n)} →
      {yG : ∀ n, ((K n).stage (Fin.last (K n).eventCount)).Carrier} →
      (hcan : ∀ n i hi b, ((records n i hi).static b).hasCanonicalWindow) →
      (hqcan : ∀ n : ℕ, (n : ℝ) + 1 ≤ qcan n) →
      (hpar : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1) ∧ (n : ℝ) + 1 ≤ D n ∧
        D n ≤ (p n).modelRadius ∧ n + 2 ≤ (p n).modelOrder ∧ δb n ≤ 1 / ((n : ℝ) + 1)) →
      (hscale : ∀ (n : ℕ) i hi b,
        ((n : ℝ) + 1) * qcan n ≤ ((records n i hi).static b).neck.scale) →
      (hθcap : ∀ n : ℕ, 1 - 1 / ((n : ℝ) + 2) ≤ θcap n) →
      (hpinch : ∀ n, (∀ i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount,
          Perelman.PhiAlmostNonnegative
            (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).incoming.flow
            (Ico (((K n).prefixAt (Fin.last (K n).eventCount)).time i.castSucc)
              (((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ) ∩ Ici (T₀ n)) phi) ∧
        Perelman.PhiAlmostNonnegative (G n).flow
          (Ico ((K n).time (Fin.last (K n).eventCount)) (K n).horizon ∩ Ici (T₀ n)) phi) →
      (hnot : ∀ n, ¬ ∃ (i : Fin ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)
        (hi : T₀ n ≤ ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ)
        (hl : i.succ ≤ Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)
        (A : BackwardPointTrace ((K n).prefixAt (Fin.last (K n).eventCount)).toHistory i.succ
          (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount) hl (yG n))
        (b : (((K n).prefixAt (Fin.last (K n).eventCount)).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((records n i hi).static b).window x ∧ ‖x.val‖ < D n + 1 ∧
          t n - ((K n).prefixAt (Fin.last (K n).eventCount)).time i.succ ≤
            θcap n * (((records n i hi).static b).neck.scale)⁻¹) →
      (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤
        t n - B / (G n).flow.scalar (t n) (yG n)) →
      (hRt : Tendsto (fun n => (G n).flow.scalar (t n) (yG n) *
        t n) atTop atTop) →
      {β : ℝ} → (hβ : 0 < β) →
      (hβ2 : β ≤ 1 / 2) →
      (Kh : ℕ → ObservedHistory.{u}) → (hKh : Kh = fun n => (K n).toHistory) →
      (σ : ∀ n, Icc (0 : ℝ) (Kh n).horizon) → (y : ∀ n, ((Kh n).stageAt (σ n)).Carrier) →
      (R : ℕ → ℝ) → (hσ : ∀ n, (σ n : ℝ) = t n) → (hyG : ∀ n, HEq (y n) (yG n)) →
      (hRn : ∀ n, R n = (G n).flow.scalar (t n) (yG n)) →
      (hR : ∀ n, 0 < R n) → (hRlim : Tendsto R atTop atTop) →
      {κ : ℝ} → (hκ : 0 < κ) → (ρnc : ℕ → ℝ) →
      (hradii : Tendsto (fun n => ρnc n * Real.sqrt (R n)) atTop atTop) →
      (hkappa : ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (D / Real.sqrt (R n)),
        ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hvt : v ≤ σ n), (σ n : ℝ) - T / R n ≤ v →
        ∀ tr : BackwardPointTrace (Kh n) ((Kh n).activeStage v) ((Kh n).activeStage (σ n))
          ((Kh n).activeStage_mono hvt) x,
        ∀ r'' : ℝ, 0 < r'' → r'' ≤ ρnc n →
          (Kh n).isParabolicallyRmControlledBall v
            (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'' →
          ENNReal.ofReal (κ * r'' ^ 3) ≤
            Geometry.Collapse.ballVolume ((Kh n).stageMetric ((Kh n).activeStage v) v)
              (tr.point ((Kh n).activeStage v) le_rfl ((Kh n).activeStage_mono hvt)) r'') →
      (hdepthAF : (∀ A : ℝ, 0 < A → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
          ∀ z ∈ riemannianBallOf ((G n).flow.base.metric (t n)) (yG n)
              (A / Real.sqrt ((G n).flow.scalar (t n) (yG n))),
            (G n).flow.scalar (t n) z ≤ Q * (G n).flow.scalar (t n) (yG n)) →
        ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          ∀ T : ℝ, 0 < T → ObservedHistory.DepthExtendable Kh σ y R (φ ∘ ψ) T) →
      ∀ (Tn aSeed : ∀ n, Icc (0 : ℝ) (Kh n).horizon) (haT : ∀ n, aSeed n ≤ Tn n)
        (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
        (pT : ∀ n, ((Kh n).stageAt (Tn n)).Carrier)
        (seedTrace : ∀ n, BackwardPointTrace (Kh n) ((Kh n).activeStage (aSeed n))
          ((Kh n).activeStage (Tn n)) ((Kh n).activeStage_mono (haT n)) (pT n))
      (L : ℕ → ℝ) (r : ℕ → ℝ),
      ∀ {Cg εg C1g C2g : ℝ} {Ctg : ℝ≥0}, 0 < Cg → εg ≤ coneAccuracy →
      ObservedHistory.HgoodCg_C11SH Cg Kh Tn aSeed σ haT hsT has pT seedTrace y R L εg C1g C2g
        Ctg →
      (∀ n, ((K n).prefixAt (Fin.last (K n).eventCount)).EventSlabsDerivative Ctime (Cg * R n)
        (Fin.last ((K n).prefixAt (Fin.last (K n).eventCount)).eventCount)) →
      ∀ {Cgrad : ℝ≥0}, C2g ≤ (Cgrad : ℝ) →
      0 ≤ C2g →
      Tendsto L atTop atTop →
      (∀ n, GC.LongTime.hasSmallParabolicCurvature (Kh n) (Tn n) (pT n) (r n)) →
      (∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2) →
      Tendsto (fun n => R n * r n ^ 2) atTop atTop →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n) →
      ∀ {a₁ : ℝ}, 0 ≤ a₁ →
      (∀ n (τ' : Icc (0 : ℝ) (Kh n).horizon) (x : ((Kh n).stageAt τ').Carrier),
        InFixedHamiltonIveyRegion ((Kh n).stageMetric ((Kh n).activeStage τ') τ') (a₁ + τ') x) →
      ∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (Kh n).horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
        (Kh n).activeStage v = (Kh n).activeStage (σ n) →
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
  intro Ctime phi hphi K t htl htK G hG D θcap qcan T₀ p δb records yG hcan hqcan hpar hscale hθcap
    hpinch hnot hT₀ hRt β hβ hβ2 Kh hKh σ y R hσ hyG hRn hR hRlim κ hκ ρnc hradii hkappa hdepthAF
    Tn aSeed haT hsT has pT seedTrace L r Cg εg C1g C2g Ctg hCg hεg hgood hslabSel Cgrad hC2
    hC20 hL hsmall hclock hRr hwin a₁ ha₁ hpin
  subst hKh
  have hRt' : Tendsto (fun n => R n * t n) atTop atTop := hRt.congr fun n => by rw [hRn n]
  have hCt : (0 : ℝ) < ((Ctime + Ctg + 1 : ℝ≥0) : ℝ) := by positivity
  have hCtg : (Ctg : ℝ) ≤ ((Ctime + Ctg + 1 : ℝ≥0) : ℝ) := by
    push_cast
    linarith [Ctime.coe_nonneg]
  exact hdistW_finalSlab_guarded_P6GW hphi htl htK hG hcan hqcan hpar hscale hθcap hpinch hnot hT₀
    hRt hβ hβ2 (fun n => (K n).toHistory) rfl σ y R hσ hyG hRn hR hRlim hκ ρnc hradii hkappa
    hdepthAF Tn aSeed haT hsT has pT seedTrace L r hCg hεg hgood hslabSel hC2
    (hseedG_final_seq_P6GWF (β := β) K hgood hC20 htl htK hσ hR hRt' hwin hL hsmall hclock hRr ha₁
      hpin hCg hCt hCtg) hL hsmall hclock hRr hwin ha₁ hpin

end FinalChainPointAnchor

/-- consumer（event 实例，`_P6GWF`）：event 支 point-anchor（WSBASE `windowSeed_pointAnchor_C11WB`，经 GW
`hseedTopGuarded_seq_P6GW`）在 GW G2 event 链实际用的 guard 常数 `Ctime + Ctg + 1` 处给 hseedTop 的
guarded 替代物；前提表 = point-anchor 完整前提（hgood、seed、pinching、窗口、预算、`Lc/L` 裕量）+ `0 ≤ C2`。 -/
example {Cg β : ℝ} {Ctime : ℝ≥0}
    (K : ℕ → RetainedCoreHistory.{u})
    {Tn aSeed σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {haT : ∀ n, aSeed n ≤ Tn n} {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
    {pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier}
    {seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n)}
    {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R L : ℕ → ℝ} {eps C1 C2 : ℝ}
    {Ctg : ℝ≥0}
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L eps C1 C2 Ctg)
    (hC2 : 0 ≤ C2)
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    {yG : ∀ n, ((K n).stage (j n).castSucc).Carrier}
    (hσ : ∀ n, (σ n : ℝ) = t n) (hyG : ∀ n, HEq (y n) (yG n))
    (hRn : ∀ n, R n = ((K n).toHistory.event (j n)).incoming.flow.scalar (t n) (yG n))
    (hRpos : ∀ n, 0 < R n) (hRt : Tendsto (fun n => R n * t n) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hL : Tendsto L atTop atTop) {r : ℕ → ℝ}
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop) {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ n (τ' : Icc (0 : ℝ) (K n).toHistory.horizon)
      (x : ((K n).toHistory.stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ') τ')
        (a₀ + τ') x)
    (hCg : 0 < Cg) :
    ∀ Rad : ℝ, ∀ᶠ n in atTop,
      ∀ (h1 : (K n).toHistory.activeStage (aSeed n) ≤ (j n).castSucc)
        (h2 : (j n).castSucc ≤ (K n).toHistory.activeStage (Tn n)),
      PickedBallWindowSeedGuarded_P6GW β Rad (Cg * R n) (Ctime + Ctg + 1) (K n) (j n) (t n) (yG n)
        ((seedTrace n).point (j n).castSucc h1 h2)
        (riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
            ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
              ((K n).toHistory.activeStage_mono (has n))
              ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
          ENNReal.ofReal (L n / Real.sqrt (R n))) :=
  hseedTopGuarded_seq_P6GW K hgood hC2 hjt htj hσ hyG hRn hRpos hRt hwin hL hsmall hclock hRr
    ha₀ hpin hCg (by positivity) (by push_cast; linarith [Ctime.coe_nonneg])

/-- consumer（final 实例，`_P6GWF`）：final 支 point-anchor（本文件 `windowSeed_pointAnchor_final_P6GWF`，经
`hseedG_final_seq_P6GWF`）在 GW G2b final 链的 guard 常数 `Ctime + Ctg + 1` 处给出 `hseedG` 槽逐字；前提表与
event 实例逐项同形（`j` → `Fin.last`，`hjt / htj` → `htl / htK`；无 `hyG / hRn`）。 -/
example {Cg β : ℝ} {Ctime : ℝ≥0}
    (K : ℕ → RetainedCoreHistory.{u})
    {Tn aSeed σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon}
    {haT : ∀ n, aSeed n ≤ Tn n} {hsT : ∀ n, σ n ≤ Tn n} {has : ∀ n, aSeed n ≤ σ n}
    {pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier}
    {seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n)}
    {y : ∀ n, ((K n).toHistory.stageAt (σ n)).Carrier} {R L : ℕ → ℝ} {eps C1 C2 : ℝ}
    {Ctg : ℝ≥0}
    (hgood : ObservedHistory.HgoodCg_C11SH Cg (fun n => (K n).toHistory) Tn aSeed σ haT hsT has pT
      seedTrace y R L eps C1 C2 Ctg)
    (hC2 : 0 ≤ C2) {t : ℕ → ℝ}
    (htl : ∀ n, (K n).time (Fin.last (K n).eventCount) < t n) (htK : ∀ n, t n < (K n).horizon)
    (hσ : ∀ n, (σ n : ℝ) = t n)
    (hRpos : ∀ n, 0 < R n) (hRt : Tendsto (fun n => R n * t n) atTop atTop)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, (aSeed n : ℝ) ≤ σ n - T / R n)
    (hL : Tendsto L atTop atTop) {r : ℕ → ℝ}
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop) {a₀ : ℝ} (ha₀ : 0 ≤ a₀)
    (hpin : ∀ n (τ' : Icc (0 : ℝ) (K n).toHistory.horizon)
      (x : ((K n).toHistory.stageAt τ').Carrier),
      InFixedHamiltonIveyRegion ((K n).toHistory.stageMetric ((K n).toHistory.activeStage τ') τ')
        (a₀ + τ') x)
    (hCg : 0 < Cg) :
    ∀ Rad : ℝ, ∀ᶠ n in atTop,
      ∀ x ∈ riemannianBallOf
          ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)) (y n)
          (Rad / Real.sqrt (R n)),
      ∀ s : ℝ, (σ n : ℝ) - β / R n ≤ s → s < σ n →
        (K n).toHistory.time ((K n).toHistory.activeStage (σ n)) < s →
        Cg * R n < metricScalarAt
          ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s) x →
        GuardKX_C11KX
          (metricScalarAt ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n)))
          (Cg * R n) ((Ctime + Ctg + 1 : ℝ≥0) : ℝ) (σ n) s x →
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) s)
            ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
              ((K n).toHistory.activeStage_mono (has n))
              ((K n).toHistory.activeStage_mono (hsT n))) x ≤
          riemannianEDistOf
              ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n))
                ((K n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / Real.sqrt (R n)) :=
  hseedG_final_seq_P6GWF K hgood hC2 htl htK hσ hRpos hRt hwin hL hsmall hclock hRr ha₀ hpin hCg
    (by positivity) (by push_cast; linarith [Ctime.coe_nonneg])

/-- consumer（G4，`_P6GWF`）：final 全链（无 hseedTop / hseedG）。 -/
example := @hdistW_finalSlab_pointAnchor_P6GWF.{u}

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
