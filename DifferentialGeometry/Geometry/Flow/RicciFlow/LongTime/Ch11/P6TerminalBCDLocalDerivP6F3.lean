import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6TerminalBCDLocalP6F3

/-!
# BCDT 局域 `hderivL` 的 ∂ₜ 分量 ⇐ hgood 时间分量 + `hstayΩ`（O-CH11-FOOT3 G3，后缀 `_P6F3`）

R-C11-15 D-7："hderiv 改为 Ω_k 内 R > Cg·R_k 的 hgood 时间分量形"。本文件证明 G2 的 `hderivL`
（`Cg = 4`、`Cder = Ctime`）可由 selected-family 前缀里的 `hgood`（`HasSpatialCanonicalTimeControl` 的
时间分量）加一条距离合同 `hstayΩ` 得到：
* `ObservedHistory.deriv_incoming_of_hgood_P6F3`（PROVED，单点核）：slab `i` 内部时刻 `v`、点
  `x ∈ stage i⁻`，`(stageAt v)` 中与 `x` HEq 的点满足 HSCTC ⇒ incoming flow 形的
  `|∂ₜR(·, x)| ≤ Ctime·R²`（slab 桥：`stageMetric_castSucc_apply` + `activeStage` 在 slab 内部 = `i⁻`）。
* `ObservedHistory.deriv_incoming_of_hgood_stay_P6F3`（PROVED）：单点核 ∘ hgood（距离由 `hstay` 给，
  `σ − L²/R ≤ a ≤ v′ ≤ b ≤ σ`、阈值 `4R < R(v′, x)`）。
* **`hderivL_of_hgood_P6F3`**（PROVISIONAL，binder `hstayΩ`）：结论 = G2 `hderivL` binder 逐字（`Cg := 4`，
  `Cder := Ctime`）。早先 slab 合取用 `hstayΩ` 在 trace 点上；当前 slab 合取用 singleton trace。
**`hstayΩ`（距离合同）与 J10T0 / CXJT0 的差异**（lead 要求逐字相同，否则写出差异）：
* 内容相同：trace 点在使用时刻 `v` 落在 selected 邻域 Ω_k，即
  `d_v(seedTrace(v), ·) ≤ d_σ(seedTrace(σ), y) + L/√R`，与 CXJT0
  `timeFootprint_of_hgood_stopped_CXJT0` 的单 n `hstop` 体逐字同一不等式（左右两边逐字）。
* 索引不同：`hstop` 对固定 `(a, t)` 与 activeStage 索引的 trace `A : activeStage a → activeStage t`
  量化 `A.point (activeStage v)`；BCDT 消费端（P6WB `hslabs`）的 trace 是 event 索引
  `B : first → (i k)⁻`，时刻在 incoming slab 内（`v < σ = time (i k).succ`），故 `hstayΩ` 量化
  `∀ U_t 点 z、∀ B、∀ m（first ≤ m ≤ (i k)⁻）、∀ v ∈ [t − T/R_k, t]`（`activeStage v = m`）、
  `∀ zz HEq B.point m`。
* CXJT0 序列形 `hdistW`（= P6CD `hgrad_of_selection_sameSlab_Cg_P6CD` 的 `hdistW`）带
  `activeStage v = activeStage σ`，指 σ 所在（event 之后的）slab；BCDT 窗口在 event 之前的 incoming
  slab，序列形 `hdistW` 不适用（`v < σ` 时同 slab 条件只剩 `v = σ`）。
非循环：只用前缀里的 `hgood`、`haS`、`hL`；不含 HU / hclosG / hscalU / CanonicalLateCore / hspine /
`hderivKC` / 全局 `EventSlabsDerivative`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn

/-- `l = m` 的 stage 之间取 HEq 代表。 -/
private theorem exists_heq_of_stage_eq_P6F3 (H : ObservedHistory.{u})
    {l m : Fin (H.eventCount + 1)} (h : l = m) (x : (H.stage l).Carrier) :
    ∃ z : (H.stage m).Carrier, HEq z x := by
  subst h
  exact ⟨x, HEq.rfl⟩

/-- 标量 `stageMetric m` ↔ incoming（`m = i⁻`）。 -/
private theorem scalar_of_stage_P6F3 (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    {m : Fin (H.eventCount + 1)} (hm : i.castSucc = m) (v : ℝ)
    (x : (H.stage i.castSucc).Carrier) (z : (H.stage m).Carrier) (hz : HEq z x) :
    metricScalarAt (H.stageMetric m v) z = (H.event i).incoming.flow.scalar v x := by
  subst hm
  obtain rfl := eq_of_heq hz
  rw [ObservedHistory.stageMetric_castSucc_apply]
  rfl

/-- 时间导数 `stageMetric m` → incoming（`m = i⁻`）。 -/
private theorem deriv_of_stage_P6F3 (H : ObservedHistory.{u}) (i : Fin H.eventCount)
    {m : Fin (H.eventCount + 1)} (hm : i.castSucc = m) (v : ℝ) (Ctime : ℝ≥0)
    (x : (H.stage i.castSucc).Carrier) (z : (H.stage m).Carrier) (hz : HEq z x)
    (h : |derivWithin (fun t => metricScalarAt (H.stageMetric m t) z) (Iic v) v| ≤
      Ctime * metricScalarAt (H.stageMetric m v) z ^ 2) :
    |derivWithin (fun w => (H.event i).incoming.flow.scalar w x) (Iic v) v| ≤
      Ctime * (H.event i).incoming.flow.scalar v x ^ 2 := by
  subst hm
  obtain rfl := eq_of_heq hz
  simp only [ObservedHistory.stageMetric_castSucc_apply] at h
  exact h

/-- slab 内部时刻的 `activeStage`（ObservedHistory 版）。 -/
theorem ObservedHistory.activeStage_eq_of_mem_slab_P6F3 (H : ObservedHistory.{u})
    (j : Fin H.eventCount) (τ : Icc (0 : ℝ) H.horizon)
    (h1 : H.time j.castSucc ≤ τ) (h2 : (τ : ℝ) < H.time j.succ) :
    H.activeStage τ = j.castSucc :=
  (H.mem_stageDomain_iff τ j.castSucc).mp (by
    simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using
      (show (τ : ℝ) ∈ Ico (H.time j.castSucc) (H.time j.succ) from ⟨h1, h2⟩))

/-- **单点核（PROVED，`_P6F3`）**：slab `i` 内部时刻 `v`、`x ∈ stage i⁻`；`stageAt v` 中与 `x` HEq 且
标量 `≥ q` 的点满足 HSCTC，且 `q ≤ R(v, x)` ⇒ incoming flow 形 `|∂ₜR(·, x)| ≤ Ctime·R²`。 -/
theorem ObservedHistory.deriv_incoming_of_hgood_P6F3 {eps C1 C2 : ℝ} {Ctime : ℝ≥0}
    (H : ObservedHistory.{u}) (i : Fin H.eventCount) (x : (H.stage i.castSucc).Carrier)
    (v : Icc (0 : ℝ) H.horizon) (hv1 : H.time i.castSucc < v) (hv2 : (v : ℝ) < H.time i.succ)
    {q : ℝ} (hq : q ≤ (H.event i).incoming.flow.scalar v x)
    (hctl : ∀ zz : (H.stageAt v).Carrier, HEq zz x →
      q ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) zz →
      H.HasSpatialCanonicalTimeControl eps C1 C2 Ctime v zz) :
    |derivWithin (fun w => (H.event i).incoming.flow.scalar w x) (Iic (v : ℝ)) v| ≤
      Ctime * (H.event i).incoming.flow.scalar v x ^ 2 := by
  have hact : H.activeStage v = i.castSucc := H.activeStage_eq_of_mem_slab_P6F3 i v hv1.le hv2
  obtain ⟨zz, hzz⟩ := exists_heq_of_stage_eq_P6F3 H hact.symm x
  have hsc := scalar_of_stage_P6F3 H i hact.symm (v : ℝ) x zz hzz
  have hctl' := hctl zz hzz (by rw [hsc]; exact hq)
  have hd := hctl'.2 (by rw [hact]; exact hv1) (hv2.trans_le (H.time_le_horizon_at _))
  exact deriv_of_stage_P6F3 H i hact.symm (v : ℝ) Ctime x zz hzz hd

/-- **单点核 ∘ hgood（PROVED，`_P6F3`）**：hgood（单条 history，阈值 `4R`）+ `hstay`（`[a, b]` 内、
`activeStage v = i⁻` 的时刻，与 `x` HEq 的点在 Ω 内）+ `σ − L²/R ≤ a ≤ v′ ≤ b ≤ σ`、`aSeed ≤ a`、
`4R < R(v′, x)` ⇒ incoming flow 形 `|∂ₜR(·, x)| ≤ Ctime·R²`。 -/
theorem ObservedHistory.deriv_incoming_of_hgood_stay_P6F3 {eps C1 C2 : ℝ} {Ctime : ℝ≥0}
    (H : ObservedHistory.{u}) {Tn aSeed σ : Icc (0 : ℝ) H.horizon} (haT : aSeed ≤ Tn)
    (hsT : σ ≤ Tn) (has : aSeed ≤ σ) {p : (H.stageAt Tn).Carrier}
    (seedTrace : BackwardPointTrace H (H.activeStage aSeed) (H.activeStage Tn)
      (H.activeStage_mono haT) p)
    (y : (H.stageAt σ).Carrier) (R L : ℝ)
    (hgood : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      (σ : ℝ) - L ^ (2 : ℕ) / R ≤ (v : ℝ) →
      ∀ z : (H.stageAt v).Carrier,
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono (hvs.trans hsT))) z ≤
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
              (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                (H.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt R) →
        4 * R ≤ metricScalarAt (H.stageMetric (H.activeStage v) v) z →
        H.HasSpatialCanonicalTimeControl eps C1 C2 Ctime v z)
    (i : Fin H.eventCount) (x : (H.stage i.castSucc).Carrier) (a b v' : ℝ)
    (hv1 : H.time i.castSucc < v') (hv2 : v' < H.time i.succ) (hav' : a ≤ v') (hvb : v' ≤ b)
    (haS : (aSeed : ℝ) ≤ a) (hbσ : b ≤ σ) (haL : (σ : ℝ) - L ^ (2 : ℕ) / R ≤ a)
    (hthr : 4 * R < (H.event i).incoming.flow.scalar v' x)
    (hstay : ∀ (v : Icc (0 : ℝ) H.horizon) (hav : aSeed ≤ v) (hvs : v ≤ σ),
      a ≤ (v : ℝ) → (v : ℝ) ≤ b → H.activeStage v = i.castSucc →
      ∀ zz : (H.stageAt v).Carrier, HEq zz x →
        riemannianEDistOf (H.stageMetric (H.activeStage v) v)
            (seedTrace.point (H.activeStage v) (H.activeStage_mono hav)
              (H.activeStage_mono (hvs.trans hsT))) zz ≤
          riemannianEDistOf (H.stageMetric (H.activeStage σ) σ)
              (seedTrace.point (H.activeStage σ) (H.activeStage_mono has)
                (H.activeStage_mono hsT)) y +
            ENNReal.ofReal (L / Real.sqrt R)) :
    |derivWithin (fun w' => (H.event i).incoming.flow.scalar w' x) (Iic v') v'| ≤
      Ctime * (H.event i).incoming.flow.scalar v' x ^ 2 := by
  have hv0 : 0 ≤ v' := (H.time_nonneg _).trans hv1.le
  have hvH : v' ≤ H.horizon := hv2.le.trans (H.time_le_horizon_at _)
  let v : Icc (0 : ℝ) H.horizon := ⟨v', hv0, hvH⟩
  have hav : aSeed ≤ v := show (aSeed : ℝ) ≤ v' from haS.trans hav'
  have hvs : v ≤ σ := show v' ≤ (σ : ℝ) from hvb.trans hbσ
  have hact : H.activeStage v = i.castSucc := H.activeStage_eq_of_mem_slab_P6F3 i v hv1.le hv2
  exact H.deriv_incoming_of_hgood_P6F3 i x v hv1 hv2 hthr.le
    (fun zz hzz hq4 => hgood v hav hvs (haL.trans hav') zz
      (hstay v hav hvs hav' hvb hact zz hzz) hq4)

/-- **`hderivL` ⇐ hgood + `hstayΩ`（PROVISIONAL，`_P6F3`）**：结论 = G2 `hderivL` binder 逐字
（`Cg := 4`、`Cder := Ctime`）；binder `hstayΩ`（与 CXJT0 `hstop` 的差异见文件头）。 -/
theorem hderivL_of_hgood_P6F3 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hstayΩ :
      ∀ (T r : ℝ), 0 < T → 0 < r →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
            ∀ (first : Fin ((Kh k).eventCount + 1)) (hfl : first ≤ (i k).castSucc),
            ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                (r / Real.sqrt (R k)),
            ∀ (B : BackwardPointTrace (Kh k) first (i k).castSucc hfl z)
              (m : Fin ((Kh k).eventCount + 1)) (hf : first ≤ m) (hm : m ≤ (i k).castSucc)
              (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
              t - T / R k ≤ (v : ℝ) → (v : ℝ) ≤ t → (Kh k).activeStage v = m →
            ∀ zz : ((Kh k).stageAt v).Carrier, HEq zz (B.point m hf hm) →
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) zz ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k))) :
      ∀ (T r : ℝ), 0 < T → 0 < r →
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k),
        let Kh : ℕ → ObservedHistory.{u} := fun k =>
          ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory
        ∀ (Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier),
          (∀ k : ℕ, (k : ℝ) + 1 ≤ c k * (Tn k : ℝ)) →
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
        ∀ i : ∀ k, Fin (Kh k).eventCount, (∀ k, (σ k : ℝ) = (Kh k).time (i k).succ) →
        ∀ᶠ k in atTop, ∀ (p' : ((Kh k).stage (i k).castSucc).Carrier)
          (q : ((Kh k).stage (i k).succ).Carrier), HEq (y k) q →
          ((Kh k).event (i k)).RegularCrossing p' q →
          ∀ᶠ t in 𝓝[<] (Kh k).time (i k).succ,
            (∀ (first : Fin ((Kh k).eventCount + 1)) (hfl : first ≤ (i k).castSucc),
              ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                  (r / Real.sqrt (R k)),
              ∀ (B : BackwardPointTrace (Kh k) first (i k).castSucc hfl z)
                (i' : Fin (Kh k).eventCount) (hf : first ≤ i'.castSucc)
                (hij : i'.castSucc < (i k).castSucc),
              ∀ v' ∈ Ioo ((Kh k).time i'.castSucc) ((Kh k).time i'.succ), t - T / R k ≤ v' →
                4 * R k < ((Kh k).event i').incoming.flow.scalar v'
                  (B.point i'.castSucc hf hij.le) →
                |derivWithin (fun w' => ((Kh k).event i').incoming.flow.scalar w'
                    (B.point i'.castSucc hf hij.le)) (Iic v') v'| ≤
                  Ctime * ((Kh k).event i').incoming.flow.scalar v'
                    (B.point i'.castSucc hf hij.le) ^ 2) ∧
            ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                (r / Real.sqrt (R k)),
              ∀ v' ∈ Ioo ((Kh k).time (i k).castSucc) t, t - T / R k ≤ v' →
                4 * R k < ((Kh k).event (i k)).incoming.flow.scalar v' z →
                |derivWithin (fun w' => ((Kh k).event (i k)).incoming.flow.scalar w' z)
                    (Iic v') v'| ≤
                  Ctime * ((Kh k).event (i k)).incoming.flow.scalar v' z ^ 2 := by
  intro T r hT hr ind c hc Kh Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L hRdef
    hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi
  have hst := hstayΩ T r hT hr
    ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L
    hRdef hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi
  have h2T : (0 : ℝ) < 2 * T := by positivity
  filter_upwards [hst, hL.eventually_ge_atTop (2 * T + 1), haS (2 * T) h2T] with k hsk hLk haSk
  intro p' q hq hcross
  have hRk := hRpos k
  have hσs : (σ k : ℝ) = (Kh k).time (i k).succ := hi k
  have hcs : (Kh k).time (i k).castSucc < (Kh k).time (i k).succ :=
    (Kh k).time_strictMono Fin.castSucc_lt_succ
  have hTR : 0 < T / R k := div_pos hT hRk
  have hL2 : 2 * T / R k ≤ L k ^ (2 : ℕ) / R k := by
    refine div_le_div_of_nonneg_right ?_ hRk.le
    nlinarith [mul_le_mul hLk hLk (by linarith) (by linarith)]
  have h2TR : 2 * T / R k = T / R k + T / R k := by ring
  filter_upwards [hsk p' q hq hcross, Ioo_mem_nhdsLT (show max ((Kh k).time (i k).castSucc)
      ((Kh k).time (i k).succ - T / R k) < (Kh k).time (i k).succ from max_lt hcs (by linarith))]
    with t hstt ht
  have ht1 : (Kh k).time (i k).castSucc < t := lt_of_le_of_lt (le_max_left _ _) ht.1
  have ht2 : (Kh k).time (i k).succ - T / R k < t := lt_of_le_of_lt (le_max_right _ _) ht.1
  have haA : (aSeed k : ℝ) ≤ t - T / R k := by linarith
  have hbσ : t ≤ (σ k : ℝ) := by linarith [ht.2]
  have haL : (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ t - T / R k := by linarith
  refine ⟨?_, ?_⟩
  · intro first hfl z hz B i' hf hij v' hv' hwin hRv'
    have hsi : i'.succ ≤ (i k).castSucc := by
      rw [Fin.le_def]
      have h := Fin.lt_def.mp hij
      simp only [Fin.val_succ, Fin.val_castSucc] at h ⊢
      omega
    have hlt : v' < t :=
      lt_of_lt_of_le hv'.2 (((Kh k).time_strictMono.monotone hsi).trans ht1.le)
    exact (Kh k).deriv_incoming_of_hgood_stay_P6F3 (haT k) (hsT k) (has k) (seedTrace k) (y k)
      (R k) (L k) (hgood k) i' (B.point i'.castSucc hf hij.le) (t - T / R k) t v' hv'.1 hv'.2
      hwin hlt.le haA hbσ haL hRv' (hstt first hfl z hz B i'.castSucc hf hij.le)
  · intro z hz v' hv' hwin hRv'
    exact (Kh k).deriv_incoming_of_hgood_stay_P6F3 (haT k) (hsT k) (has k) (seedTrace k) (y k)
      (R k) (L k) (hgood k) (i k) z (t - T / R k) t v' hv'.1 (hv'.2.trans ht.2) hwin hv'.2.le
      haA hbσ haL hRv'
      (hstt (i k).castSucc le_rfl z hz (BackwardPointTrace.singleton (Kh k) (i k).castSucc z)
        (i k).castSucc le_rfl le_rfl)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
