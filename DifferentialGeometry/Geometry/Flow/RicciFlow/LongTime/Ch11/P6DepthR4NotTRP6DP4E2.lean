import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DepthR4AssembleP6DP4E
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DepthR4DiagP6DP4E2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6BCDBootstrapBallP6BB
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDAlignCrossP6SB2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6StageStabP6ST
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Local.AdapterAgeRecord_P6M

/-!
# 深度归纳期 4 / R4 E2a′（O-CH11-DEPTH4E2，后缀 `_P6DP4E2`）：hTR 合同否定 ⇒ 对角族上的 R4 中心

BCDBOOT hTR 合同按 `∀ T r, 0 < T → 0 < r → ∃ Kt, 0 ≤ Kt ∧ BODY(Kt)` 的量词序使用。`BODY` 是
`P6BCDBootstrapBallP6BB:601–641`（`hgridTr_of_tracedRegion_P6BB` 的 `hTR` 前提）的逐字内联，只把
`Ktr r T * R k` 换成 `Kt * R k`（生成器 `build-logs/scratch/O-CH11-DEPTH4E2/gen/common.py` 带 sha256 断言：
源段 :600–641 = 743f7edc…e8d1，与 :949–990 逐字相同；换后 body = d2de7b2f…601e）。不另立 def / Prop。

* `exists_R4_center_family_of_notTR_P6DP4E2`（PROVED，相对已登记环境前提）：固定 `(T, r)`，若对每个
  `m : ℕ` 都有 `¬ BODY(m)`，则依次做：
  - 推开否定：`simp only [not_forall, Filter.not_eventually, exists_prop]`，再 `choose` 出 31 个
    分量（ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L hRdef hRpos hRr hL
    hsel hgood haS hTnS hroom hradii i hi hbad）；
  - 对角：`exists_diag_pick_P6DP4E2`，其中 E = {haS, hTnS}，Fd = {L ≥ T+1, R(σ−(Tn−½)) ≥ T, √R/200 ≥ T,
    塔帧 hsepWK 在 `C = 1`、event `i k` 处}；
  - 调 E1 `exists_R4_center_family_P6DP4E`：Bad 并入 crossing 见证、slab 成员、中心可比性
    `R/2 < R(t, y′) < 2R`（`eventually_centerScalar_lt_of_regularCrossing_P6SB2` 与本文件下界孪生
    `eventually_centerScalar_gt_of_regularCrossing_P6DP4E2`，与坏时刻 `∃ᶠ` 相交）。
  得到对角族（仍满足 hTR 前缀）+ R4 中心 `(pm, t, y′)` + R4 帧事实 + 坏性 `¬TR(k·R)`，以 CPS 形交给
  `hcont`（其前缀 = hTR 前缀逐字 + R4 中心数据；也是 E2b 中 driver binder 的 R4 帧闭合前缀）。
  环境前提：塔 records（CXSP `exists_records_of_prepared_chain_CXSP` 形）、全部 static cap 的
  canonical window、`pF` 的精度 / 阶 / 半径、以及**塔帧 hsepWK**（(SEP-ρ)，owner HNOT-LOCALDT；对 hTR
  前缀全称闭合，先例 = KAPPA-ADAPT `hkappaC_tower_of_fresh_P6KA` 的环境前提）。hOld 由 records 字段
  `old_eq_retained` 给出；两端标量由 hsepWK 经 `scalar_lt_half_scale_of_sep*`、
  `towerScale_eq_output_P6SB2`、`seed_scalar_le_of_smallParabolic_C11G` 给出。
* `false_of_depthExtendable_of_bad_P6DP4E2`（PROVED，K₀ 收尾）：driver 子列上的 `DepthExtendable` 在
  `A := r` 处给出 `K₀`，与 `¬TR(n·R)` 在 `σ i ≥ ⌈K₀⌉` 处用 `isTracedRegion.mono_bound` 相矛盾。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **crossing 中心标量的 terminal 连续性，下界孪生（`_P6DP4E2`，PROVED）**：
`eventually_centerScalar_lt_of_regularCrossing_P6SB2` 的对称形：`C < R_out(q)` ⇒ `t ↑ time i⁺` 时
`stageAt t` 中与 `p′` HEq 的点标量 `> C`（供 R4 中心 `R(t, y′) > R/2 > 0`，即 hanchor0 产出所需的 `hRc`）。 -/
theorem eventually_centerScalar_gt_of_regularCrossing_P6DP4E2 (H : ObservedHistory.{u})
    (i : Fin H.eventCount) {p' : (H.stage i.castSucc).Carrier} {q : (H.stage i.succ).Carrier}
    (hcross : (H.event i).RegularCrossing p' q) {C : ℝ}
    (hC : C < metricScalarAt (H.event i).outputMetric q) :
    ∀ᶠ t in 𝓝[<] H.time i.succ, ∀ (tt : Icc (0 : ℝ) H.horizon), (tt : ℝ) = t →
      ∀ y' : (H.stageAt tt).Carrier, HEq y' p' →
        C < metricScalarAt (H.stageMetric (H.activeStage tt) tt) y' := by
  have hp : p' ∈ (H.event i).incoming.terminalRegularOpen :=
    hcross.mem_terminalRegularRegion (H.event i)
  have h := (H.event i).terminal.tendsto_metricScalarAt ⟨p', hp⟩
  rw [MetricCutCapEvent.RegularCrossing.scalar_eq (H.event i) (p := ⟨p', hp⟩) hcross] at h
  have hev := h.eventually (lt_mem_nhds hC)
  have hIoo : Ioo (H.time i.castSucc) (H.time i.succ) ∈ 𝓝[<] H.time i.succ :=
    Ioo_mem_nhdsLT (H.time_strictMono i.castSucc_lt_succ)
  filter_upwards [hev, hIoo] with t ht hts
  intro tt htt y' hy'
  have hact : H.activeStage tt = i.castSucc :=
    (H.mem_stageDomain_iff tt i.castSucc).mp (by
      simpa only [ObservedHistory.stageDomain, Fin.lastCases_castSucc] using
        (show (tt : ℝ) ∈ Ico (H.time i.castSucc) (H.time i.succ) from
          ⟨htt ▸ hts.1.le, htt ▸ hts.2⟩))
  rw [H.scalar_stage_castSucc_of_heq_P6SB2 i hact.symm tt p' y' hy', htt]
  exact ht

/-- **K₀ 收尾（`_P6DP4E2`，PROVED）**：driver 子列 `σ` 上 `DepthExtendable … T` 与逐 `n` 的坏性
`¬ isTracedRegion (ts n) (ys n) (r/√R) (T/R) (n·R)` 矛盾（`A := r` 取 `K₀`，`σ i ≥ i ≥ ⌈K₀⌉`，
`isTracedRegion.mono_bound`）。 -/
theorem false_of_depthExtendable_of_bad_P6DP4E2 {Hs : ℕ → ObservedHistory.{u}}
    {ts : ∀ n, Icc (0 : ℝ) (Hs n).horizon} {ys : ∀ n, ((Hs n).stageAt (ts n)).Carrier}
    {R : ℕ → ℝ} {σ : ℕ → ℕ} {T r : ℝ} (hσ : StrictMono σ) (hr : 0 < r) (hR : ∀ n, 0 < R n)
    (hDE : ObservedHistory.DepthExtendable Hs ts ys R σ T)
    (hbad : ∀ n, ¬ (Hs n).isTracedRegion (ts n) (ys n) (r / Real.sqrt (R n)) (T / R n)
      ((n : ℝ) * R n)) : False := by
  obtain ⟨K₀, hK₀, hev⟩ := hDE r hr
  obtain ⟨N, hN⟩ := exists_nat_ge K₀
  obtain ⟨i, hTR, hi⟩ := (hev.and (eventually_ge_atTop N)).exists
  have hσi : (N : ℝ) ≤ (σ i : ℝ) := by exact_mod_cast hi.trans (hσ.id_le i)
  exact hbad (σ i) (hTR.mono_bound (mul_nonneg hK₀ (hR _).le)
    (mul_le_mul_of_nonneg_right (hN.trans hσi) (hR _).le))

/-- **E2a′（`_P6DP4E2`，PROVED 相对已登记环境前提）**：hTR 合同在固定 `(T, r)` 处对一切 `Kt = m` 失败 ⇒
对角族上的 R4 中心（CPS 形：任何吃「hTR 前缀 + R4 中心数据 + 坏性 `¬TR(k·R)`」的推理都给出 `False`）。 -/
theorem exists_R4_center_family_of_notTR_P6DP4E2 :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
    ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} (F : GC.Interface.RawSurgery P g)
      {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {pF : CutoffParameters}
      (records : ∀ n (e : Fin (F.tower.history n).eventCount),
        GeometricCutoffRecord (F.tower.history n).toHistory e pF),
      (∀ n e b, ((records n e).static b).hasCanonicalWindow) →
      pF.modelAccuracy ≤ ε₀ → 2 ≤ pF.modelOrder →
      StandardCap.transitionEnd + 10 < pF.modelRadius →
      (
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
        ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ k in atTop,
          ∀ (e : Fin (Kh k).eventCount) b, (σ k : ℝ) - T / R k < (Kh k).time e.succ →
            2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R k) <
              (((records (ind k) e).rescale_P6M (c k) (hc k)).static b).neck.scale) →
      ∀ (T r : ℝ), 0 < T → 0 < r →
      (∀ m : ℕ, ¬ (
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
              ∀ (tt : Icc (0 : ℝ) (Kh k).horizon), (tt : ℝ) = t →
              ∀ y' : ((Kh k).stageAt tt).Carrier, HEq y' p' →
                (Kh k).isTracedRegion tt y' (r / Real.sqrt (R k)) (T / R k) ((m : ℝ) * R k))) →
      (
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
        ∀ (pm : ∀ k, ((Kh k).stage (i k).castSucc).Carrier)
          (t : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y' : ∀ k, ((Kh k).stageAt (t k)).Carrier)
          (hat : ∀ k, aSeed k ≤ t k) (hts : ∀ k, t k ≤ σ k),
          (∀ k, HEq (y' k) (pm k)) →
          (∀ k, ∃ wp : ((Kh k).stage (i k).succ).Carrier, HEq (y k) wp ∧
            ((Kh k).event (i k)).RegularCrossing (pm k) wp) →
          (∀ k, (Kh k).time (i k).castSucc < (t k : ℝ) ∧ (t k : ℝ) < (Kh k).time (i k).succ) →
          (∀ k, (σ k : ℝ) - t k ≤ 1 / R k) →
          (∀ k, metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k)) (y' k) <
            2 * R k) →
          (∀ k, R k / 2 <
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k)) (y' k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvt : v ≤ t k),
            (t k : ℝ) - (L k - 2) ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvt.trans ((hts k).trans (hsT k))))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (t k)) (t k))
                    ((seedTrace k).point ((Kh k).activeStage (t k))
                      ((Kh k).activeStage_mono (hat k))
                      ((Kh k).activeStage_mono ((hts k).trans (hsT k)))) (y' k) +
                  ENNReal.ofReal ((L k - 2) / Real.sqrt (R k)) →
              4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ k, ¬ (Kh k).isTracedRegion (t k) (y' k) (r / Real.sqrt (R k)) (T / R k)
            ((k : ℝ) * R k)) →
          False) →
      False := by
  obtain ⟨ε₀, hε₀, hE1⟩ := exists_R4_center_family_P6DP4E.{u}
  refine ⟨ε₀, hε₀, ?_⟩
  intro P g F ε C1 C2 Ctime pF records hcanF hacc hord hrad hsepWK T r hT hr hneg hcont
  have h0 := hneg
  simp only [not_forall, Filter.not_eventually, exists_prop] at h0
  choose ind c hc Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L hRdef hRpos hRr
    hL hsel hgood haS hTnS hroom hradii i hi hbad using h0
  -- tower-frame hsepWK at the selection event, `C = 1`, threshold `T = 1`
  have hsep1 : ∀ m, ∀ᶠ k in atTop, ∀ b, 2 * max (3 / ((1 : ℝ) / 100) ^ 2) (1 * R m k) <
      (((records (ind m k) (i m k)).rescale_P6M (c m k) (hc m k)).static b).neck.scale := by
    intro m
    filter_upwards [hsepWK (ind m) (c m) (hc m) (Tn m) (pT m) (hTc m) (aSeed m) (haT m)
      (hclock m) (hone m) (hsm m) (seedTrace m) (σ m) (y m) (R m) (hsT m) (has m) (L m)
      (hRdef m) (hRpos m) (hRr m) (hL m) (hsel m) (hgood m) (haS m) (hTnS m) (hroom m)
      (hradii m) (i m) (hi m) 1 one_pos 1 zero_le_one] with k hk b
    refine hk (i m k) b ?_
    rw [← hi m k]
    have : 0 < 1 / R m k := one_div_pos.mpr (hRpos m k)
    linarith
  -- diagonal pick
  obtain ⟨κ, hκ⟩ := GC.LongTime.Ch11.exists_diag_pick_P6DP4E2 hbad
    (E := fun m T k => (aSeed m k : ℝ) ≤ σ m k - T / R m k ∧
      (Tn m k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ m k : ℝ) - T / R m k)
    (Fd := fun m T k => T + 1 ≤ L m k ∧
      T ≤ R m k * ((σ m k : ℝ) - ((Tn m k : ℝ) - 1 ^ (2 : ℕ) / 2)) ∧
      T ≤ 1 / 200 * Real.sqrt (R m k) ∧
      ∀ b, 2 * max (3 / ((1 : ℝ) / 100) ^ 2) (1 * R m k) <
        (((records (ind m k) (i m k)).rescale_P6M (c m k) (hc m k)).static b).neck.scale)
    (fun m T hT => (haS m T hT).and (hTnS m T hT))
    (fun m T => ((hL m).eventually_ge_atTop (T + 1)).and (((hroom m).eventually_ge_atTop T).and
      (((hradii m).eventually_ge_atTop T).and (hsep1 m))))
  -- the diagonal family satisfies the hTR prefix
  have hmk : ∀ m : ℕ, (m : ℝ) ≤ (κ m : ℝ) := fun m => by exact_mod_cast (hκ m).2.2.2
  have hRpos' : ∀ m, 0 < R m (κ m) := fun m => hRpos m (κ m)
  have hTc' : ∀ m : ℕ, (m : ℝ) + 1 ≤ c m (κ m) * (Tn m (κ m) : ℝ) := fun m =>
    le_trans (by linarith [hmk m]) (hTc m (κ m))
  have hRr' : ∀ m : ℕ, (m : ℝ) + 1 ≤ R m (κ m) := fun m =>
    le_trans (by linarith [hmk m]) (hRr m (κ m))
  have hL' : Tendsto (fun m => L m (κ m)) atTop atTop :=
    GC.LongTime.Ch11.tendsto_of_diag_P6DP4E2 fun m => by linarith [(hκ m).2.2.1.1]
  have hroom' : Tendsto (fun m => R m (κ m) * ((σ m (κ m) : ℝ) -
      ((Tn m (κ m) : ℝ) - 1 ^ (2 : ℕ) / 2))) atTop atTop :=
    GC.LongTime.Ch11.tendsto_of_diag_P6DP4E2
      (L := fun m k => R m k * ((σ m k : ℝ) - ((Tn m k : ℝ) - 1 ^ (2 : ℕ) / 2)))
      fun m => (hκ m).2.2.1.2.1
  have hradii' : Tendsto (fun m => 1 / 200 * Real.sqrt (R m (κ m))) atTop atTop :=
    GC.LongTime.Ch11.tendsto_of_diag_P6DP4E2 (L := fun m k => 1 / 200 * Real.sqrt (R m k))
      fun m => (hκ m).2.2.1.2.2.1
  have haS' : ∀ T : ℝ, 0 < T → ∀ᶠ m in atTop,
      (aSeed m (κ m) : ℝ) ≤ σ m (κ m) - T / R m (κ m) :=
    GC.LongTime.Ch11.eventually_of_diag_P6DP4E2
      (E := fun m T k => (aSeed m k : ℝ) ≤ σ m k - T / R m k)
      (fun m T T' k hTT' h => le_trans h (by
        have := div_le_div_of_nonneg_right hTT' (hRpos m k).le
        linarith)) fun m => (hκ m).2.1.1
  have hTnS' : ∀ T : ℝ, 0 < T → ∀ᶠ m in atTop,
      (Tn m (κ m) : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ m (κ m) : ℝ) - T / R m (κ m) :=
    GC.LongTime.Ch11.eventually_of_diag_P6DP4E2
      (E := fun m T k => (Tn m k : ℝ) - 1 ^ (2 : ℕ) / 2 ≤ (σ m k : ℝ) - T / R m k)
      (fun m T T' k hTT' h => le_trans h (by
        have := div_le_div_of_nonneg_right hTT' (hRpos m k).le
        linarith)) fun m => (hκ m).2.1.2
  -- E1 environment on the diagonal family
  let K : ℕ → RetainedCoreHistory.{u} := fun m =>
    (F.tower.history (ind m (κ m))).rescale_P6N (c m (κ m)) (hc m (κ m))
  have hasl : ∀ m, (aSeed m (κ m) : ℝ) < σ m (κ m) := fun m => by
    have h1 := (hκ m).2.1.1
    have h2 : 0 < ((m : ℝ) + 1) / R m (κ m) := div_pos (by positivity) (hRpos m (κ m))
    linarith
  have hf : ∀ m, (K m).toHistory.activeStage (aSeed m (κ m)) ≤ (i m (κ m)).castSucc := fun m =>
    ObservedHistory.activeStage_le_castSucc_of_lt_P6ST (K m).toHistory (i m (κ m))
      ((hasl m).trans_eq (hi m (κ m)))
  have hl : ∀ m, (i m (κ m)).succ ≤ (K m).toHistory.activeStage (Tn m (κ m)) := fun m =>
    (activeStage_time_succ_P6DP4E (K m) (i m (κ m)) (σ m (κ m)) (hi m (κ m))).symm.le.trans
      ((K m).toHistory.activeStage_mono (hsT m (κ m)))
  obtain ⟨pm, t, y', hat, hts, hB, hy', hclose, hgood'⟩ := hE1 (eps := ε) (C1' := C1)
    (C2' := C2) (Ctime' := Ctime) K (fun m => i m (κ m))
    (q := fun m => pF.rescale_P6N (c m (κ m)) (hc m (κ m)))
    (fun m => (records (ind m (κ m)) (i m (κ m))).rescale_P6M (c m (κ m)) (hc m (κ m)))
    (fun m => Tn m (κ m)) (fun m => aSeed m (κ m)) (fun m => σ m (κ m))
    (fun m => haT m (κ m)) (fun m => hsT m (κ m)) (fun m => has m (κ m))
    (fun m => pT m (κ m)) (fun m => seedTrace m (κ m)) (fun m => y m (κ m))
    (fun m => R m (κ m)) (fun m => L m (κ m)) hRpos'
    (fun m => by linarith [(hκ m).2.2.1.1, hmk m, (by positivity : (0 : ℝ) ≤ m)])
    hasl (fun m => hi m (κ m)) hf hl
    (fun m => ((records (ind m (κ m)) (i m (κ m))).rescale_P6M (c m (κ m))
      (hc m (κ m))).old_eq_retained)
    (fun m b => ((records (ind m (κ m)) (i m (κ m))).static b).hasCanonicalWindow_rescale_P6M
      (hcanF _ _ b) _ _)
    (fun _ => hacc) (fun _ => hord) (fun _ => hrad)
    (fun m b => by
      refine scalar_lt_half_scale_of_sep_seed_P6DP4E ((hκ m).2.2.1.2.2.2 b) ?_
      have h1 := ObservedHistory.seed_scalar_le_of_smallParabolic_C11G (K m).toHistory (haT m (κ m))
        (hsm m (κ m)) (hclock m (κ m)) (seedTrace m (κ m)) (σ m (κ m)) (has m (κ m))
        (hsT m (κ m)) (i m (κ m)).succ
        (activeStage_time_succ_P6DP4E (K m) (i m (κ m)) (σ m (κ m)) (hi m (κ m)))
        ((hf m).trans (Fin.castSucc_lt_succ (i := i m (κ m))).le) (hl m)
      rw [hi m (κ m), ObservedHistory.stageMetric_succ_time_C11G] at h1
      exact h1.trans (by norm_num))
    (fun m wp hwp b => by
      refine scalar_lt_half_scale_of_sep_P6DP4E ((hκ m).2.2.1.2.2.2 b) ?_
      have h := ObservedHistory.towerScale_eq_output_P6SB2 (K m).toHistory (i m (κ m))
        (σ m (κ m)) (hi m (κ m)) (y m (κ m)) wp hwp
      rw [← hRdef m (κ m)] at h
      rw [← h]
      linarith)
    (fun m => hgood m (κ m))
    (fun m pm' t' =>
      (∃ wp : ((K m).toHistory.stage (i m (κ m)).succ).Carrier, HEq (y m (κ m)) wp ∧
        ((K m).toHistory.event (i m (κ m))).RegularCrossing pm' wp) ∧
      ((K m).time (i m (κ m)).castSucc < t' ∧ t' < (K m).time (i m (κ m)).succ) ∧
      (∀ (tt : Icc (0 : ℝ) (K m).toHistory.horizon), (tt : ℝ) = t' →
        ∀ yy : ((K m).toHistory.stageAt tt).Carrier, HEq yy pm' →
          metricScalarAt ((K m).toHistory.stageMetric ((K m).toHistory.activeStage tt) tt) yy <
            2 * R m (κ m)) ∧
      (∀ (tt : Icc (0 : ℝ) (K m).toHistory.horizon), (tt : ℝ) = t' →
        ∀ yy : ((K m).toHistory.stageAt tt).Carrier, HEq yy pm' →
          R m (κ m) / 2 <
            metricScalarAt ((K m).toHistory.stageMetric ((K m).toHistory.activeStage tt) tt) yy) ∧
      ∃ tt : Icc (0 : ℝ) (K m).toHistory.horizon, (tt : ℝ) = t' ∧
        ∃ yy : ((K m).toHistory.stageAt tt).Carrier, HEq yy pm' ∧
          ¬ (K m).toHistory.isTracedRegion tt yy (r / Real.sqrt (R m (κ m)))
            (T / R m (κ m)) ((m : ℝ) * R m (κ m)))
    (fun m => by
      obtain ⟨p', q, hq, hcr, hfr⟩ := (hκ m).1
      refine ⟨p', q, hq, hcr, ?_⟩
      have hR2 : metricScalarAt ((K m).toHistory.event (i m (κ m))).outputMetric q <
          2 * R m (κ m) := by
        have h := ObservedHistory.towerScale_eq_output_P6SB2 (K m).toHistory (i m (κ m))
          (σ m (κ m)) (hi m (κ m)) (y m (κ m)) q hq
        rw [← hRdef m (κ m)] at h
        rw [← h]
        linarith [hRpos m (κ m)]
      have hcmp := ObservedHistory.eventually_centerScalar_lt_of_regularCrossing_P6SB2
        (K m).toHistory (i m (κ m)) hcr hR2
      have hR3 : R m (κ m) / 2 <
          metricScalarAt ((K m).toHistory.event (i m (κ m))).outputMetric q := by
        have h := ObservedHistory.towerScale_eq_output_P6SB2 (K m).toHistory (i m (κ m))
          (σ m (κ m)) (hi m (κ m)) (y m (κ m)) q hq
        rw [← hRdef m (κ m)] at h
        rw [← h]
        linarith [hRpos m (κ m)]
      have hcmpL := eventually_centerScalar_gt_of_regularCrossing_P6DP4E2
        (K m).toHistory (i m (κ m)) hcr hR3
      have hslab : ∀ᶠ t' in 𝓝[<] (K m).time (i m (κ m)).succ,
          t' ∈ Ioo ((K m).time (i m (κ m)).castSucc) ((K m).time (i m (κ m)).succ) :=
        Ioo_mem_nhdsLT ((K m).time_strictMono (Fin.castSucc_lt_succ (i := i m (κ m))))
      exact (hfr.and_eventually (hcmp.and (hcmpL.and hslab))).mono fun t' h =>
        ⟨⟨q, hq, hcr⟩, h.2.2.2, h.2.1, h.2.2.1, h.1⟩)
  have hcross := fun k => (hB k).1
  have hslab := fun k => (hB k).2.1
  have hcmp := fun k => (hB k).2.2.1 (t k) rfl (y' k) (hy' k)
  have hcmpL := fun k => (hB k).2.2.2.1 (t k) rfl (y' k) (hy' k)
  have hbadTR : ∀ k, ¬ (K k).toHistory.isTracedRegion (t k) (y' k) (r / Real.sqrt (R k (κ k)))
      (T / R k (κ k)) ((k : ℝ) * R k (κ k)) := by
    intro k
    obtain ⟨tt, htt, yy, hyy, hn⟩ := (hB k).2.2.2.2
    obtain rfl : tt = t k := Subtype.ext htt
    obtain rfl : yy = y' k := eq_of_heq (hyy.trans (hy' k).symm)
    exact hn
  exact hcont (fun m => ind m (κ m)) (fun m => c m (κ m)) (fun m => hc m (κ m))
    (fun m => Tn m (κ m)) (fun m => pT m (κ m)) hTc' (fun m => aSeed m (κ m))
    (fun m => haT m (κ m)) (fun m => hclock m (κ m)) (fun m => hone m (κ m))
    (fun m => hsm m (κ m)) (fun m => seedTrace m (κ m)) (fun m => σ m (κ m))
    (fun m => y m (κ m)) (fun m => R m (κ m)) (fun m => hsT m (κ m)) (fun m => has m (κ m))
    (fun m => L m (κ m)) (fun m => hRdef m (κ m)) hRpos' hRr' hL' (fun m => hsel m (κ m))
    (fun m => hgood m (κ m)) haS' hTnS' hroom' hradii' (fun m => i m (κ m))
    (fun m => hi m (κ m)) pm t y' hat hts hy' hcross hslab hclose hcmp hcmpL hgood' hbadTR

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
