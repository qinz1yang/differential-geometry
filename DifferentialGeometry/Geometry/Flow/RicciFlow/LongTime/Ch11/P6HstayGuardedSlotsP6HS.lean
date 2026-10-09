import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HstayGuardedGateP6HS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6Foot3GradSlotP6F5

/-!
# guarded 槽 `hderivL⋆` / `hgradL⋆` ⇐ hgood + `hstayStar`（HSTAY-A4 G3，后缀 `_P6HS`）

G2 gate 孪生 `hlocBCD_of_localSupplies_gate_late_guarded_P6HS` 的两个导数槽（c⋆ guard 形）由前缀 `hgood`
（`HasSpatialCanonicalTimeControl`，阈值 `4·R_k`）+ 距离合同 **`hstayStar`** 付：
* **`hstayStar`**（距离合同，逐点、带阈值、带 c⋆ guard）：U_t 点 `z` 出发的 trace `B`、slab `i′ ≤ (i k)⁻`、
  求值时刻 `v′ ∈ (time i′⁻, time i′⁺)`、`v′ < t`、`t − T/R_k ≤ v′`，在
  guard `(t − v′)·max(max 4 Cg·R_k, R(t, z)) ≤ 1/(2·max(Ctime, 1))` 与阈值 `Cg·R_k < R(v′, B.point)` 下，
  trace 点在 hgood 邻域 `d_{v′}(seed, ·) ≤ d_σ(seed, y) + L/√R`。相对 FOOT3 `hstayΩ`（整窗 `[t − T/R, t]`
  全部时刻、无阈值）严格更弱：只在自适应短窗、阈值以上的求值点要求（形同 SLTPROD G3c
  `hstayLocStar_of_firstExit_P6SP` 的结论，帧不同：gate 帧 `t ↑ σ`、event 索引 trace）。
* `hderivLStar_of_hgood_stayStar_P6HS`（PROVISIONAL[`hstayStar`]，选择子约束 `4 ≤ Cg`）：结论 = G2 gate 孪生
  `hderivL` 槽逐字（`Cder := Ctime`）。证明 = FOOT3 单点核 `deriv_incoming_of_hgood_P6F3` ∘ hgood ∘ `hstayStar`
  （当前 slab 用 singleton trace）。
* `hgradLStar_of_hgood_stayStar_P6HS`（PROVISIONAL[`hstayStar`]，`4 ≤ Cg`）：
  结论 = G2 gate 孪生 `hgradL` 槽逐字
  （`Cgrad := C2.toNNReal`）。证明同 FOOT5 G2（witness `gradient` 字段，singleton trace）。
* consumer：两槽喂 G2 gate 孪生（类型检查）。
生成：build-logs/scratch/HSTAY-A4/gen/gen3.py（binder 从 FOOT3 / G2 文件切文本 + 断言插入 guard）。
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
open ObservedHistory

/-- **`hderivL⋆` ⇐ hgood + `hstayStar`（`_P6HS`，PROVISIONAL[`hstayStar`]）**：结论 = G2 gate 孪生
`hderivL` 槽逐字（`Cder := Ctime`）；`4 ≤ Cg`。 -/
theorem hderivLStar_of_hgood_stayStar_P6HS {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {Cg : ℝ} (hCg4 : 4 ≤ Cg)
    (hstayStar :
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
              (i' : Fin (Kh k).eventCount) (hf : first ≤ i'.castSucc)
              (hij : i'.castSucc ≤ (i k).castSucc),
            ∀ v' ∈ Ioo ((Kh k).time i'.castSucc) ((Kh k).time i'.succ), v' < t →
              t - T / R k ≤ v' →
              (t - v') * max (max 4 Cg * R k) (((Kh k).event (i k)).incoming.flow.scalar t z) ≤
                1 / (2 * max (Ctime : ℝ) 1) →
              Cg * R k < ((Kh k).event i').incoming.flow.scalar v' (B.point i'.castSucc hf hij) →
            ∀ (vv : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ vv) (hvs : vv ≤ σ k),
              (vv : ℝ) = v' →
            ∀ x : ((Kh k).stageAt vv).Carrier, HEq x (B.point i'.castSucc hf hij) →
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage vv) vv)
                  ((seedTrace k).point ((Kh k).activeStage vv) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) x ≤
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
                Cg * R k < ((Kh k).event i').incoming.flow.scalar v'
                  (B.point i'.castSucc hf hij.le) →
                (t - v') * max (max 4 Cg * R k) (((Kh k).event (i k)).incoming.flow.scalar t z) ≤
                  1 / (2 * max (Ctime : ℝ) 1) →
                |derivWithin (fun w' => ((Kh k).event i').incoming.flow.scalar w'
                    (B.point i'.castSucc hf hij.le)) (Iic v') v'| ≤
                  Ctime * ((Kh k).event i').incoming.flow.scalar v'
                    (B.point i'.castSucc hf hij.le) ^ 2) ∧
            ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                (r / Real.sqrt (R k)),
              ∀ v' ∈ Ioo ((Kh k).time (i k).castSucc) t, t - T / R k ≤ v' →
                Cg * R k < ((Kh k).event (i k)).incoming.flow.scalar v' z →
                (t - v') * max (max 4 Cg * R k) (((Kh k).event (i k)).incoming.flow.scalar t z) ≤
                  1 / (2 * max (Ctime : ℝ) 1) →
                |derivWithin (fun w' => ((Kh k).event (i k)).incoming.flow.scalar w' z)
                    (Iic v') v'| ≤
                  Ctime * ((Kh k).event (i k)).incoming.flow.scalar v' z ^ 2 := by
  intro T r hT hr ind c hc Kh Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L hRdef
    hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi
  have hst := hstayStar T r hT hr
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
  have h4R : 4 * R k ≤ Cg * R k := mul_le_mul_of_nonneg_right hCg4 hRk.le
  filter_upwards [hsk p' q hq hcross, Ioo_mem_nhdsLT (show max ((Kh k).time (i k).castSucc)
      ((Kh k).time (i k).succ - T / R k) < (Kh k).time (i k).succ from max_lt hcs (by linarith))]
    with t hstt ht
  have ht1 : (Kh k).time (i k).castSucc < t := lt_of_le_of_lt (le_max_left _ _) ht.1
  have ht2 : (Kh k).time (i k).succ - T / R k < t := lt_of_le_of_lt (le_max_right _ _) ht.1
  have haA : (aSeed k : ℝ) ≤ t - T / R k := by linarith
  have hbσ : t ≤ (σ k : ℝ) := by linarith [ht.2]
  have haL : (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ t - T / R k := by linarith
  refine ⟨?_, ?_⟩
  · intro first hfl z hz B i' hf hij v' hv' hwin hRv' hg
    have hsi : i'.succ ≤ (i k).castSucc := by
      rw [Fin.le_def]
      have h := Fin.lt_def.mp hij
      simp only [Fin.val_succ, Fin.val_castSucc] at h ⊢
      omega
    have hlt : v' < t :=
      lt_of_lt_of_le hv'.2 (((Kh k).time_strictMono.monotone hsi).trans ht1.le)
    have hv0 : 0 ≤ v' := ((Kh k).time_nonneg _).trans hv'.1.le
    have hvH : v' ≤ (Kh k).horizon := hv'.2.le.trans ((Kh k).time_le_horizon_at _)
    let vv : Icc (0 : ℝ) (Kh k).horizon := ⟨v', hv0, hvH⟩
    have hav : aSeed k ≤ vv := show (aSeed k : ℝ) ≤ v' by linarith
    have hvs : vv ≤ σ k := show v' ≤ (σ k : ℝ) by linarith
    exact (Kh k).deriv_incoming_of_hgood_P6F3 i' (B.point i'.castSucc hf hij.le) vv hv'.1 hv'.2
      (q := 4 * R k) (lt_of_le_of_lt h4R hRv').le
      (fun zz hzz h4 => hgood k vv hav hvs (haL.trans hwin) zz
        (hstt first hfl z hz B i' hf hij.le v' hv' hlt hwin hg hRv' vv hav hvs rfl zz hzz) h4)
  · intro z hz v' hv' hwin hRv' hg
    have hv2 : v' < (Kh k).time (i k).succ := hv'.2.trans ht.2
    have hv0 : 0 ≤ v' := ((Kh k).time_nonneg _).trans hv'.1.le
    have hvH : v' ≤ (Kh k).horizon := hv2.le.trans ((Kh k).time_le_horizon_at _)
    let vv : Icc (0 : ℝ) (Kh k).horizon := ⟨v', hv0, hvH⟩
    have hav : aSeed k ≤ vv := show (aSeed k : ℝ) ≤ v' by linarith
    have hvs : vv ≤ σ k := show v' ≤ (σ k : ℝ) by linarith [hv'.2]
    exact (Kh k).deriv_incoming_of_hgood_P6F3 (i k) z vv hv'.1 hv2
      (q := 4 * R k) (lt_of_le_of_lt h4R hRv').le
      (fun zz hzz h4 => hgood k vv hav hvs (haL.trans hwin) zz
        (hstt (i k).castSucc le_rfl z hz (BackwardPointTrace.singleton (Kh k) (i k).castSucc z)
          (i k) le_rfl le_rfl v' ⟨hv'.1, hv2⟩ hv'.2 hwin hg hRv' vv hav hvs rfl zz hzz) h4)

/-- **`hgradL⋆` ⇐ hgood + `hstayStar`（`_P6HS`，PROVISIONAL[`hstayStar`]）**：结论 = G2 gate 孪生
`hgradL` 槽逐字（`Cgrad := C2.toNNReal`）；`4 ≤ Cg`。 -/
theorem hgradLStar_of_hgood_stayStar_P6HS {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {Cg : ℝ} (hCg4 : 4 ≤ Cg)
    (hstayStar :
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
              (i' : Fin (Kh k).eventCount) (hf : first ≤ i'.castSucc)
              (hij : i'.castSucc ≤ (i k).castSucc),
            ∀ v' ∈ Ioo ((Kh k).time i'.castSucc) ((Kh k).time i'.succ), v' < t →
              t - T / R k ≤ v' →
              (t - v') * max (max 4 Cg * R k) (((Kh k).event (i k)).incoming.flow.scalar t z) ≤
                1 / (2 * max (Ctime : ℝ) 1) →
              Cg * R k < ((Kh k).event i').incoming.flow.scalar v' (B.point i'.castSucc hf hij) →
            ∀ (vv : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ vv) (hvs : vv ≤ σ k),
              (vv : ℝ) = v' →
            ∀ x : ((Kh k).stageAt vv).Carrier, HEq x (B.point i'.castSucc hf hij) →
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage vv) vv)
                  ((seedTrace k).point ((Kh k).activeStage vv) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) x ≤
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
            ∀ z ∈ riemannianBallOf (((Kh k).event (i k)).incoming.flow.base.metric t) p'
                (r / Real.sqrt (R k)),
              ∀ v' ∈ Ioo ((Kh k).time (i k).castSucc) t, t - T / R k ≤ v' →
                Cg * R k < ((Kh k).event (i k)).incoming.flow.scalar v' z →
                (t - v') * max (max 4 Cg * R k) (((Kh k).event (i k)).incoming.flow.scalar t z) ≤
                  1 / (2 * max (Ctime : ℝ) 1) →
                ∀ ξ : TangentSpace ThreeModel z,
                  |scalarDifferential ((Kh k).event (i k)).incoming.flow v' z ξ| ≤
                    (C2.toNNReal : ℝ) * ((Kh k).event (i k)).incoming.flow.scalar v' z *
                      Real.sqrt (((Kh k).event (i k)).incoming.flow.scalar v' z) *
                      Real.sqrt
                        ((((Kh k).event (i k)).incoming.flow.base.metric v').inner z ξ ξ) := by
  intro T r hT hr ind c hc Kh Tn pT hTc aSeed haT hclock hone hsm seedTrace σ y R hsT has L hRdef
    hRpos hRr hL hsel hgood haS hTnS hroom hradii i hi
  have hst := hstayStar T r hT hr
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
  have h4R : 4 * R k ≤ Cg * R k := mul_le_mul_of_nonneg_right hCg4 hRk.le
  filter_upwards [hsk p' q hq hcross, Ioo_mem_nhdsLT (show max ((Kh k).time (i k).castSucc)
      ((Kh k).time (i k).succ - T / R k) < (Kh k).time (i k).succ from max_lt hcs (by linarith))]
    with t hstt ht
  have ht1 : (Kh k).time (i k).castSucc < t := lt_of_le_of_lt (le_max_left _ _) ht.1
  have ht2 : (Kh k).time (i k).succ - T / R k < t := lt_of_le_of_lt (le_max_right _ _) ht.1
  have haA : (aSeed k : ℝ) ≤ t - T / R k := by linarith
  have hbσ : t ≤ (σ k : ℝ) := by linarith [ht.2]
  have haL : (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ t - T / R k := by linarith
  intro z hz v' hv' hwin hRv' hg ξ
  have hv0 : 0 ≤ v' := ((Kh k).time_nonneg _).trans hv'.1.le
  have hv2 : v' < (Kh k).time (i k).succ := hv'.2.trans ht.2
  have hvH : v' ≤ (Kh k).horizon := hv2.le.trans ((Kh k).time_le_horizon_at _)
  let vv : Icc (0 : ℝ) (Kh k).horizon := ⟨v', hv0, hvH⟩
  have hav : aSeed k ≤ vv := show (aSeed k : ℝ) ≤ v' by linarith
  have hvs : vv ≤ σ k := show v' ≤ (σ k : ℝ) by linarith [hv'.2]
  have hact : (Kh k).activeStage vv = (i k).castSucc :=
    (Kh k).activeStage_eq_of_mem_slab_P6F3 (i k) vv hv'.1.le hv2
  obtain ⟨zz, hzz⟩ := exists_heq_stageAt_P6JW (Kh k) hact z
  have hd := hstt (i k).castSucc le_rfl z hz (BackwardPointTrace.singleton (Kh k) (i k).castSucc z)
    (i k) le_rfl le_rfl v' ⟨hv'.1, hv2⟩ hv'.2 hwin hg hRv' vv hav hvs rfl zz hzz
  have hsc := ObservedHistory.scalar_transport_P6BB hact (rfl : (vv : ℝ) = v') zz z hzz
  have h4R' : 4 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage vv) vv) zz := by
    rw [hsc, ObservedHistory.stageMetric_castSucc_apply]
    exact h4R.trans hRv'.le
  have hσL : (σ k : ℝ) - L k ^ (2 : ℕ) / R k ≤ (vv : ℝ) := haL.trans hwin
  have hctl := hgood k vv hav hvs hσL zz hd h4R'
  have key : ∀ (m : Fin ((Kh k).eventCount + 1)) (hm : (Kh k).activeStage vv = m)
      (x' : ((Kh k).stage m).Carrier), HEq zz x' →
      ∃ W : SpatialCanonicalWitness ((Kh k).stageMetric m v') ε C1 C2 x',
        W.capTubeHasNeckChart ε := by
    intro m hm x' hx'
    subst hm
    obtain rfl := eq_of_heq hx'
    exact hctl.1
  have hres := key (i k).castSucc hact z hzz
  rw [ObservedHistory.stageMetric_castSucc_apply] at hres
  obtain ⟨W, -⟩ := hres
  have hR0 : 0 ≤ ((Kh k).event (i k)).incoming.flow.scalar v' z := W.Q_pos.le
  exact (W.gradient ξ).trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (Real.le_coe_toNNReal C2) hR0) (Real.sqrt_nonneg _))
    (Real.sqrt_nonneg _))

/-- consumer（G3）：两个 guarded 槽 producer 的类型检查。 -/
example := @hderivLStar_of_hgood_stayStar_P6HS.{u}

example := @hgradLStar_of_hgood_stayStar_P6HS.{u}

/-- consumer（G3 → G2）：两个 producer 逐字喂 G2 gate 孪生的 `hderivL` / `hgradL` 槽（`Cder := Ctime`、
`Cgrad := C2.toNNReal`，同一 `hstayStar`）；其余 binder（`hmargin hrecords hpinch hkappaL`）由类型推断对齐。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {ε C1 C2 : ℝ} {Ctime : ℝ≥0} {Aseed : ℝ} {q : CutoffParameters} (hεle : ε ≤ coneAccuracy)
    {κ : ℝ} (hκ : 0 < κ) {Cg : ℝ} (hCg4 : 4 ≤ Cg) {phi : ℝ → ℝ}
    (hphi : Perelman.AdmissiblePinchingFunction phi) : True := by
  have _h := fun hmargin hrecords hpinch hkappaL hstayStar =>
    hlocBCD_of_localSupplies_gate_late_guarded_P6HS (F := F) (Ctime := Ctime) (Aseed := Aseed)
      (q := q) (Cg := Cg) (Cder := Ctime) (Cgrad := C2.toNNReal) (C1 := C1) hεle hκ hphi
      hmargin hrecords hpinch
      (hderivLStar_of_hgood_stayStar_P6HS (F := F) (C1 := C1) (C2 := C2) hCg4 hstayStar)
      (hgradLStar_of_hgood_stayStar_P6HS (F := F) (C1 := C1) (C2 := C2) hCg4 hstayStar) hkappaL
  trivial

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
