import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6J11HgapDrvJ11S
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KdataRescaleP6X3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GapProducersFinalLocP6KT2c

/-!
# hgap J11 final 槽 `hJ11F` / `hJ11F8` ⇐ FRESH + `hDext`（O-CH11-J11STAY G6，后缀 `_J11S`）

lead 续令（3）。final 槽前缀与事件槽只差中心位置 `time last < σ < horizon`（G1/G4 stay 对任意
`σ < horizon` 成立：CXJF2 first-exit 覆盖 final slab，`hUSCtop` 空真）。final 槽自带 records 包已是
driver 形（`recordsK`（阈 `T₀`）、`hcan`、`hacc ≤ 1/(n+1)`、`n + 1 ≤ radius`、`n + 2 ≤ order`、
scale 分离 `(n+1)·max((n+1)/c, Qs) ≤ scale`）⇒ **records 包由槽内部付**，不需 `hDrvJ`：
* `hsepK_of_scale_J11S`（PROVED）：scale 分离 + `R ≤ c·Qs`（`hRρ` + `neckRadius_rescale_inv_sq_P6X`）
  ⇒ 重标度 records 的 driver `hsep` 窗形（`hscaleK_rescale_P6X3`）；
* `hJ11F_loc_of_depthExt_J11S` / `hJ11F8_loc_of_depthExt_J11S`：KT2c final producer
  `hgapJF{,8}_loc_of_producers_P6KT2c` 的 `hJ11F` / `hJ11F8` 逐字，PROVISIONAL[`hDextJF`]
  （final 前缀 ⇒ hPN 中心 driver 输出 `hDext`）；`hC2`、`hfresh`、`records` 为常数 / producer 原有前提。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open GC.LongTime.Ch11 (p6CoarseC_C11GT6 p6FineEta_C11GT6)

/-- **driver `hsep` 窗形 ⇐ 原尺度 scale 分离（`_J11S`，PROVED）**：原 records `(n+1)·max((n+1)/c, Qs) ≤ scale`
+ `R ≤ c·Qs` ⇒ 重标度 records（`recordsKRescale_P6X3`，`T̃₀ = max 1 (T₀/c)`）对任意 `T, C`
最终 `2·max(3/(1/100)², C·R) < scale`（窗条件不用）。 -/
theorem hsepK_of_scale_J11S {Ho : ℕ → RetainedCoreHistory.{u}} {c : ℕ → ℝ} (hc : ∀ n, 0 < c n)
    {p : ℕ → CutoffParameters} {T₀ Qs R : ℕ → ℝ}
    (recP : ∀ n (i : Fin (Ho n).eventCount), T₀ n ≤ (Ho n).time i.succ →
      GeometricCutoffRecord (Ho n).toHistory i (p n))
    (σ : ∀ n, Icc (0 : ℝ) ((Ho n).rescale_P6N (c n) (hc n)).toHistory.horizon)
    (hRpos : ∀ n, 0 < R n) (hRQ : ∀ n, R n ≤ c n * Qs n)
    (hsc : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Qs n) ≤
      ((recP n i hi).static b).neck.scale) :
    ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (i : Fin ((Ho n).rescale_P6N (c n) (hc n)).eventCount)
        (hi : max 1 (T₀ n / c n) ≤ ((Ho n).rescale_P6N (c n) (hc n)).time i.succ) b,
        (σ n : ℝ) - T / R n < ((Ho n).rescale_P6N (c n) (hc n)).time i.succ →
        2 * max (3 / ((1 : ℝ) / 100) ^ 2) (C * R n) <
          (((Ho n).recordsKRescale_P6X3 (hc n) (recP n) i hi).static b).neck.scale := by
  intro T _ C hC
  obtain ⟨N, hN⟩ := exists_nat_ge (2 * C + 245)
  filter_upwards [eventually_ge_atTop N] with n hn i hi b _
  have hn' : (N : ℝ) ≤ n := by exact_mod_cast hn
  have h := (Ho n).hscaleK_rescale_P6X3 (hc n) (recP n) (hsc n) i hi b
  have hR := hRpos n
  have hm1 : ((n : ℝ) + 1) * ((n : ℝ) + 1) ≤ ((n : ℝ) + 1) * max ((n : ℝ) + 1) (c n * Qs n) :=
    mul_le_mul_of_nonneg_left (le_max_left _ _) (by positivity)
  have hm2 : ((n : ℝ) + 1) * R n ≤ ((n : ℝ) + 1) * max ((n : ℝ) + 1) (c n * Qs n) :=
    mul_le_mul_of_nonneg_left ((hRQ n).trans (le_max_right _ _)) (by positivity)
  rw [mul_max_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  refine max_lt ?_ ?_
  · nlinarith
  · nlinarith

/-- **hgap J11 final 槽（`_J11S`，PROVISIONAL[`hDextJF`]）**：结论 = KT2c `hJ11F` 逐字。 -/
theorem hJ11F_loc_of_depthExt_J11S {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {a₀ : ℝ} {T₀ Qt : ℕ → ℝ}
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hfresh : ∀ A : ℝ, 0 < A → ∃ κ : ℝ, 0 < κ ∧ ∃ Tf : ℝ, ∀ n,
      KappaSeedWindowFwd_C11PK (fun w => q.neckRadius (4 * w / 3)) A κ Tf
        (F.tower.history n).toHistory)
    (hC2 : 0 ≤ C2) (records : GC.LongTime.Ch11.CutoffRecords_C11S F q)
    (hDextJF : ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
        let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
        ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
          (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
          (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
          (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
          (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
            ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
        let c : ℕ → ℝ := fun k => r k ^ 2
        let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
        let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
        let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
        let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
        let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
          (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
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
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
          (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
          (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
          (∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (σ k : ℝ) ∧
            (σ k : ℝ) < (Kh k).horizon) →
          (∀ k : ℕ, (k : ℝ) + 1 < R k) →
        ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          ∀ T : ℝ, 0 < T → ObservedHistory.DepthExtendable Kh σ y R (φ ∘ ψ) T) :
    ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
        let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
        ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
          (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
          (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
          (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
          (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
            ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
        let c : ℕ → ℝ := fun k => r k ^ 2
        let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
        let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
        let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
        let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
        let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
          (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          ∀ (hRpos : ∀ k, 0 < R k), (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
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
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
          (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
          (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
          (∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (σ k : ℝ) ∧
            (σ k : ℝ) < (Kh k).horizon) →
          (∀ k : ℕ, (k : ℝ) + 1 < R k) →
        let Qs : ℕ → ℝ := fun n => max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹
        (∀ (p : ℕ → CutoffParameters)
          (recordsK : ∀ n (i : Fin (Ho n).eventCount), T₀ n ≤ (Ho n).time i.succ →
            GeometricCutoffRecord (Ho n).toHistory i (p n)),
          (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
          (∀ n (i : Fin (Ho n).eventCount), T₀ n ≤ (Ho n).time i.succ →
            q.delta ((Ho n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) →
          (∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) →
          (∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) →
          (∀ n : ℕ, n + 2 ≤ (p n).modelOrder) →
          (∀ n i hi b, 1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) →
          (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Qs n) ≤
            ((recordsK n i hi).static b).neck.scale) →
          (∃ κd : ℝ, 0 < κd ∧ ∀ D Lv B : ℝ, 0 < D → 0 < Lv → 0 < B → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Ho n).toHistory.stageMetric
            ((Ho n).toHistory.activeStage ((Ho n).unscaleTime_P6X (hc n) (σ n)))
            ((Ho n).unscaleTime_P6X (hc n) (σ n)))
            ((Ho n).uncastRescale_P6CK (hc n) (σ n) (y n)) (D / Real.sqrt (R n / c n)),
        ∀ (v : Icc (0 : ℝ) (Ho n).toHistory.horizon)
          (hvt : v ≤ (Ho n).unscaleTime_P6X (hc n) (σ n)),
          (((Ho n).unscaleTime_P6X (hc n) (σ n) : Icc (0 : ℝ) (Ho n).toHistory.horizon) : ℝ) -
            B / (R n / c n) ≤ v →
        ∀ tr : BackwardPointTrace (Ho n).toHistory ((Ho n).toHistory.activeStage v)
          ((Ho n).toHistory.activeStage ((Ho n).unscaleTime_P6X (hc n) (σ n)))
          ((Ho n).toHistory.activeStage_mono hvt) x,
        ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ Lv →
          (Ho n).toHistory.isParabolicallyRmControlledBall v
            (tr.point ((Ho n).toHistory.activeStage v) le_rfl
              ((Ho n).toHistory.activeStage_mono hvt))
            (ϱ / Real.sqrt (R n / c n)) →
          ENNReal.ofReal (κd * ϱ ^ 3) ≤
            ballVolume (scaleMetric (R n / c n) (div_pos (hRpos n) (hc n))
              ((Ho n).toHistory.stageMetric ((Ho n).toHistory.activeStage v) v))
              (tr.point ((Ho n).toHistory.activeStage v) le_rfl
                ((Ho n).toHistory.activeStage_mono hvt)) ϱ)) := by
  intro A hA ind Ho Tno pTo r hr hk h2r hsmo hvolo c hc K Kh Tn pT aSeed haT hclock h1 hsm
    hlate seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ
    hroom hball hdistσ hev hlt Qs p recP hcanP _ haccP hradP hordP _ hscP
  have hDext := hDextJF A hA ind Tno pTo r hr hk h2r hsmo hvolo aSeed haT hclock h1 hsm hlate
    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
    hball hdistσ hev hlt
  have hσH : ∀ k, (σ k : ℝ) < (Kh k).horizon := fun k => (hev k).2
  have hfinE := hdistσ.mono fun k hk =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans le_self_add hk)
  have hRr' : ∀ k : ℕ, (k : ℝ) + 1 ≤ R k := hRr
  have hRQ : ∀ n, R n ≤ c n * Qs n := fun n => by
    have h := hRρ n
    have hTn : c n * (Tn n : ℝ) = Tno n := (Ho n).mul_rescaleTime_P6X (hc n) (Tno n)
    rw [RetainedCoreHistory.neckRadius_rescale_inv_sq_P6X (hc n) q, hTn] at h
    exact h.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (hc n).le)
  have hT₀K : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, max 1 (T₀ n / c n) ≤ (σ n : ℝ) - T / R n :=
    fun T hT => (hwin T hT).mono fun n hn => by
      refine max_le ((h1 n).trans hn) (le_trans ?_ hn)
      rw [div_le_iff₀ (hc n)]
      linarith [hlate n, mul_comm (c n) (aSeed n : ℝ)]
  have hstayK := ObservedHistory.hstayK_of_drv_J11S (Cg := 4) (haT := haT) hC2 K hclock h1 hsm
    seedTrace σ y R hsT has L hRpos hRr' hL hgood hσH hfinE
    (fun k τ x => ObservedHistory.hpin_rescaled_of_records_P6HI F records ind c hc k τ x)
    (fun n => (p n).rescale_P6N (c n) (hc n)) (fun n => max 1 (T₀ n / c n))
    (fun n => (Ho n).recordsKRescale_P6X3 (hc n) (recP n))
    (hsepK_of_scale_J11S hc recP σ hRpos hRQ hscP) hT₀K
    (fun n => (Ho n).hcanK_rescale_P6X3 (hc n) (recP n) (hcanP n)) haccP hradP hordP
  have hfpL := ObservedHistory.hfpL_hPN_of_depthExt_J11S (haT := haT) seedTrace σ y R hsT has L
    hRpos hL hstayK hDext hdistσ
  obtain ⟨κ, hκ, Tf, hsup⟩ := hfresh (A + 3) (by linarith)
  have hsupK := GC.LongTime.Ch11.fresh_rescale_adapter_P6JA hsup ind c hc
  have hA0 : (0 : ℝ) < A := by linarith
  have hR1 : ∀ k, (1 : ℝ) ≤ R k := fun k => by
    have := hRr k
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hprep0 := fun k => ObservedHistory.freshK_prep_J11S hanti (Ho k) (Tno k) (pTo k) (hr k)
    hA0 (Tno k).2.1 (h2r k) (hvolo k) (hR1 k) (hRρ k)
  have hTf : ∀ᶠ k in atTop, Tf / c k ≤ (Tn k : ℝ) := by
    obtain ⟨N, hN⟩ := exists_nat_ge Tf
    filter_upwards [eventually_ge_atTop N] with k hkN
    have h1' : (N : ℝ) ≤ k := by exact_mod_cast hkN
    exact (ObservedHistory.freshK_prep_J11S hanti (Ho k) (Tno k) (pTo k) (hr k) hA0
      (by linarith [hk k]) (h2r k) (hvolo k) (hR1 k) (hRρ k)).1
  exact hJ11_of_fresh_fpL_J11S (Ho := Ho) (c := c) (haT := haT) hc seedTrace σ y R hsT hκ hRpos
    (fun k w => q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k)) (fun k => Tf / c k)
    hsupK hTf (fun k => (hprep0 k).2.1) hsm (fun k => (hprep0 k).2.2.1)
    (fun k => (hprep0 k).2.2.2) hclock hwin hwin' hradii hfpL

/-- **hgap J11 final J8 槽（`_J11S`，PROVISIONAL[`hDextJF`]）**：结论 = KT2c `hJ11F8` 逐字。 -/
theorem hJ11F8_loc_of_depthExt_J11S {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    {a₀ : ℝ} {T₀ Qt : ℕ → ℝ}
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hfresh : ∀ A : ℝ, 0 < A → ∃ κ : ℝ, 0 < κ ∧ ∃ Tf : ℝ, ∀ n,
      KappaSeedWindowFwd_C11PK (fun w => q.neckRadius (4 * w / 3)) A κ Tf
        (F.tower.history n).toHistory)
    (hC2 : 0 ≤ C2) (records : GC.LongTime.Ch11.CutoffRecords_C11S F q)
    (hDextJF : ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
        let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
        ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
          (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
          (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
          (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
          (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
            ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
        let c : ℕ → ℝ := fun k => r k ^ 2
        let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
        let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
        let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
        let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
        let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
          (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl (p6FineEta_C11GT6 ε)
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε))
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε))
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε)).toNNReal (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              8 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
          (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
          (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
          (∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (σ k : ℝ) ∧
            (σ k : ℝ) < (Kh k).horizon) →
          (∀ k : ℕ, (k : ℝ) + 1 < R k) →
        ∀ φ : ℕ → ℕ, StrictMono φ → ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
          ∀ T : ℝ, 0 < T → ObservedHistory.DepthExtendable Kh σ y R (φ ∘ ψ) T) :
    ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
        let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
        ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
          (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
          (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
          (∀ k, 2 * r k ^ 2 < (Tno k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
          (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
            ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
        let c : ℕ → ℝ := fun k => r k ^ 2
        let hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
        let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (hc k)
        let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
        let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k => (Ho k).rescaleTime_P6X (hc k) (Tno k)
        let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
          (Ho k).castRescale_P6X (hc k) (Tno k) (pTo k)
        ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
          (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - 1 ^ 2) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
          (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
          (∀ k, T₀ k ≤ c k * (aSeed k : ℝ)) →
        ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
            ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
          (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
          (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
          (∀ k, R k =
            metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
          ∀ (hRpos : ∀ k, 0 < R k), (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) → (∀ k, Qt k < R k) →
          Tendsto L atTop atTop →
          (∀ k, ¬ (Kh k).HasSpatialCanonicalTimeControl (p6FineEta_C11GT6 ε)
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε))
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε))
            (p6CoarseC_C11GT6.{u} (p6FineEta_C11GT6 ε)).toNNReal (σ k) (y k)) →
          (∀ k, ∀ (v : Icc (0 : ℝ) (Kh k).horizon) (hav : aSeed k ≤ v) (hvs : v ≤ σ k),
            (σ k : ℝ) - L k ^ 2 / R k ≤ (v : ℝ) →
            ∀ z : ((Kh k).stageAt v).Carrier,
              riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage v) v)
                  ((seedTrace k).point ((Kh k).activeStage v) ((Kh k).activeStage_mono hav)
                    ((Kh k).activeStage_mono (hvs.trans (hsT k)))) z ≤
                riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                    ((seedTrace k).point ((Kh k).activeStage (σ k))
                      ((Kh k).activeStage_mono (has k)) ((Kh k).activeStage_mono (hsT k))) (y k) +
                  ENNReal.ofReal (L k / Real.sqrt (R k)) →
              8 * R k ≤ metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage v) v) z →
              (Kh k).HasSpatialCanonicalTimeControl ε C1 C2 Ctime v z) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (aSeed k : ℝ) ≤ σ k - T / R k) →
          (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ (σ k : ℝ) - T / R k) →
          Tendsto (fun k => R k * ((σ k : ℝ) - ((Tn k : ℝ) - 1 ^ 2 / 2))) atTop atTop →
          Tendsto (fun k => 1 / 200 * Real.sqrt (R k)) atTop atTop →
          (∀ k, R k ≤ ((q.rescale_P6N (c k) (hc k)).neckRadius (Tn k) ^ 2)⁻¹) →
          (∀ k, (Tn k : ℝ) - 1 ^ 2 / 2 ≤ σ k - L k ^ 2 / R k) →
          (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
          (∀ᶠ k in atTop,
            riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
                ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
                  ((Kh k).activeStage_mono (hsT k))) (y k) +
              ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
          (∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (σ k : ℝ) ∧
            (σ k : ℝ) < (Kh k).horizon) →
          (∀ k : ℕ, (k : ℝ) + 1 < R k) →
        let Qs : ℕ → ℝ := fun n => max (((n : ℝ) + 1) / c n) (q.neckRadius (Tno n) ^ 2)⁻¹
        (∀ (p : ℕ → CutoffParameters)
          (recordsK : ∀ n (i : Fin (Ho n).eventCount), T₀ n ≤ (Ho n).time i.succ →
            GeometricCutoffRecord (Ho n).toHistory i (p n)),
          (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) →
          (∀ n (i : Fin (Ho n).eventCount), T₀ n ≤ (Ho n).time i.succ →
            q.delta ((Ho n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) →
          (∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) →
          (∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) →
          (∀ n : ℕ, n + 2 ≤ (p n).modelOrder) →
          (∀ n i hi b, 1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) →
          (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Qs n) ≤
            ((recordsK n i hi).static b).neck.scale) →
          (∃ κd : ℝ, 0 < κd ∧ ∀ D Lv B : ℝ, 0 < D → 0 < Lv → 0 < B → ∀ᶠ n in atTop,
        ∀ x ∈ riemannianBallOf ((Ho n).toHistory.stageMetric
            ((Ho n).toHistory.activeStage ((Ho n).unscaleTime_P6X (hc n) (σ n)))
            ((Ho n).unscaleTime_P6X (hc n) (σ n)))
            ((Ho n).uncastRescale_P6CK (hc n) (σ n) (y n)) (D / Real.sqrt (R n / c n)),
        ∀ (v : Icc (0 : ℝ) (Ho n).toHistory.horizon)
          (hvt : v ≤ (Ho n).unscaleTime_P6X (hc n) (σ n)),
          (((Ho n).unscaleTime_P6X (hc n) (σ n) : Icc (0 : ℝ) (Ho n).toHistory.horizon) : ℝ) -
            B / (R n / c n) ≤ v →
        ∀ tr : BackwardPointTrace (Ho n).toHistory ((Ho n).toHistory.activeStage v)
          ((Ho n).toHistory.activeStage ((Ho n).unscaleTime_P6X (hc n) (σ n)))
          ((Ho n).toHistory.activeStage_mono hvt) x,
        ∀ ϱ : ℝ, 0 < ϱ → ϱ ≤ Lv →
          (Ho n).toHistory.isParabolicallyRmControlledBall v
            (tr.point ((Ho n).toHistory.activeStage v) le_rfl
              ((Ho n).toHistory.activeStage_mono hvt))
            (ϱ / Real.sqrt (R n / c n)) →
          ENNReal.ofReal (κd * ϱ ^ 3) ≤
            ballVolume (scaleMetric (R n / c n) (div_pos (hRpos n) (hc n))
              ((Ho n).toHistory.stageMetric ((Ho n).toHistory.activeStage v) v))
              (tr.point ((Ho n).toHistory.activeStage v) le_rfl
                ((Ho n).toHistory.activeStage_mono hvt)) ϱ)) := by
  intro A hA ind Ho Tno pTo r hr hk h2r hsmo hvolo c hc K Kh Tn pT aSeed haT hclock h1 hsm
    hlate seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ
    hroom hball hdistσ hev hlt Qs p recP hcanP _ haccP hradP hordP _ hscP
  have hDext := hDextJF A hA ind Tno pTo r hr hk h2r hsmo hvolo aSeed haT hclock h1 hsm hlate
    seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hRt hradii hRρ hroom
    hball hdistσ hev hlt
  have hσH : ∀ k, (σ k : ℝ) < (Kh k).horizon := fun k => (hev k).2
  have hfinE := hdistσ.mono fun k hk =>
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top (le_trans le_self_add hk)
  have hRr' : ∀ k : ℕ, (k : ℝ) + 1 ≤ R k := hRr
  have hRQ : ∀ n, R n ≤ c n * Qs n := fun n => by
    have h := hRρ n
    have hTn : c n * (Tn n : ℝ) = Tno n := (Ho n).mul_rescaleTime_P6X (hc n) (Tno n)
    rw [RetainedCoreHistory.neckRadius_rescale_inv_sq_P6X (hc n) q, hTn] at h
    exact h.trans (mul_le_mul_of_nonneg_left (le_max_right _ _) (hc n).le)
  have hT₀K : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, max 1 (T₀ n / c n) ≤ (σ n : ℝ) - T / R n :=
    fun T hT => (hwin T hT).mono fun n hn => by
      refine max_le ((h1 n).trans hn) (le_trans ?_ hn)
      rw [div_le_iff₀ (hc n)]
      linarith [hlate n, mul_comm (c n) (aSeed n : ℝ)]
  have hstayK := ObservedHistory.hstayK_of_drv_J11S (Cg := 8) (haT := haT) hC2 K hclock h1 hsm
    seedTrace σ y R hsT has L hRpos hRr' hL hgood hσH hfinE
    (fun k τ x => ObservedHistory.hpin_rescaled_of_records_P6HI F records ind c hc k τ x)
    (fun n => (p n).rescale_P6N (c n) (hc n)) (fun n => max 1 (T₀ n / c n))
    (fun n => (Ho n).recordsKRescale_P6X3 (hc n) (recP n))
    (hsepK_of_scale_J11S hc recP σ hRpos hRQ hscP) hT₀K
    (fun n => (Ho n).hcanK_rescale_P6X3 (hc n) (recP n) (hcanP n)) haccP hradP hordP
  have hfpL := ObservedHistory.hfpL_hPN_of_depthExt_J11S (haT := haT) seedTrace σ y R hsT has L
    hRpos hL hstayK hDext hdistσ
  obtain ⟨κ, hκ, Tf, hsup⟩ := hfresh (A + 3) (by linarith)
  have hsupK := GC.LongTime.Ch11.fresh_rescale_adapter_P6JA hsup ind c hc
  have hA0 : (0 : ℝ) < A := by linarith
  have hR1 : ∀ k, (1 : ℝ) ≤ R k := fun k => by
    have := hRr k
    have : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    linarith
  have hprep0 := fun k => ObservedHistory.freshK_prep_J11S hanti (Ho k) (Tno k) (pTo k) (hr k)
    hA0 (Tno k).2.1 (h2r k) (hvolo k) (hR1 k) (hRρ k)
  have hTf : ∀ᶠ k in atTop, Tf / c k ≤ (Tn k : ℝ) := by
    obtain ⟨N, hN⟩ := exists_nat_ge Tf
    filter_upwards [eventually_ge_atTop N] with k hkN
    have h1' : (N : ℝ) ≤ k := by exact_mod_cast hkN
    exact (ObservedHistory.freshK_prep_J11S hanti (Ho k) (Tno k) (pTo k) (hr k) hA0
      (by linarith [hk k]) (h2r k) (hvolo k) (hR1 k) (hRρ k)).1
  exact hJ11_of_fresh_fpL_J11S (Ho := Ho) (c := c) (haT := haT) hc seedTrace σ y R hsT hκ hRpos
    (fun k w => q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k)) (fun k => Tf / c k)
    hsupK hTf (fun k => (hprep0 k).2.1) hsm (fun k => (hprep0 k).2.2.1)
    (fun k => (hprep0 k).2.2.2) hclock hwin hwin' hradii hfpL

/-- **consumer（`_J11S`）**：输出喂 KT2c `hgapJF_loc_of_producers_P6KT2c` 的 `hJ11F` 位。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hδq : Tendsto q.delta atTop (𝓝 0))
    (records : GC.LongTime.Ch11.CutoffRecords_C11S F q)
    (hP5L : ∀ (D ε : ℝ) (m : ℕ), 0 < ε → ∃ T : ℝ, ∀ k, ∃ p : CutoffParameters,
      p.delta = q.delta ∧ p.neckRadius = q.neckRadius ∧ p.fixed = q.fixed ∧
      p.recenterConstant = q.recenterConstant ∧ D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ε ∧
      m ≤ p.modelOrder ∧ ∃ rs : ∀ i : Fin (F.tower.history k).eventCount,
        T ≤ (F.tower.history k).time i.succ →
        GeometricCutoffRecord (F.tower.history k).toHistory i p,
      (∀ i hi b, GC.LongTime.Ch11.linkedCanonicalWindow_C11E ((rs i hi).static b)) ∧
      ∀ i hi, (rs i hi).nominalRadius = (records k i).nominalRadius ∧
        (rs i hi).delta = (records k i).delta ∧
        (rs i hi).order = (records k i).order ∧
        (∀ α, HEq ((rs i hi).neck α) ((records k i).neck α)) ∧
        (∀ b, ((rs i hi).static b).neck.scale = ((records k i).static b).neck.scale) ∧
        ∀ (b) (z : ThreeBall),
          ((rs i hi).static b).inclusion (((rs i hi).static b).witness.cap z) =
            ((records k i).static b).inclusion (((records k i).static b).witness.cap z))
    {Ctime₀ : ℝ≥0} (hTD : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime₀)
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
      -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x)
    {T₀ Qt : ℕ → ℝ}
    (hT₀ : ∀ n, lateThrJF_P6WR2 a₀ records hP5L hδq hanti n ≤ T₀ n)
    (hfresh : ∀ A : ℝ, 0 < A → ∃ κ : ℝ, 0 < κ ∧ ∃ Tf : ℝ, ∀ n,
      KappaSeedWindowFwd_C11PK (fun w => q.neckRadius (4 * w / 3)) A κ Tf
        (F.tower.history n).toHistory) (hC2 : 0 ≤ C2) : True := by
  have _ := fun hDextJF => ObservedHistory.hgapJF_loc_of_producers_P6KT2c
    (ε := ε) (C1 := C1) (C2 := C2) (Ctime := Ctime) hanti hδq records hP5L hTD ha₀ hHI
    hT₀
    (hJ11F_loc_of_depthExt_J11S (T₀ := T₀) (Qt := Qt) (a₀ := a₀) hanti hfresh hC2 records
      hDextJF)
  trivial

/-- **consumer（`_J11S`）**：输出喂 KT2c `hgapJF8_loc_of_producers_P6KT2c` 的 `hJ11F8` 位。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hδq : Tendsto q.delta atTop (𝓝 0))
    (records : GC.LongTime.Ch11.CutoffRecords_C11S F q)
    (hP5L : ∀ (D ε : ℝ) (m : ℕ), 0 < ε → ∃ T : ℝ, ∀ k, ∃ p : CutoffParameters,
      p.delta = q.delta ∧ p.neckRadius = q.neckRadius ∧ p.fixed = q.fixed ∧
      p.recenterConstant = q.recenterConstant ∧ D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ε ∧
      m ≤ p.modelOrder ∧ ∃ rs : ∀ i : Fin (F.tower.history k).eventCount,
        T ≤ (F.tower.history k).time i.succ →
        GeometricCutoffRecord (F.tower.history k).toHistory i p,
      (∀ i hi b, GC.LongTime.Ch11.linkedCanonicalWindow_C11E ((rs i hi).static b)) ∧
      ∀ i hi, (rs i hi).nominalRadius = (records k i).nominalRadius ∧
        (rs i hi).delta = (records k i).delta ∧
        (rs i hi).order = (records k i).order ∧
        (∀ α, HEq ((rs i hi).neck α) ((records k i).neck α)) ∧
        (∀ b, ((rs i hi).static b).neck.scale = ((records k i).static b).neck.scale) ∧
        ∀ (b) (z : ThreeBall),
          ((rs i hi).static b).inclusion (((rs i hi).static b).witness.cap z) =
            ((records k i).static b).inclusion (((records k i).static b).witness.cap z))
    {Ctime₀ : ℝ≥0} (hTD : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime₀)
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
      -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x)
    {T₀ Qt : ℕ → ℝ}
    (hT₀ : ∀ n, lateThrJF_P6WR2 a₀ records hP5L hδq hanti n ≤ T₀ n)
    (hfresh : ∀ A : ℝ, 0 < A → ∃ κ : ℝ, 0 < κ ∧ ∃ Tf : ℝ, ∀ n,
      KappaSeedWindowFwd_C11PK (fun w => q.neckRadius (4 * w / 3)) A κ Tf
        (F.tower.history n).toHistory) (hC2 : 0 ≤ C2) : True := by
  have _ := fun hDextJF => ObservedHistory.hgapJF8_loc_of_producers_P6KT2c
    (ε := ε) (C1 := C1) (C2 := C2) (Ctime := Ctime) hanti hδq records hP5L hTD ha₀ hHI
    hT₀
    (hJ11F8_loc_of_depthExt_J11S (T₀ := T₀) (Qt := Qt) (a₀ := a₀) hanti hfresh hC2 records
      hDextJF)
  trivial

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
