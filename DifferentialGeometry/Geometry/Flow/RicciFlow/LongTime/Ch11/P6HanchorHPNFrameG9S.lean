import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDShiftSeqG9S
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SliceBCBDAlignCrossP6SB2
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SelectionP6X
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6FreshRescaleP6JA
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HpinRescaledP6HI
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6VolumeRescaleCXSP
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LateTimeCoreP6TC

/-!
# hPN 帧 producer：塔帧 `hanchor0`（G9″ 平移孪生 ⇐ hPN 合同字段 + A2B 数值项）
（O-CH11-G9SHIFT G2，后缀 `_G9S`）

`hanchor0_hPN_frame_G9S`：binder 顺序与 `lateTimeCoreAt_of_normalized_prefix_P6TC` 的 `hPN` 合同
（`P6LateTimeCoreP6TC`:121–180）逐字一致（`let Ho / c / K / Kh / Tn / pT`，`r := 1` 的 K 帧，`Aκ := A + 7`），
只删去本接线不用的 `Qt`、`¬HSCTC`、两条 `Tendsto`、`hroom`；其后追加 K 帧数据与位置数据。
结论 = DEPTH4C2 driver 的 `hanchor0` 槽逐字（`Hs := Kh`、`ts := σ`、`ys := y`、`R`）。
链：
* `j / hjt / htj` ⇒ `yG`（`activeStage_eq_of_mem_slab_P6X`，同 `eventInterior_data_P6X` 的证明）与 `hRn`
  （`scalar_of_incoming_P6X`）；
* `hT₀` ⇐ `hT₀_seed_G9S`（`T₀ n := Tn n − 1/2`）；`hRa / hT₀X` ⇐ A2B `hRa_of_hPN_A2B / hT₀X_of_hPN_A2B`
  （`T₀X := T₀ / c`）；`hdσ` ⇐ hPN 球字段；`hgate` ⇐ hPN 末字段（`A + 3 ≤ A + 7`）；`hOldX = rfl`
  （`RetainedCoreHistory` 的 event `old` 定义即 retained core，`rescale_P6N` 保持）；`hpin` ⇐ HINIT
  `hpin_rescaled_of_records_P6HI`（`a₀ := 0`）；
* FRESH：`hsupA` 的 `nr_k w = ρ(4 c_k w / 3) / √c_k`、`Tκ_k = Tf / c_k`、`Aκ = A + 7`；`hWK` = `hsup`，
  `hTκ`（eventually）⇐ `c k · Tn k = Tno k ≥ k + 1`，`htimeS` ⇐ `2 r² < Tno`，`hvolS` ⇐ 原尺度体积字段
  经 `le_ballVolume_castRescale_iff_CXSP`，`hnrS` ⇐ `ρ` 反单调 + `Tn > 2`（`4(Tn − 1/2)/3 ≥ Tn`）+ 天花板
  `R ≤ ρ̂(Tn)⁻²`、`R ≥ 1`；
* `hpre1 / hpre2` ⇐ `hpre_Tn_G9S`（`TimeDerivativeSupply_C11E` + `ρ` 反单调，阈值在 `Tn`）；`hsepρ`、
  `hsupA`、`hder` 为已登记合同；底座已换 BCBD-A2 G6 guarded 孪生（无 `hdistW`），
  逐 `n` FRESH 版见 `P6SliceBCBDGuardSeqG9S`；
* 主体 ⇐ `sliceBCBD_kernel_fresh_sep_noProtC_alignedG_seq_ev_G9S` ∘
  `hanchor0_driver_of_kernel_comparable_P6SB2`（`C := 1`，`R = scalar(σ, y)`）。
生成器 `gen/genB.py`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn
open DifferentialGeometry.Integral.Measure DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- seed 形 `T₀`（`_G9S`，PROVED；SEPFIX `hT₀_seed_P6SF` 的本地孪生，避免同名冲突）：
`T₀ n := Tn n − 1/2` 满足 kernel `hT₀`。 -/
theorem hT₀_seed_G9S {Tn σ R : ℕ → ℝ} (hR : ∀ n, 0 < R n)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, Tn n - 1 ^ 2 / 2 ≤ σ n - T / R n) :
    ∀ B : ℝ, ∀ᶠ n in atTop, Tn n - 1 ^ 2 / 2 ≤ σ n - B / R n := by
  intro B
  rcases lt_or_ge 0 B with hB | hB
  · exact hwin B hB
  · filter_upwards [hwin 1 one_pos] with n hn
    have h1 : B / R n ≤ 1 / R n :=
      div_le_div_of_nonneg_right (by linarith) (hR n).le
    linarith

/-- **前缀 Dt，阈值在 `Tn`（`_G9S`，PROVED；SEPFIX `hpre_of_supply_tower_Tn_P6SF` 的本地孪生）**：
`K n = (F.tower.history (ind n)).rescale_P6N (c n)`，观测时刻 `t n ≤ Tn n`，
`ρs n := fun _ => ρ̂(Tn n)` 处的 `hpre1 / hpre2`。 -/
theorem hpre_Tn_G9S {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {Ctime : ℝ≥0}
    (hTD : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (hanti : AntitoneOn q.neckRadius (Ici 0)) (ind : ℕ → ℕ) {c : ℕ → ℝ} (hc : ∀ n, 0 < c n)
    {j : ∀ n, Fin (F.tower.history (ind n)).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time (j n).castSucc < t n)
    (htj : ∀ n, t n < ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time (j n).succ)
    (Tn : ℕ → ℝ) (htT : ∀ n, t n ≤ Tn n) :
    (∀ n, ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).EventSlabsDerivative Ctime
        (max ((n : ℝ) + 1) ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹)
        (j n).castSucc) ∧
    (∀ n, (((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).toHistory.event
        (j n)).incoming.DerivativeBoundBefore Ctime
          (max ((n : ℝ) + 1) ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹) (t n)) := by
  obtain ⟨h1, h2⟩ := prefixDt_rescale_seq_P6HN hTD hanti ind hc hjt htj
  have hle : ∀ n, c n * (q.neckRadius (c n * t n) ^ 2)⁻¹ ≤
      max ((n : ℝ) + 1) ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ := fun n => by
    have ht0 : 0 ≤ t n :=
      ((((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).toHistory.time_nonneg
        (j n).castSucc)).trans (hjt n).le
    have heq : ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ =
        c n * (q.neckRadius (c n * Tn n) ^ 2)⁻¹ := by
      change ((q.neckRadius (c n * Tn n) / Real.sqrt (c n)) ^ 2)⁻¹ = _
      rw [div_pow, Real.sq_sqrt (hc n).le, inv_div, div_eq_mul_inv]
    rw [heq]
    refine le_trans ?_ (le_max_right _ _)
    exact mul_le_mul_of_nonneg_left (inv_sq_neckRadius_le_P6HN hanti
      (mul_nonneg (hc n).le ht0) (mul_le_mul_of_nonneg_left (htT n) (hc n).le)) (hc n).le
  exact ⟨fun n e he => derivativeBoundBefore_mono_qcan_P6SN _ (hle n) (h1 n e he),
    fun n => derivativeBoundBefore_mono_qcan_P6SN _ (hle n) (h2 n)⟩

/-- **`hnrS` 数值核（`_G9S`，PROVED）**：`Tn > 2`、`w ∈ [Tn − 1/2, Tn]`、`R ≥ 1`、天花板
`R ≤ ρ̂(Tn)⁻²` ⇒ `ρ(4 c w / 3) / √c ≤ 1`（FRESH 供给的 `nr_k` 在 seed 窗内不超过 `r = 1`）。 -/
theorem nr_le_one_G9S {q : CutoffParameters} (hanti : AntitoneOn q.neckRadius (Ici 0))
    {c Tn w R : ℝ} (hc : 0 < c) (hT : 2 < Tn) (hw1 : Tn - 1 ^ 2 / 2 ≤ w) (hR1 : 1 ≤ R)
    (hceil : R ≤ ((q.rescale_P6N c hc).neckRadius Tn ^ 2)⁻¹) :
    q.neckRadius (4 * (c * w) / 3) / Real.sqrt c ≤ 1 := by
  have hTw : Tn ≤ 4 * w / 3 := by linarith
  have h43 : c * Tn ≤ 4 * (c * w) / 3 :=
    calc c * Tn ≤ c * (4 * w / 3) := mul_le_mul_of_nonneg_left hTw hc.le
      _ = 4 * (c * w) / 3 := by ring
  have hc0 : 0 ≤ c * Tn := mul_nonneg hc.le (by linarith)
  have hanti' : q.neckRadius (4 * (c * w) / 3) ≤ q.neckRadius (c * Tn) :=
    hanti (mem_Ici.mpr hc0) (mem_Ici.mpr (hc0.trans h43)) h43
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hρ : (q.rescale_P6N c hc).neckRadius Tn = q.neckRadius (c * Tn) / Real.sqrt c := rfl
  rw [hρ] at hceil
  set ρh : ℝ := q.neckRadius (c * Tn) / Real.sqrt c with hρh
  have hρ2 : ρh ^ 2 ≤ 1 := by
    rcases (sq_nonneg ρh).eq_or_lt with h0 | hpos
    · rw [← h0]
      exact zero_le_one
    · have h1 : 1 ≤ (ρh ^ 2)⁻¹ := hR1.trans hceil
      exact (one_le_inv₀ hpos).mp h1
  have hρ1 : ρh ≤ 1 := by nlinarith [sq_nonneg (ρh - 1)]
  exact (div_le_div_of_nonneg_right hanti' hs.le).trans hρ1

/-- **hPN 帧 producer：塔帧 `hanchor0`（`_G9S`，PROVISIONAL[`hsupA`（FRESH 合同）、`hder`、
`hsepρ`、`records / recordsK / hcanK / hacc / hrad / hord / hpinchK0`（已登记 K 帧 records 合同）]）**：
见文件头。 -/
theorem hanchor0_hPN_frame_G9S {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hεcone : ε ≤ coneAccuracy) (hC2 : 0 ≤ C2)
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hder : GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime)
    (T₀o : ℕ → ℝ)
    (hsupA : ∀ Aseed : ℝ, 1 < Aseed → ∃ κ : ℝ, 0 < κ ∧ ∃ Tf : ℝ,
      ∀ (ind : ℕ → ℕ) (c : ℕ → ℝ) (hc : ∀ k, 0 < c k) (k : ℕ),
        KappaSeedWindowFwd_C11PK
          (fun w => q.neckRadius (4 * (c k * w) / 3) / Real.sqrt (c k)) (Aseed + 7) κ
          (Tf / c k) ((F.tower.history (ind k)).rescale_P6N (c k) (hc k)).toHistory)
    {phi : ℝ → ℝ} (hphi : Perelman.AdmissiblePinchingFunction phi) {θ₀ : ℝ} (hθ₀ : 0 < θ₀)
    {pF : CutoffParameters}
    (records : ∀ n (e : Fin (F.tower.history n).eventCount),
      GeometricCutoffRecord (F.tower.history n).toHistory e pF)
    {A : ℝ} (hA : 1 < A) (ind : ℕ → ℕ) :
    let Ho : ℕ → RetainedCoreHistory.{u} := fun k => F.tower.history (ind k)
    ∀ (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
      (pTo : ∀ k, ((Ho k).toHistory.stageAt (Tno k)).Carrier) (r : ℕ → ℝ)
      (hr : ∀ k, 0 < r k), (∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) →
      (∀ k, 2 * r k ^ (2 : ℕ) < (Tno k : ℝ)) →
      (∀ k, GC.LongTime.hasSmallParabolicCurvature (Ho k).toHistory (Tno k) (pTo k) (r k)) →
      (∀ k, ENNReal.ofReal (A⁻¹ * r k ^ 3) ≤ ballVolume ((Ho k).toHistory.stageMetric
        ((Ho k).toHistory.activeStage (Tno k)) (Tno k)) (pTo k) (r k)) →
    let c : ℕ → ℝ := fun k => r k ^ (2 : ℕ)
    let K : ℕ → RetainedCoreHistory.{u} := fun k => (Ho k).rescale_P6N (c k) (pow_pos (hr k) 2)
    let Kh : ℕ → ObservedHistory.{u} := fun k => (K k).toHistory
    let Tn : ∀ k, Icc (0 : ℝ) (Kh k).horizon := fun k =>
      (Ho k).rescaleTime_P6X (pow_pos (hr k) 2) (Tno k)
    let pT : ∀ k, ((Kh k).stageAt (Tn k)).Carrier := fun k =>
      (Ho k).castRescale_P6X (pow_pos (hr k) 2) (Tno k) (pTo k)
    ∀ (aSeed : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (haT : ∀ k, aSeed k ≤ Tn k),
      (∀ k, (aSeed k : ℝ) = (Tn k : ℝ) - (1 : ℝ) ^ (2 : ℕ)) → (∀ k, 1 ≤ (aSeed k : ℝ)) →
      (∀ k, GC.LongTime.hasSmallParabolicCurvature (Kh k) (Tn k) (pT k) 1) →
      (∀ k, T₀o k ≤ c k * (aSeed k : ℝ)) →
    ∀ (seedTrace : ∀ k, BackwardPointTrace (Kh k) ((Kh k).activeStage (aSeed k))
        ((Kh k).activeStage (Tn k)) ((Kh k).activeStage_mono (haT k)) (pT k))
      (σ : ∀ k, Icc (0 : ℝ) (Kh k).horizon) (y : ∀ k, ((Kh k).stageAt (σ k)).Carrier)
      (R : ℕ → ℝ) (hsT : ∀ k, σ k ≤ Tn k) (has : ∀ k, aSeed k ≤ σ k) (L : ℕ → ℝ),
      (∀ k, R k =
        metricScalarAt ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k)) (y k)) →
      (∀ k, 0 < R k) → (∀ k : ℕ, (k : ℝ) + 1 ≤ R k) →
      Tendsto L atTop atTop →
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
      (∀ T : ℝ, 0 < T → ∀ᶠ k in atTop, (Tn k : ℝ) - (1 : ℝ) ^ (2 : ℕ) / 2 ≤ (σ k : ℝ) - T / R k) →
      (∀ k, R k ≤ ((q.rescale_P6N (c k) (pow_pos (hr k) 2)).neckRadius (Tn k) ^ (2 : ℕ))⁻¹) →
      (∀ k, y k ∈ riemannianBallOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
        ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
          ((Kh k).activeStage_mono (hsT k))) ((A + 1) * 1)) →
      (∀ᶠ k in atTop,
        riemannianEDistOf ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ((seedTrace k).point ((Kh k).activeStage (σ k)) ((Kh k).activeStage_mono (has k))
              ((Kh k).activeStage_mono (hsT k))) (y k) +
          ENNReal.ofReal ((L k + 1) / Real.sqrt (R k)) ≤ ENNReal.ofReal ((A + 3) * 1)) →
    ∀ (p : ℕ → CutoffParameters)
      (recordsK : ∀ k (i : Fin (K k).eventCount),
        (Tn k : ℝ) - (1 : ℝ) ^ (2 : ℕ) / 2 ≤ (K k).time i.succ →
        GeometricCutoffRecord (K k).toHistory i (p k))
      (_hcanK : ∀ k i hi b, ((recordsK k i hi).static b).hasCanonicalWindow)
      (_hacc : ∀ᶠ k : ℕ in atTop, (p k).modelAccuracy ≤ 1 / ((k : ℝ) + 1))
      (_hrad : ∀ᶠ k : ℕ in atTop, (k : ℝ) + 1 ≤ (p k).modelRadius)
      (_hord : ∀ᶠ k : ℕ in atTop, k + 2 ≤ (p k).modelOrder)
    (_hpinchK0 : ∀ n (i : Fin (K n).eventCount), Perelman.PhiAlmostNonnegative
      ((K n).toHistory.event i).incoming.flow
      (Ico ((K n).time i.castSucc) ((K n).time i.succ) ∩
        Ici ((Tn n : ℝ) - (1 : ℝ) ^ (2 : ℕ) / 2)) phi)
      (j : ∀ k, Fin (K k).eventCount)
      (_hjt : ∀ k, (K k).time (j k).castSucc < (σ k : ℝ))
      (_htj : ∀ k, (σ k : ℝ) < (K k).time (j k).succ)
      (_hsepρ : ∀ B : ℝ, 0 < B → ∀ᶠ n in atTop,
        ∀ (i : Fin (K n).eventCount) (hi : (Tn n : ℝ) - (1 : ℝ) ^ (2 : ℕ) / 2 ≤ (K n).time i.succ)
          (b : ((K n).toHistory.event i).RetainedBoundaryIndex), i.succ ≤ (j n).castSucc →
          ((σ n : ℝ) - B / R n ≤ (K n).time i.succ ∨
            (σ n : ℝ) - (K n).time i.succ ≤ θ₀ * (((recordsK n i hi).static b).neck.scale)⁻¹) →
          ((n : ℝ) + 1) * max ((n : ℝ) + 1)
              ((q.rescale_P6N (c n) (pow_pos (hr n) 2)).neckRadius (Tn n) ^ (2 : ℕ))⁻¹ ≤
            ((recordsK n i hi).static b).neck.scale),
      ∀ A' : ℝ, 0 < A' → ∃ Q : ℝ, 2 ≤ Q ∧ ∀ᶠ n in atTop,
        ∀ z ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (A' / Real.sqrt (R n)),
          metricScalarAt ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) z ≤ Q * R n := by
  intro Ho Tno pTo r hr hNT htime hsmallo hvolo c K Kh Tn pT aSeed haT hclock ha1 hsmallK hT₀o
    seedTrace σ y R hsT has L hRdef hRpos hRle hL hgood hwin hwinF hceil hyball hgate
    p recordsK hcanK hacc hrad hord hpinchK0 j hjt htj hsepρ
  have hc : ∀ k, 0 < c k := fun k => pow_pos (hr k) 2
  have hR1 : ∀ n, 1 ≤ R n := fun n => by
    have h1 := hRle n
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hTn : ∀ n, c n * (Tn n : ℝ) = (Tno n : ℝ) := fun n =>
    (Ho n).mul_rescaleTime_P6X (hc n) (Tno n)
  have hc2 : ∀ n, c n = r n ^ 2 := fun _ => rfl
  have hTn2 : ∀ n, 2 < (Tn n : ℝ) := fun n => by
    by_contra hle0
    have hle := not_lt.mp hle0
    have hrp : 0 < r n ^ 2 := pow_pos (hr n) 2
    have h3 := mul_le_mul_of_nonneg_left hle hrp.le
    have h4 := hTn n
    have h5 := htime n
    rw [hc2 n] at h4
    linarith
  have hact : ∀ n, (Kh n).activeStage (σ n) = (j n).castSucc := fun n =>
    (K n).activeStage_eq_of_mem_slab_P6X (j n) (σ n) (hjt n).le (htj n)
  obtain ⟨yG, hyG⟩ : ∃ yG : ∀ n, ((K n).stage (j n).castSucc).Carrier,
      ∀ n, HEq (y n) (yG n) :=
    ⟨fun n => cast (congrArg (fun m => ((K n).stage m).Carrier) (hact n)) (y n),
      fun n => (cast_heq _ _).symm⟩
  have hRn : ∀ n, R n =
      ((K n).toHistory.event (j n)).incoming.flow.scalar (σ n) (yG n) := fun n => by
    rw [hRdef n]
    exact (K n).scalar_of_incoming_P6X (j n) (hact n).symm (σ n) (yG n) (y n) (hyG n)
  obtain ⟨hpre1, hpre2⟩ := hpre_Tn_G9S hder hanti ind hc (j := j) (t := fun n => (σ n : ℝ))
    hjt htj (fun n => (Tn n : ℝ)) (fun n => Subtype.coe_le_coe.mpr (hsT n))
  obtain ⟨κ, hκ, Tf, hsup⟩ := hsupA A hA
  have hTκ : ∀ᶠ n in atTop, Tf / c n ≤ (Tn n : ℝ) := by
    obtain ⟨N, hN⟩ := exists_nat_gt Tf
    filter_upwards [eventually_ge_atTop N] with n hn
    rw [div_le_iff₀ (hc n)]
    have h1 := hNT n
    have h2 : (N : ℝ) ≤ n := by exact_mod_cast hn
    have h3 := hTn n
    calc Tf ≤ c n * (Tn n : ℝ) := by linarith
      _ = (Tn n : ℝ) * c n := mul_comm _ _
  have hvolS : ∀ n, ENNReal.ofReal ((A + 7)⁻¹ * 1 ^ 3) ≤ ballVolume
      ((Kh n).stageMetric ((Kh n).activeStage (Tn n)) (Tn n)) (pT n) 1 := by
    intro n
    have hrs : r n / Real.sqrt (c n) = 1 := by
      rw [hc2 n, Real.sqrt_sq (hr n).le]
      exact div_self (hr n).ne'
    have h := ((Ho n).le_ballVolume_castRescale_iff_CXSP (hc n) (v := Tno n) (p := pTo n)
      (κ := A⁻¹) (r := r n)).mpr (hvolo n)
    rw [hrs] at h
    refine le_trans (ENNReal.ofReal_le_ofReal ?_) h
    have hA0 : 0 < A := by linarith
    have h7 : (A + 7)⁻¹ ≤ A⁻¹ := inv_anti₀ hA0 (by linarith)
    exact mul_le_mul_of_nonneg_right h7 (by positivity)
  have hS := ObservedHistory.sliceBCBD_kernel_fresh_sep_noProtC_alignedG_seq_ev_G9S
    (K := K) (j := j)
    (t := fun n => (σ n : ℝ)) (T₀ := fun n => (Tn n : ℝ) - 1 ^ 2 / 2) (p := p)
    (recordsK := recordsK) (yG := yG) (hεcone := hεcone) (hC20 := hC2) (hphi := hphi)
    (hθ₀ := hθ₀) (hjt := hjt) (htj := htj) (hcanK := hcanK) (hacc := hacc) (hrad := hrad)
    (hord := hord) (hpinchK0 := hpinchK0) (Kh := Kh) (hKh := rfl) (σ := σ)
    (hσ := fun _ => rfl) (y := y) (hyG := hyG) (R := R) (hRpos := hRpos) (hRn := hRn)
    (hRle := hRle)
    (hT₀ := hT₀_seed_G9S (Tn := fun n => (Tn n : ℝ)) (σ := fun n => (σ n : ℝ)) hRpos hwinF)
    (Tn := Tn) (aSeed := aSeed) (haT := haT) (hsT := hsT) (has := has) (pT := pT)
    (seedTrace := seedTrace) (L := L) (hL := hL) (hCg := (by norm_num : (2 : ℝ) ≤ 4))
    (hgood := hgood) (hwin := hwin) (hr := one_pos)
    (hsmall := hsmallK) (hclock := hclock) (a₀ := fun _ => 0) (ha₀ := fun _ => le_rfl)
    (hpin := fun n s x =>
      ObservedHistory.hpin_rescaled_of_records_P6HI F records ind c hc n s x)
    (hRa := hRa_of_hPN_A2B R (fun n => (aSeed n : ℝ)) hRle ha1)
    (T₀X := fun n => T₀o n / c n)
    (hT₀X := hT₀X_of_hPN_A2B T₀o c (fun n => (aSeed n : ℝ)) hc hT₀o)
    (hOldX := fun _ _ _ => rfl) (hdσ := fun n => ne_top_of_lt (hyball n)) (hκ := hκ)
    (nr := fun n w => q.neckRadius (4 * (c n * w) / 3) / Real.sqrt (c n))
    (Tκ := fun n => Tf / c n) (Aκ := A + 7) (hWK := fun n => hsup ind c hc n) (hTκ := hTκ)
    (htimeS := fun n => by have := hTn2 n; linarith) (hvolS := hvolS)
    (hnrS := fun n w h1 _ => nr_le_one_G9S hanti (hc n) (hTn2 n) h1 (hR1 n) (hceil n))
    (hwinF := hwinF)
    (hgate := hgate.mono fun n h => h.trans (ENNReal.ofReal_le_ofReal (by linarith)))
    (ρs := fun n _ => (q.rescale_P6N (c n) (hc n)).neckRadius (Tn n)) (hceil := hceil)
    (hsepρ := hsepρ) (hpre1 := hpre1) (hpre2 := hpre2)
  exact ObservedHistory.hanchor0_driver_of_kernel_comparable_P6SB2 Kh rfl σ y hjt htj hyG R hRpos
    hRn R hRpos one_pos (Filter.Eventually.of_forall fun n => by rw [← hRdef n, one_mul]) hS

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
