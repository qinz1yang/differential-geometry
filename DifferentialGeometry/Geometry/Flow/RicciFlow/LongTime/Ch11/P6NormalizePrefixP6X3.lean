import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HclosNormalizeSmallP6X3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6RoomDistSigmaP6R2

/-!
# D-17 量词重排：producer 阈值进 prefix、retained selector、保留 `A` / `hvol`（O-CH11-P6SEL3 G5）

P6WIRE 对照表（build-logs/scratch/S-CH11-P6WIRE/TABLE.md）S1/S4/S5 的修复（后缀 `_P6X3`）：
* **S1**：`T₀ Qt : ℕ → ℝ`（records late 阈值、**重标度**导数阈值）与 `Ctime₀` 在 selection **之前**给出；
  坏种子取在 `K₁ = max (k+1) (Qt k + 1)`、`T = max (k+1) (2 T₀ k)` 处，于是迟度
  `T₀ k ≤ c·ãSeed = t − r² > t/2` 与 `Qt k < R̃` 由 selection 输出**证出**，进 `hPNP` 前缀而非
  gap 结论。
  原尺度导数阈值 = `Qt n / c n`（`c n·(Qt n/c n) = Qt n`）；`Qt` 取重标度单位是必须的——原尺度固定阈值
  `Q < R_orig` 不可证（`R_orig ≥ K₁ r⁻²`，`r` 无上界）。
* **S4**：`hPNP` 前缀保留原尺度种子 `Tno pTo r`、`hsmall`、`hvol`（`A⁻¹ r³ ≤ ballVolume`）与 `A`；重标度种子
  `Tn pT` 由 `let` 给出（`c = r²`）。
* **S5**：selection 换 P6REST2 retained 版 `selection_of_bad_sequence_retained_P6R2`（于重标度 history，
  `r̃ = 1`）：前缀多 `R̃ ≤ ρ̃(T̃n)⁻²`、per-n `hroom`、ball `(A+1)·1`、`hdistσ`（`hdistσ_of_retained_P6R2`，
  `Aκ = A + 3`）。
* `lateCoreAt_of_normalized_prefix_P6X3` / **`canonicalLateCore_of_normalized_prefix_P6X3`**
  （`A ≤ 1` 借 `max A 2`）；`example`：旧 G4a `canonicalLateCore_of_normalizedS_P6X3` 由新形推出（新 gap 更弱）。
* **`ObservedHistory.canonicalLateCore_of_normalizedS_hclos_prefix_P6X3`**：G4b 的重排版，`hgapP` 的 ∃ 只剩
  `p pF recordsK a₀` 与其余 binder（`T₀ Qt Ctime₀` 在外层 prefix，`Monotone T₀`、`Monotone Qt` 供子列重索引）；
  κ 组只剩 `κ ρV hκ hρV hκR`（`r := 1`、`Aκ := A + 3`，`hroom` / `hdistσ` 取前缀）。
* **S3（BLOCKED，未修）**：`hgapP` 仍收重标度 `Nonempty (Pre841Data_C11K Kh σ y R hRpos)`——lateHI 主形
  `false_of_selection_eventSlab_lateHI_closed_Cg_P6S3` 经 `exists_tracedPinching_of_pre841_P6M d`
  （`d.native.pinching` 单一 shift）与 `hseed_of_pre841_P6M d` 消费整个 `d`；重标度族的 native `params`
  随 `n` 变，不可由原尺度 `d` 搬运。repair target：P6CG 主形变体收 κ-only（`kappa_pos` + 尺度不变的
  `volume_ge`）+ 迟窗 pinching（G3 `hpin_rescale_P6X3`，年龄 ≥ 1）代替 `d`。**S2**：`hslabK` 由 P6WIRE 另接。
陈述由 build-logs/scratch/O-CH11-P6SEL3/mk_g5.py 生成。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.CheegerGromovCompactness
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood
open DifferentialGeometry.Geometry.Collapse
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace GC.LongTime.Ch11

universe u

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
open DifferentialGeometry.PDE.RicciFlow.Perelman.CanonicalNeighborhood.FiniteHorn

/-- **(b) 于单个 `A > 1` ⇐ S5 + S11 + `hPNP`**（`_P6X3`）：见文件头。 -/
theorem lateCoreAt_of_normalized_prefix_P6X3 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hcan : HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2)
    (hder : TimeDerivativeSupply_C11E F q.neckRadius Ctime) (T₀ Qt : ℕ → ℝ)
    (hPN : ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
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
        False)
    {A : ℝ} (hA : 1 < A) :
    LargerBallCanonicalLateAt_P6A F ε C1 C2 A := by
  by_contra hcon
  have hk : ∀ k : ℕ, ∃ (n : ℕ) (t : Icc (0 : ℝ) (F.tower.history n).toHistory.horizon)
      (p : ((F.tower.history n).toHistory.stageAt t).Carrier) (r : ℝ)
      (x : ((F.tower.history n).toHistory.stageAt t).Carrier),
      (k : ℝ) + 1 ≤ (t : ℝ) ∧ 2 * T₀ k ≤ (t : ℝ) ∧ 2 * r ^ 2 < (t : ℝ) ∧
      hasSmallParabolicCurvature (F.tower.history n).toHistory t p r ∧
      ENNReal.ofReal (A⁻¹ * r ^ 3) ≤ ballVolume ((F.tower.history n).toHistory.stageMetric
        ((F.tower.history n).toHistory.activeStage t) t) p r ∧
      x ∈ riemannianBallOf ((F.tower.history n).toHistory.stageMetric
        ((F.tower.history n).toHistory.activeStage t) t) p (A * r) ∧
      max ((k : ℝ) + 1) (Qt k + 1) * (r ^ 2)⁻¹ ≤ metricScalarAt
        ((F.tower.history n).toHistory.stageMetric
          ((F.tower.history n).toHistory.activeStage t) t) x ∧
      ¬ ∃ W : SpatialCanonicalWitness ((F.tower.history n).toHistory.stageMetric
          ((F.tower.history n).toHistory.activeStage t) t) ε C1 C2 x,
        W.capTubeHasNeckChart ε := by
    intro k
    by_contra hk
    refine hcon ⟨max ((k : ℝ) + 1) (Qt k + 1), max ((k : ℝ) + 1) (2 * T₀ k),
      lt_max_of_lt_left (by positivity), lt_max_of_lt_left (by positivity), ?_⟩
    intro n _ t p r hT ht hs hv x hx hK
    by_contra hW
    exact hk ⟨n, t, p, r, x, (le_max_left _ _).trans hT, (le_max_right _ _).trans hT, ht, hs, hv,
      hx, hK, hW⟩
  choose ind Tn pT r x hlate hlateT₀ htime hsmall hvol hx hK hW using hk
  have hr : ∀ k, 0 < r k := fun k => (hsmall k).1
  have hseed : ∀ k, ∃ (a : Icc (0 : ℝ) (F.tower.history (ind k)).toHistory.horizon)
      (hat : a ≤ Tn k), (a : ℝ) = (Tn k : ℝ) - r k ^ 2 ∧
      Nonempty (BackwardPointTrace (F.tower.history (ind k)).toHistory
        ((F.tower.history (ind k)).toHistory.activeStage a)
        ((F.tower.history (ind k)).toHistory.activeStage (Tn k))
        ((F.tower.history (ind k)).toHistory.activeStage_mono hat) (pT k)) := fun k => by
    obtain ⟨hrk, a, hat, ha, htr⟩ := hsmall k
    have hp : pT k ∈ riemannianBallOf ((F.tower.history (ind k)).toHistory.stageMetric
        ((F.tower.history (ind k)).toHistory.activeStage (Tn k)) (Tn k)) (pT k) (r k) := by
      change riemannianEDistOf _ (pT k) (pT k) < ENNReal.ofReal (r k)
      rw [riemannianEDistOf_self]
      exact ENNReal.ofReal_pos.mpr hrk
    obtain ⟨tr, -⟩ := htr (pT k) hp
    exact ⟨a, hat, ha, ⟨tr⟩⟩
  choose aSeed haT hclock hst using hseed
  have hc : ∀ k, 0 < r k ^ 2 := fun k => pow_pos (hr k) 2
  have hsq : ∀ k, Real.sqrt (r k ^ 2) = r k := fun k => Real.sqrt_sq (hr k).le
  have hRx : ∀ k : ℕ, max ((k : ℝ) + 1) (Qt k + 1) ≤ r k ^ 2 * metricScalarAt
      ((F.tower.history (ind k)).toHistory.stageMetric
        ((F.tower.history (ind k)).toHistory.activeStage (Tn k)) (Tn k)) (x k) := by
    intro k
    have := mul_le_mul_of_nonneg_left (hK k) (hc k).le
    rwa [← mul_assoc, mul_comm (r k ^ 2), mul_assoc, mul_inv_cancel₀ (hc k).ne', mul_one] at this
  have hRx' : ∀ k : ℕ, max ((k : ℝ) + 1) (Qt k + 1) ≤ metricScalarAt
      (((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory.stageMetric
        (((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory.activeStage
          ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k)))
        ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k)))
      ((F.tower.history (ind k)).castRescale_P6X (hc k) (Tn k) (x k)) := fun k => by
    rw [(F.tower.history (ind k)).scalar_castRescale_P6X (hc k)]
    exact hRx k
  have hxb : ∀ k, (F.tower.history (ind k)).castRescale_P6X (hc k) (Tn k) (x k) ∈
      riemannianBallOf
        (((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory.stageMetric
        (((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory.activeStage
          ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k)))
        ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k)))
      ((F.tower.history (ind k)).castRescale_P6X (hc k) (Tn k) (pT k)) (A * 1) := fun k => by
    have h := (F.tower.history (ind k)).ball_castRescale_P6X (hc k) (Tn k) (pT k) (x k) (hx k)
    rwa [hsq k, mul_div_assoc, div_self (hr k).ne'] at h
  have hclock' : ∀ k, (((F.tower.history (ind k)).rescaleTime_P6X (hc k) (aSeed k) :
      Icc (0 : ℝ) ((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory.horizon) :
        ℝ) = ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k) : ℝ) - 1 ^ 2 := fun k => by
    change (aSeed k : ℝ) / r k ^ 2 = (Tn k : ℝ) / r k ^ 2 - 1 ^ 2
    rw [hclock k, sub_div, div_self (hc k).ne', one_pow]
  have hRx0 : ∀ k : ℕ, (k : ℝ) + 1 ≤ metricScalarAt
      (((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory.stageMetric
        (((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory.activeStage
          ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k)))
        ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k)))
      ((F.tower.history (ind k)).castRescale_P6X (hc k) (Tn k) (x k)) :=
    fun k => (le_max_left _ _).trans (hRx' k)
  have hRpos0 : ∀ k, 0 < metricScalarAt
      (((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory.stageMetric
        (((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory.activeStage
          ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k)))
        ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k)))
      ((F.tower.history (ind k)).castRescale_P6X (hc k) (Tn k) (x k)) :=
    fun k => lt_of_lt_of_le (by positivity) (hRx0 k)
  have hdiv : Tendsto (fun k => metricScalarAt
      (((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory.stageMetric
        (((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory.activeStage
          ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k)))
        ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k)))
      ((F.tower.history (ind k)).castRescale_P6X (hc k) (Tn k) (x k))
      * (fun _ : ℕ => (1 : ℝ)) k ^ 2) atTop atTop :=
    tendsto_atTop_mono (fun k : ℕ => by rw [one_pow, mul_one]; linarith [hRx0 k])
      tendsto_natCast_atTop_atTop
  have hA0 : 0 < A := zero_lt_one.trans hA
  have hsel := ObservedHistory.selection_of_bad_sequence_retained_P6R2
    (Kh := fun k => ((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory)
    (fun k => q.rescale_P6N (r k ^ 2) (hc k)) le_rfl le_rfl le_rfl
    (fun k => RetainedCoreHistory.neckRadius_rescale_antitone_P6X (hc k) hanti)
    (fun k => (F.tower.history (ind k)).canonical_rescale_P6X (hc k) (hcan (ind k)))
    (fun k => (F.tower.history (ind k)).derivative_rescale_P6X (hc k)
      (fun v z hlo hhi hR =>
        stageDerivative_of_timeDerivativeSupply_P6X hder (ind k) v z hlo hhi hR))
    (fun k => (F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k))
    (fun k => (F.tower.history (ind k)).castRescale_P6X (hc k) (Tn k) (pT k))
    (fun _ => 1) A (fun _ => one_pos) hA0
    (fun k => (F.tower.history (ind k)).rescaleTime_P6X (hc k) (aSeed k))
    (fun k => (F.tower.history (ind k)).rescaleTime_mono_P6X (hc k) (haT k)) hclock'
    (fun k => (F.tower.history (ind k)).seedTrace_rescale_P6X (hc k) (haT k) (hst k).some)
    (fun k => (F.tower.history (ind k)).castRescale_P6X (hc k) (Tn k) (x k)) hxb hRpos0
    (fun k hG => (F.tower.history (ind k)).noWitness_castRescale_P6X (hc k) (Tn k) (x k) (hW k)
      hG.1) hdiv
  obtain ⟨σ, y, R, hsT, has, L, ⟨hRdef, hRpos, hRle, hQρ, hL, hbad, hgood, hwin, hwin', hroomT,
    hradii⟩, hLdef, hroom, hball⟩ := hsel
  have hdistσ := ObservedHistory.hdistσ_of_retained_P6R2 (Aκ := A + 3)
    (haT := fun k => (F.tower.history (ind k)).rescaleTime_mono_P6X (hc k) (haT k)) (hsT := hsT)
    (has := has) hA0 le_rfl (fun _ => one_pos) hRpos0 hRle hLdef hdiv hball
  have hsmallR : ∀ k, hasSmallParabolicCurvature
      ((F.tower.history (ind k)).rescale_P6N (r k ^ 2) (hc k)).toHistory
      ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (Tn k))
      ((F.tower.history (ind k)).castRescale_P6X (hc k) (Tn k) (pT k)) 1 := fun k => by
    have h := (F.tower.history (ind k)).hasSmallParabolicCurvature_rescale_P6X3 (hc k) (Tn k)
      (pT k) (hsmall k)
    rwa [hsq k, div_self (hr k).ne'] at h
  have hT₀l : ∀ k, T₀ k ≤ r k ^ 2 *
      ((F.tower.history (ind k)).rescaleTime_P6X (hc k) (aSeed k) : ℝ) := fun k => by
    rw [(F.tower.history (ind k)).mul_rescaleTime_P6X (hc k), hclock k]
    linarith [hlateT₀ k, htime k]
  have hQR : ∀ k, Qt k < R k := fun k => by
    have := (le_max_right _ _).trans ((hRx' k).trans (hRle k))
    linarith
  refine hPN A hA ind Tn pT r hr hlate htime hsmall hvol
    (fun k => (F.tower.history (ind k)).rescaleTime_P6X (hc k) (aSeed k))
    (fun k => (F.tower.history (ind k)).rescaleTime_mono_P6X (hc k) (haT k)) hclock'
    (fun k => ?_) hsmallR hT₀l
    (fun k => (F.tower.history (ind k)).seedTrace_rescale_P6X (hc k) (haT k) (hst k).some)
    σ y R hsT has L hRdef hRpos (fun k => (hRx0 k).trans (hRle k)) hQR hL hbad hgood hwin hwin'
    hroomT hradii hQρ hroom hball hdistσ
  rw [hclock' k]
  change 1 ≤ (Tn k : ℝ) / r k ^ 2 - 1 ^ 2
  rw [le_sub_iff_add_le, le_div_iff₀ (hc k)]
  linarith [htime k]

/-- **(b) 最小合同 ⇐ S5 + S11 + `hPNP`**（`_P6X3`；`A ≤ 1` 借 `max A 2`）。 -/
theorem canonicalLateCore_of_normalized_prefix_P6X3 {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters} {ε C1 C2 : ℝ} {Ctime : ℝ≥0}
    (hanti : AntitoneOn q.neckRadius (Ici 0))
    (hcan : HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2)
    (hder : TimeDerivativeSupply_C11E F q.neckRadius Ctime) (T₀ Qt : ℕ → ℝ)
    (hPN : ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
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
        False) :
    CanonicalLateCore_P6X F ε C1 C2 := by
  intro A hA
  have hA2 : 1 < max A 2 := lt_of_lt_of_le one_lt_two (le_max_right _ _)
  exact lateCoreAt_mono_P6X (lateCoreAt_of_normalized_prefix_P6X3 hanti hcan hder T₀ Qt hPN hA2)
    hA (le_max_left _ _)

/-- 旧形 ⇒ 新形：G4a `canonicalLateCore_of_normalizedS_P6X3`（旧 `hPNS`）由新形推出——`hPNP` 的新前件
（原尺度 `hsmall` / `hvol`、迟度、`Qt < R̃`、retained 四项）丢弃，`k+1 ≤ c·T̃n` 由 `c·(Tno/c) = Tno`。 -/
example : type_of% @canonicalLateCore_of_normalizedS_P6X3.{u} := by
  intro P g F q ε C1 C2 Ctime hanti hcan hder hPNS
  refine canonicalLateCore_of_normalized_prefix_P6X3 hanti hcan hder (fun _ => 0) (fun _ => 0) ?_
  intro _ _ ind Ho Tno pTo r hr hlate _ _ _ c hc K Kh Tn pT aSeed haT hclock h1 hsm _ seedTrace σ y
    R hsT has L hRdef hRpos hRr _ hL hsel hgood hwin hwin' hroomT hradii _ _ _ _
  exact hPNS ind c hc Tn pT
    (fun k => (hlate k).trans_eq ((Ho k).mul_rescaleTime_P6X (hc k) (Tno k)).symm) aSeed haT
    hclock h1 hsm seedTrace σ y R hsT has L hRdef hRpos hRr hL hsel hgood hwin hwin' hroomT hradii

end GC.LongTime.Ch11

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

open Perelman.CanonicalNeighborhood.FiniteHorn (SpatialCanonicalWitness)

namespace ObservedHistory

/-- **D-17 端到端，量词重排版（`_P6X3`）**：G4b `canonicalLateCore_of_normalizedS_hclos_P6X3` 的 prefix 重排：
`Ctime₀ T₀ Qt`（+ `Monotone`）在 selection 前；`hgapP` / `hrestP` 的前缀 = `hPNP`（原尺度种子 + `A` +
`hvol` + 迟度 + `Qt < R̃` + retained 四项）；`hgapP` 的 ∃ 只剩 `p pF recordsK a₀`。见文件头。 -/
theorem canonicalLateCore_of_normalizedS_hclos_prefix_P6X3 :
    ∃ epsW : ℝ, 0 < epsW ∧ ∀ ε : ℝ, 0 < ε → ε < 1 / 11 → ε ≤ epsW →
    ε ≤ crossingWindowNeckAccuracy.{u} → ε ≤ crossingNeckAccuracy.{u} → ε ≤ coneAccuracy →
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {C1 C2 : ℝ} {Ctime : ℝ≥0}, C ≤ C1 → C ≤ C2 → C.toNNReal ≤ Ctime →
      ∀ {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
        {q : CutoffParameters},
      AntitoneOn q.neckRadius (Ici 0) →
      GC.LongTime.Ch11.HistoryCanonicalSupply_C11S F q.neckRadius ε C1 C2 →
      GC.LongTime.Ch11.TimeDerivativeSupply_C11E F q.neckRadius Ctime →
      ∀ (Ctime₀ : ℝ≥0) (T₀ Qt : ℕ → ℝ), Monotone T₀ → Monotone Qt →
      (hgapP : ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
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
          (∀ k, ∃ j : Fin (Kh k).eventCount, (Kh k).time j.castSucc < (σ k : ℝ) ∧
          (σ k : ℝ) < (Kh k).time j.succ) →
          (∀ k : ℕ, (k : ℝ) + 1 < R k) →
        ∃ (p pF : ℕ → CutoffParameters)
          (recordsK : ∀ n (i : Fin (Ho n).eventCount),
            T₀ n ≤ (Ho n).time i.succ → GeometricCutoffRecord (Ho n).toHistory i (p n))
          (a₀ : ℕ → ℝ),
          Nonempty (∀ n i, GeometricCutoffRecord (Ho n).toHistory i (pF n)) ∧
          (∀ n, 0 < a₀ n) ∧
          (∀ n x, InFixedHamiltonIveyRegion ((Ho n).initialMetric 0) (a₀ n) x ∧
            -3 / a₀ n ≤ metricScalarAt ((Ho n).initialMetric 0) x) ∧
          (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) ∧
          (∀ n (i : Fin (Ho n).eventCount), T₀ n ≤ (Ho n).time i.succ →
            (pF n).delta ((Ho n).time i.succ) ≤ 1 / ((n : ℝ) + 1)) ∧
          (∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) ∧
          (∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) ∧
          (∀ n : ℕ, n + 2 ≤ (p n).modelOrder) ∧
          (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max (((n : ℝ) + 1) / c n) (Qt n / c n) ≤
            ((recordsK n i hi).static b).neck.scale) ∧
          (∀ᶠ n in atTop, ∀ i hi b, 1 ≤ a₀ n * ((recordsK n i hi).static b).neck.scale) ∧
          (∀ n, (Ho n).EventSlabsDerivative Ctime₀ (Qt n / c n) (Fin.last (Ho n).eventCount)) ∧
          (∀ (n : ℕ) (j' : Fin (K n).eventCount) (yG' : ((K n).stage j'.castSucc).Carrier),
        HEq (y n) yG' →
        (∃ (i : Fin (Ho n).eventCount) (hi : T₀ n ≤ (Ho n).time i.succ)
        (hl : i.succ ≤ j'.castSucc)
        (A : BackwardPointTrace (Ho n).toHistory i.succ j'.castSucc hl yG')
        (b : ((Ho n).toHistory.event i).RetainedBoundaryIndex)
        (x : standardCapWindow (p n).modelRadius),
        A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
          ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
          (σ n : ℝ) - (K n).time i.succ ≤
            (1 - 1 / ((n : ℝ) + 2)) * (c n * ((recordsK n i hi).static b).neck.scale)⁻¹) →
        (Kh n).HasSpatialCanonicalTimeControl ε C1 C2 Ctime (σ n) (y n)) ∧
          Nonempty (GC.LongTime.Ch11.Pre841Data_C11K Kh σ y R hRpos) ∧
          (∀ D T : ℝ, 0 < D → 0 < T → ∀ᶠ n in atTop,
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
              ENNReal.ofReal (L n / 4 / Real.sqrt (R n))) ∧
          (∃ (κ : ℝ) (ρV : ℕ → ℝ), 0 < κ ∧
            (Tendsto (fun n => ρV n * Real.sqrt (R n)) atTop atTop) ∧
            (∀ᶠ n in atTop, ∀ (j : Fin (Kh n).eventCount) (c : ((Kh n).stage j.castSucc).Carrier)
        (U : Set ((Kh n).stage j.castSucc).Carrier) (a t ρU : ℝ),
        (Tn n : ℝ) - 1 ^ 2 / 2 ≤ a → t ≤ (Tn n : ℝ) →
        (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ z ∈ U, ∀ zz cc : ((Kh n).stageAt τ).Carrier, HEq zz z → HEq cc c →
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) cc zz <
              ENNReal.ofReal ρU) →
        (∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ (hav : aSeed n ≤ τ) (hvt : τ ≤ Tn n), ∀ cc : ((Kh n).stageAt τ).Carrier, HEq cc c →
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                ((seedTrace n).point ((Kh n).activeStage τ) ((Kh n).activeStage_mono hav)
                  ((Kh n).activeStage_mono hvt)) cc + ENNReal.ofReal ρU ≤
              ENNReal.ofReal ((A + 3) * 1)) →
        ∀ (τ : Icc (0 : ℝ) (Kh n).horizon), a ≤ (τ : ℝ) → (τ : ℝ) ≤ t →
          (Kh n).time j.castSucc < τ → (τ : ℝ) < (Kh n).time j.succ →
          ∀ z ∈ U, ∀ zz : ((Kh n).stageAt τ).Carrier, HEq zz z →
          ∀ b : ℝ, 0 < b → b ≤ ρV n → (Kh n).isParabolicallyRmControlledBall τ zz b →
            ENNReal.ofReal κ * ENNReal.ofReal b ^ 3 ≤
              riemannianVolumeMeasure ThreeModel ((Kh n).stageAt τ).Carrier
                ((Kh n).stageMetric ((Kh n).activeStage τ) τ)
                (riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage τ) τ) zz b))) ∧
          (∀ Rad B σ₁ σ₂ : ℝ, σ₁ ≤ σ₂ → σ₂ < 0 → ∀ Dw Dd : ℝ, 0 < Dw → 0 < Dd →
        ∃ C : ℝ, 1 ≤ C ∧ ∀ᶠ n in atTop,
        ∀ (j' : Fin (Kh n).eventCount) (v : ℝ), (Kh n).time j'.castSucc < v →
          v < (Kh n).time j'.succ → (σ n : ℝ) + σ₁ / R n ≤ v → v ≤ σ n + σ₂ / R n →
        ∀ x₁ ∈ riemannianBallOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n)) (y n)
            (Dw / Real.sqrt (R n)),
        ∀ (hjσ : j'.castSucc ≤ (Kh n).activeStage (σ n))
          (tr : BackwardPointTrace (Kh n) j'.castSucc ((Kh n).activeStage (σ n)) hjσ x₁),
        ∀ (h1 : (Kh n).activeStage (aSeed n) ≤ j'.castSucc)
          (h2 : j'.castSucc ≤ (Kh n).activeStage (Tn n)) (w : ((Kh n).stage j'.castSucc).Carrier),
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
              ((seedTrace n).point j'.castSucc h1 h2) w ≤
            riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                  ((Kh n).activeStage_mono (hsT n))) (y n) +
              ENNReal.ofReal (L n / 2 / Real.sqrt (R n)) →
          riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric v)
              (tr.point j'.castSucc le_rfl hjσ) w < ENNReal.ofReal (Dd / Real.sqrt (R n)) →
          R n ≤ ((Kh n).event j').incoming.flow.scalar v w →
          ∀ x ∈ riemannianBallOf (((Kh n).event j').incoming.flow.base.metric v) w
              (Rad / Real.sqrt (((Kh n).event j').incoming.flow.scalar v w)),
          ∀ s : ℝ, v - B / ((Kh n).event j').incoming.flow.scalar v w ≤ s → s ≤ v →
            (Kh n).time j'.castSucc < s →
            riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric s)
                ((seedTrace n).point j'.castSucc h1 h2) x ≤
              riemannianEDistOf ((Kh n).stageMetric ((Kh n).activeStage (σ n)) (σ n))
                  ((seedTrace n).point ((Kh n).activeStage (σ n)) ((Kh n).activeStage_mono (has n))
                    ((Kh n).activeStage_mono (hsT n))) (y n) +
                ENNReal.ofReal (L n / Real.sqrt (R n)) →
            ∀ z : ((Kh n).stage j'.castSucc).Carrier,
              riemannianEDistOf (((Kh n).event j').incoming.flow.base.metric s) x z <
                  ENNReal.ofReal
                    (1 / Real.sqrt (C * ((Kh n).event j').incoming.flow.scalar v w)) →
                ((Kh n).event j').incoming.flow.scalar s z ≤
                  C * ((Kh n).event j').incoming.flow.scalar v w)) →
      (hrestP : ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
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
        ((∀ k, (Kh k).time (Fin.last (Kh k).eventCount) < (σ k : ℝ) ∧ (σ k : ℝ) < (Kh k).horizon) ∨
          (∀ k, ¬ ∃ W : SpatialCanonicalWitness
            ((Kh k).stageMetric ((Kh k).activeStage (σ k)) (σ k))
            ε C1 C2 (y k), W.capTubeHasNeckChart ε)) → False) →
      GC.LongTime.Ch11.CanonicalLateCore_P6X F ε C1 C2 := by
  obtain ⟨epsW, hepsW, hB⟩ := false_of_selected_eventInterior_lateHI_P6X2.{u}
  obtain ⟨Phi, hPhi, hK⟩ := KdataRescale_P6X3.{u}
  refine ⟨epsW, hepsW, fun ε hε hsmall' hεW hεX hεN hεcone => ?_⟩
  obtain ⟨C, hC, hB'⟩ := hB ε hε hsmall' hεW hεX hεN hεcone
  refine ⟨C, hC, fun {C1 C2 Ctime} hC1 hC2 hCt => ?_⟩
  intro P g F q hanti hcan hder Ctime₀ T₀ Qt hT₀m hQm hgap hrest
  have evb : ∀ A : ℝ, 1 < A → ∀ (ind : ℕ → ℕ),
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
            (∀ k, ∃ j : Fin (Kh k).eventCount, (Kh k).time j.castSucc < (σ k : ℝ) ∧
            (σ k : ℝ) < (Kh k).time j.succ) →
            (∀ k : ℕ, (k : ℝ) + 1 < R k) →
          False := by
    intro A hA ind Ho Tno pTo r hr hlate htime hsmallo hvolo c hc K Kh Tn pT aSeed haT hclock h1
      hsm hT₀l seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hroomT hradii
      hQρ hroom hball hdistσ hev hlt
    obtain ⟨p, pF, recordsK, a₀, ⟨recordsF⟩, ha₀, hHI, hcanK, hδF, hacc, hrad, hord, hscaleK,
      hbirthA, hslabK, hcwpL, ⟨d⟩, hdistQ, ⟨κ, ρV, hκ, hρV, hκR⟩, hscalU⟩ :=
      hgap A hA ind Tno pTo r hr hlate htime hsmallo hvolo aSeed haT hclock h1 hsm hT₀l seedTrace
        σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hroomT hradii hQρ hroom hball
        hdistσ hev hlt
    obtain ⟨hHI', hcanK', hδF', hscaleK', hbirthA', hpinch', hslab'⟩ :=
      hK Ho c hc Ctime₀ (fun n => Qt n / c n) T₀ p pF recordsK a₀ recordsF ha₀ hHI hcanK hδF
        hscaleK hbirthA hslabK
    have hT₀a' : ∀ n, max 1 (T₀ n / c n) ≤ (aSeed n : ℝ) := fun n => by
      refine max_le (h1 n) ?_
      rw [div_le_iff₀ (hc n)]
      linarith [hT₀l n]
    have hQR' : ∀ n, c n * (Qt n / c n) < R n := fun n => by
      rw [mul_div_cancel₀ _ (hc n).ne']
      exact hQR n
    have hR1 : ∀ n, 1 ≤ R n := fun n => by
      have := hRr n
      have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    have hRr1 : Tendsto (fun n => R n * (fun _ : ℕ => (1 : ℝ)) n ^ 2) atTop atTop := by
      simp only [one_pow, mul_one]
      exact tendsto_atTop_mono hRr (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    have hlateR : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, 1 ≤ R n * ((σ n : ℝ) - T / R n) := by
      intro T hT
      filter_upwards [hwin T hT] with n hn
      have ha1 : (1 : ℝ) ≤ (σ n : ℝ) - T / R n := (h1 n).trans hn
      calc (1 : ℝ) ≤ R n * 1 := by linarith [hR1 n]
        _ ≤ R n * ((σ n : ℝ) - T / R n) := mul_le_mul_of_nonneg_left ha1 (by linarith [hR1 n])
    have hclosG := hclosG_of_firstExit_P6M4 Kh Tn aSeed σ haT hsT has pT seedTrace y R L hRpos
      (fun _ => 1) hL hsm hclock hRr1 hwin hlateR le_rfl
      (fun n => (Ho n).toHistory.hpin_rescale_P6X3 (hc n) (recordsF n) (ha₀ n) (hHI n)) hscalU
    refine hB' hC1 hC2 hCt hPhi (K := K) (Q := fun n => c n * (Qt n / c n))
      (T₀ := fun n => max 1 (T₀ n / c n)) (p := fun n => (p n).rescale_P6N (c n) (hc n))
      (pF := fun n => (pF n).rescale_P6N (c n) (hc n)) (a₀ := fun n => a₀ n / c n)
      (recordsK := fun n => (Ho n).recordsKRescale_P6X3 (hc n) (recordsK n))
      (fun n i => (recordsF n i).rescale_P6M (c n) (hc n)) hHI' hcanK' hδF' hacc hrad hord hscaleK'
      hbirthA' hpinch' hslab' Kh rfl σ y hev R hRdef hRpos hlt hQR'
      (fun n j' yG' hy hcw => ?_) d Tn aSeed haT hsT has hT₀a' pT seedTrace L hL 4 (by norm_num)
      hgood hwin hdistQ (Aκ := A + 3) hκ (fun _ => 1) ρV hρV hroom hdistσ hκR hclosG hsel
    obtain ⟨i, hi, hl, A', b, x, hA', hx, ht⟩ := hcw
    have hi' : T₀ n ≤ (Ho n).time i.succ :=
      RetainedCoreHistory.le_time_of_rescale_P6X3 (hc n) (t := (Ho n).time i.succ) hi
    refine hcwpL n j' yG' hy ⟨i, hi', hl, (Ho n).traceOfRescale_P6N (c n) (hc n) A', b, x, ?_, hx,
      ?_⟩
    · exact hA'.trans (congrArg (fun w => w x)
        (((recordsK n i hi').static b).rescale_P6M_window (c n) (hc n)))
    · exact ht.trans_eq (congrArg (fun z => (1 - 1 / ((n : ℝ) + 2)) * z⁻¹)
        (((recordsK n i hi').static b).rescale_P6M_scale (c n) (hc n)))
  refine GC.LongTime.Ch11.canonicalLateCore_of_normalized_prefix_P6X3 hanti hcan hder T₀ Qt ?_
  intro A hA ind Ho Tno pTo r hr hlate htime hsmallo hvolo c hc K Kh Tn pT aSeed haT hclock h1
    hsm hT₀l seedTrace σ y R hsT has L hRdef hRpos hRr hQR hL hsel hgood hwin hwin' hroomT hradii
    hQρ hroom hball hdistσ
  have key : ∀ φ : ℕ → ℕ, StrictMono φ →
      ((∀ k, ∃ j : Fin (Kh (φ k)).eventCount, (Kh (φ k)).time j.castSucc < (σ (φ k) : ℝ) ∧
          (σ (φ k) : ℝ) < (Kh (φ k)).time j.succ) ∧ ∀ k : ℕ, (k : ℝ) + 1 < R (φ k)) ∨
        (∀ k, (Kh (φ k)).time (Fin.last (Kh (φ k)).eventCount) < (σ (φ k) : ℝ) ∧
          (σ (φ k) : ℝ) < (Kh (φ k)).horizon) ∨
        (∀ k, ¬ ∃ W : SpatialCanonicalWitness ((Kh (φ k)).stageMetric
            ((Kh (φ k)).activeStage (σ (φ k))) (σ (φ k))) ε C1 C2 (y (φ k)),
          W.capTubeHasNeckChart ε) → False := by
    intro φ hφ hcls
    have hφt := hφ.tendsto_atTop
    have hlate' : ∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno (φ k) : ℝ) := fun k =>
      (GC.LongTime.Ch11.natCast_succ_le_of_strictMono_P6X hφ k).trans (hlate (φ k))
    have hRr' : ∀ k : ℕ, (k : ℝ) + 1 ≤ R (φ k) := fun k =>
      (GC.LongTime.Ch11.natCast_succ_le_of_strictMono_P6X hφ k).trans (hRr (φ k))
    have hT₀l' : ∀ k, T₀ k ≤ c (φ k) * (aSeed (φ k) : ℝ) := fun k =>
      (hT₀m (hφ.id_le k)).trans (hT₀l (φ k))
    have hQR' : ∀ k, Qt k < R (φ k) := fun k => (hQm (hφ.id_le k)).trans_lt (hQR (φ k))
    rcases hcls with ⟨hev, hlt⟩ | hcls'
    · exact evb A hA (fun k => ind (φ k)) (fun k => Tno (φ k)) (fun k => pTo (φ k))
        (fun k => r (φ k)) (fun k => hr (φ k)) hlate' (fun k => htime (φ k))
        (fun k => hsmallo (φ k)) (fun k => hvolo (φ k)) (fun k => aSeed (φ k))
        (fun k => haT (φ k)) (fun k => hclock (φ k)) (fun k => h1 (φ k)) (fun k => hsm (φ k))
        hT₀l' (fun k => seedTrace (φ k)) (fun k => σ (φ k)) (fun k => y (φ k)) (fun k => R (φ k))
        (fun k => hsT (φ k)) (fun k => has (φ k)) (fun k => L (φ k)) (fun k => hRdef (φ k))
        (fun k => hRpos (φ k)) hRr' hQR' (hL.comp hφt) (fun k => hsel (φ k)) (fun k => hgood (φ k))
        (fun T hT => hφt.eventually (hwin T hT)) (fun T hT => hφt.eventually (hwin' T hT))
        (hroomT.comp hφt) (hradii.comp hφt) (fun k => hQρ (φ k)) (fun k => hroom (φ k))
        (fun k => hball (φ k)) (hφt.eventually hdistσ) hev hlt
    · exact hrest A hA (fun k => ind (φ k)) (fun k => Tno (φ k)) (fun k => pTo (φ k))
        (fun k => r (φ k)) (fun k => hr (φ k)) hlate' (fun k => htime (φ k))
        (fun k => hsmallo (φ k)) (fun k => hvolo (φ k)) (fun k => aSeed (φ k))
        (fun k => haT (φ k)) (fun k => hclock (φ k)) (fun k => h1 (φ k)) (fun k => hsm (φ k))
        hT₀l' (fun k => seedTrace (φ k)) (fun k => σ (φ k)) (fun k => y (φ k)) (fun k => R (φ k))
        (fun k => hsT (φ k)) (fun k => has (φ k)) (fun k => L (φ k)) (fun k => hRdef (φ k))
        (fun k => hRpos (φ k)) hRr' hQR' (hL.comp hφt) (fun k => hsel (φ k)) (fun k => hgood (φ k))
        (fun T hT => hφt.eventually (hwin T hT)) (fun T hT => hφt.eventually (hwin' T hT))
        (hroomT.comp hφt) (hradii.comp hφt) (fun k => hQρ (φ k)) (fun k => hroom (φ k))
        (fun k => hball (φ k)) (hφt.eventually hdistσ) hcls'
  obtain ⟨ψ, hψ, hcls⟩ := exists_strictMono_interior_or_boundary_P6S (Kh := Kh) σ y hsel
  rcases hcls with hev | hfin | hbd
  · have hs : StrictMono fun k : ℕ => ψ (k + 1) :=
      hψ.comp fun a b hab => Nat.add_lt_add_right hab 1
    refine key (fun k => ψ (k + 1)) hs (Or.inl ⟨fun k => hev (k + 1), fun k => ?_⟩)
    have hk1 : ((k + 1 : ℕ) : ℝ) ≤ (ψ (k + 1) : ℝ) := by exact_mod_cast hψ.id_le (k + 1)
    have hk2 := hRr (ψ (k + 1))
    push_cast at hk1
    linarith
  · exact key ψ hψ (Or.inr (Or.inl hfin))
  · exact key ψ hψ (Or.inr (Or.inr hbd))

end ObservedHistory

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
