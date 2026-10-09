import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DrvResEngineSupplyHNS
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6DrvResJ10DJ4T0X

/-!
# T0K：HNR 新义务在 `aSeed` cutoff 上的引擎供给（后缀 `_T0K`）

HNRSUP（`drvResE_records_of_engine_HNS`）取 Ho cutoff `max T₀ (c(σ − L/R))`，K 帧
`T₀K = max 1 (max T₀ (c(σ−L/R))/c)`，与 J10 的 `hT₀X : T₀K ≤ σ − (1/100)²` 冲突
（`hns_T0K_not_le_T0X`）。HT0X 的 DJ4 取 `T₀K ≤ max 1 (T₀/c)`，但在该窗口上 HNR 的 birth 因子
对 Ho 时刻 `t ∈ [T₀, Tno/2)` 的早期事件无来源（`early_recent_dir_T0K`：recent 只给 `ρ(2t)⁻²`，
方向错）。本文件取 J6REC 的 `K₀ := c·aSeed = Tno − c` 型 cutoff：

* (i) 逐档 `hfine` 阈值并入 `Θ`，`Θ ≤ T₀ ≤ c·aSeed`（合同 `hlate`）；
* (ii) `Tno ≤ 2K₀` 由 `2c < Tno` 得，recent 阈值 `≤ T₀ ≤ K₀ ≤ Tno`；只在 SCRS⁺ `hfine` 解包的实际
  records 上（`neck.scale` 与参考 `records` 相等 = 同尺度见证，D-25-3）；
* (iii) 晚期 `δ → 0` scale 下界阈值并入 `Θ`；
* 同一 `T₀K := max 1 (c·aSeed/c) = aSeed` 上 `hT₀X` 对 `∀ n` 成立（DJ4 合同核 `hT0X_of_contract_T0X`
  以 `T₀ := c·aSeed` 实例化），HNR 尾条件由合同 `hwin` 给出。
不加顶层 binder；元组 `(Nf ζ Rn δ₀ m₀)` 为参数（R53）。

裁定（O-CH11-T0K G0）：核内只有一个 `∃ T₀K`（F-24-8 同元组），但没有消费点要求 `T₀K` 落在 recent 窗；
HNS 的 `c(σ−L/R)` 分量只是供给侧 cutoff。故取单一 `T₀K := aSeed`，DJ4 孪生在 HNR 线不用。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **障碍方向（`_T0K`，PROVED）**：`2t ≤ T` 时 recent 在 `2t` 处给出的尺度 `(ρ(2t)²)⁻¹` 不超过
`(ρ(T)²)⁻¹`；故 Ho 时刻 `t < Tno/2` 的事件，recent 路线给不出 birth 所需的 `N·(ρ(Tno)²)⁻¹`。 -/
theorem early_recent_dir_T0K {q : CutoffParameters} (hanti : AntitoneOn q.neckRadius (Ici 0))
    {t T : ℝ} (ht : 0 ≤ t) (htT : 2 * t ≤ T) :
    (q.neckRadius (2 * t) ^ 2)⁻¹ ≤ (q.neckRadius T ^ 2)⁻¹ := by
  have h2t : (0 : ℝ) ≤ 2 * t := by linarith
  have hT : (0 : ℝ) ≤ T := h2t.trans htT
  have hρT := q.neckRadius_pos T hT
  have hle : q.neckRadius T ≤ q.neckRadius (2 * t) :=
    hanti (Set.mem_Ici.mpr h2t) (Set.mem_Ici.mpr hT) htT
  exact inv_anti₀ (pow_pos hρT 2) (pow_le_pow_left₀ hρT.le hle 2)

/-- `aSeed` cutoff 的 K 帧阈值：`max 1 (c·a/c) = a`（`1 ≤ a`）。 -/
theorem t0K_eq_aSeed_T0K {c a : ℝ} (hc : 0 < c) (h1 : 1 ≤ a) : max 1 (c * a / c) = a := by
  have h : c * a / c = a := by field_simp
  rw [h]
  exact max_eq_right h1

/-- **`hT₀X` 于 `aSeed` cutoff（`_T0K`，PROVED）**：DJ4 合同核 `hT0X_of_contract_T0X` 取
`T₀ := c·aSeed`（`hlate` 为 `le_rfl`），`T₀K := max 1 (c·aSeed/c)`，对 `∀ n`。 -/
theorem hT0X_aSeed_T0K {c a Tn σ L R : ℕ → ℝ} (hc : ∀ n, 0 < c n) (hR : ∀ n, 0 < R n)
    (hclock : ∀ n, a n = Tn n - 1 ^ 2) (h1 : ∀ n, 1 ≤ a n)
    (hroom : ∀ n, Tn n - 1 ^ 2 / 2 ≤ σ n - L n ^ 2 / R n) :
    ∀ n, max 1 (c n * a n / c n) ≤ σ n - (1 / 100 : ℝ) ^ 2 :=
  hT0X_of_contract_T0X (T₀ := fun n => c n * a n) (T₀K := fun n => max 1 (c n * a n / c n))
    hc hR (fun _ => le_rfl) hclock h1 hroom (fun _ => le_rfl)

/-- **HNR 尾条件于 `aSeed` cutoff（`_T0K`，PROVED）**：合同 `hwin`（`aSeed ≤ σ − T/R` eventually）。 -/
theorem t0K_tail_aSeed_T0K {c a σ R : ℕ → ℝ} (hc : ∀ n, 0 < c n) (h1 : ∀ n, 1 ≤ a n)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, a n ≤ σ n - T / R n) :
    ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, max 1 (c n * a n / c n) ≤ σ n - T / R n := by
  intro T hT
  filter_upwards [hwin T hT] with n hn
  rw [t0K_eq_aSeed_T0K (hc n) (h1 n)]
  exact hn

/-- **(ii) Ho 帧 birth 于 `aSeed` cutoff（`_T0K`，PROVED）**：Ho 事件 `c·aSeed ≤ tᵢ`，
`aSeed = Tn − 1`、`2c < Tno` ⇒ `Tno ≤ 2tᵢ`；recent（因子 `max (n+1) (Nf n)`）与 lateLambda 阈值
`≤ T₀ ≤ c·aSeed`。 -/
theorem birthN_aSeed_T0K {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (records : GC.LongTime.Ch11.CutoffRecords_C11S F q)
    (hrcs : GC.LongTime.Ch11.RecentCutoffSupply_C11S records)
    (hanti : AntitoneOn q.neckRadius (Ici 0)) (hδq : Tendsto q.delta atTop (𝓝 0))
    (ind : ℕ → ℕ) (Nf : ℕ → ℝ) {T₀ c aS Tn Tno : ℕ → ℝ}
    (hTr : ∀ n, recentThrN_HNS hrcs Nf n ≤ T₀ n)
    (hT₀Λ : ∀ n, lateLambdaThr_P6HA q hδq ≤ T₀ n) (hT0k : ∀ n, T₀ n ≤ c n * aS n)
    (hc : ∀ n, 0 < c n) (hTno : ∀ n, Tno n = c n * Tn n) (hTno0 : ∀ n, 0 ≤ Tno n)
    (h2c : ∀ n, 2 * c n < Tno n) (haS : ∀ n, aS n = Tn n - 1 ^ 2)
    (n : ℕ) (i : Fin (F.tower.history (ind n)).eventCount)
    (hi : c n * aS n ≤ (F.tower.history (ind n)).time i.succ)
    (b : ((F.tower.history (ind n)).toHistory.event i).RetainedBoundaryIndex) :
    max ((n : ℝ) + 1) (Nf n) * (q.neckRadius (Tno n) ^ 2)⁻¹ ≤
      ((records (ind n) i).static b).neck.scale := by
  have hM1 : 1 ≤ max ((n : ℝ) + 1) (Nf n) :=
    le_trans (by linarith [Nat.cast_nonneg (α := ℝ) n]) (le_max_left _ _)
  have hcut : Tno n - c n = c n * aS n := by
    rw [haS n, hTno n]; ring
  have hlate : Tno n ≤ 2 * (F.tower.history (ind n)).time i.succ := by
    have := h2c n
    linarith
  have hseed : T₀ n ≤ Tno n := by
    have := hc n
    linarith [hT0k n]
  set η : ℝ := 1 / (2 * max ((n : ℝ) + 1) (Nf n)) with hηdef
  have hηpos : 0 < η := by positivity
  have hηN : 2 * η ^ 2 * max ((n : ℝ) + 1) (Nf n) ≤ 1 := by
    have heq : 2 * η ^ 2 * max ((n : ℝ) + 1) (Nf n) = 1 / (2 * max ((n : ℝ) + 1) (Nf n)) := by
      rw [hηdef]; field_simp
    rw [heq, div_le_one (by positivity)]
    linarith
  obtain ⟨-, hrec⟩ := Classical.choose_spec (hrcs η (by positivity))
  exact sepRhoPlus'_of_recentSupply_P6SF (records (ind n) i) b hanti
    (lateLambda_of_thr_P6HA q hδq (((hT₀Λ n).trans (hT0k n)).trans hi))
    hηpos.le hηN (hTno0 n) ((hTr n).trans hseed) hlate
    (fun t ht hm h => hrec t ht (ind n) i hm h)

/-- **HNR 新义务 + `hT₀X` 的同一 `T₀K` 引擎供给（`_T0K`，PROVED 相对 `hrcs`、`hfine`、`hanti`、
`hδq`、`ha₀`/`hHI`）**。`∃ Θ`（档 / recent / `δ₀` / lateLambda / 晚期 scale 阈值的 max，与 `ind`、`c`、
`Tno` 无关），对一切 `T₀ ≥ Θ` 与合同数值前提（`aSeed = Tn − 1`、`1 ≤ aSeed`、`T₀ ≤ c·aSeed`、`hroom`、
`hwin`），存在原帧参数列 `p` 与实际 records `recKHo`（Ho cutoff `c·aSeed`），其 K 帧搬运
（`recordsKRescale_P6X3`，阈值 `T₀K n := max 1 (c·aSeed/c) = aSeed`，`qK := p.rescale_P6N`）满足
(i) 档、canonical window、late `δ ≤ δ₀ n`；(ii) birth `max (n+1) (Nf n) · max (n+1) (ρ̃(Tn)²)⁻¹ ≤ scale`
（∀ n）；(iii) `1 ≤ (a₀/c)·scale`（∀ n）与 HI；且同一 `T₀K` 上 `hT₀X`（∀ n）与 HNR 尾条件。 -/
theorem drvResE_records_of_engine_T0K {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (records : GC.LongTime.Ch11.CutoffRecords_C11S F q)
    (hrcs : GC.LongTime.Ch11.RecentCutoffSupply_C11S records)
    (hanti : AntitoneOn q.neckRadius (Ici 0)) (hδq : Tendsto q.delta atTop (𝓝 0))
    (hfine : ∀ (D ζ : ℝ) (m : ℕ), 0 < ζ → ∃ T₀ : ℝ, ∀ n, ∃ p : CutoffParameters,
      D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ζ ∧ m ≤ p.modelOrder ∧
      ∃ records' : ∀ i : Fin (F.tower.history n).eventCount,
          T₀ ≤ (F.tower.history n).time i.succ →
          GeometricCutoffRecord (F.tower.history n).toHistory i p,
        (∀ i hi b, ((records' i hi).static b).hasCanonicalWindow) ∧
        ∀ i hi b, ((records' i hi).static b).neck.scale = ((records n i).static b).neck.scale)
    {a₀ : ℝ} (ha₀ : 0 < a₀)
    (hHI : ∀ n x, InFixedHamiltonIveyRegion ((F.tower.history n).initialMetric 0) a₀ x ∧
      -3 / a₀ ≤ metricScalarAt ((F.tower.history n).initialMetric 0) x)
    (Nf ζ Rn δ₀ : ℕ → ℝ) (m₀ : ℕ → ℕ) (hζ : ∀ n, 0 < ζ n) (hδ₀ : ∀ n, 0 < δ₀ n) :
    ∃ Θ : ℕ → ℝ, ∀ T₀ : ℕ → ℝ, (∀ n, Θ n ≤ T₀ n) →
      ∀ (ind : ℕ → ℕ) (c σ L R Tn Tno aS : ℕ → ℝ) (hc : ∀ n, 0 < c n),
      (∀ n, Tno n = c n * Tn n) → (∀ n, 0 ≤ Tno n) → (∀ n, 2 * c n < Tno n) →
      (∀ n, aS n = Tn n - 1 ^ 2) → (∀ n, 1 ≤ aS n) → (∀ n, T₀ n ≤ c n * aS n) →
      (∀ n, Tn n - 1 ^ 2 / 2 ≤ σ n - L n ^ 2 / R n) → (∀ n : ℕ, (n : ℝ) + 1 ≤ R n) →
      (∀ n, R n ≤ c n * (q.neckRadius (Tno n) ^ 2)⁻¹) →
      (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, aS n ≤ σ n - T / R n) →
      ∃ (p : ℕ → CutoffParameters)
        (recKHo : ∀ n (i : Fin (F.tower.history (ind n)).eventCount),
          c n * aS n ≤ (F.tower.history (ind n)).time i.succ →
          GeometricCutoffRecord (F.tower.history (ind n)).toHistory i (p n)),
        (∀ n, (p n).modelAccuracy ≤ ζ n) ∧ (∀ n, Rn n ≤ (p n).modelRadius) ∧
        (∀ n, m₀ n ≤ (p n).modelOrder) ∧
        (∀ n i hi b, ((recKHo n i hi).static b).hasCanonicalWindow) ∧
        (∀ n (i : Fin ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).eventCount),
          max 1 (c n * aS n / c n) ≤
            ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time i.succ →
          (q.rescale_P6N (c n) (hc n)).delta
            (((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time i.succ) ≤ δ₀ n) ∧
        (∀ n (i : Fin ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).eventCount)
          (hi : max 1 (c n * aS n / c n) ≤
            ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time i.succ) b,
          max ((n : ℝ) + 1) (Nf n) * max ((n : ℝ) + 1)
              ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ ≤
            ((((F.tower.history (ind n)).recordsKRescale_P6X3 (hc n) (recKHo n) i hi).static b
              ).neck.scale)) ∧
        (∀ n (i : Fin ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).eventCount)
          (hi : max 1 (c n * aS n / c n) ≤
            ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time i.succ) b,
          1 ≤ a₀ / c n *
            ((((F.tower.history (ind n)).recordsKRescale_P6X3 (hc n) (recKHo n) i hi).static b
              ).neck.scale)) ∧
        (∀ n x, InFixedHamiltonIveyRegion
            (((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).initialMetric 0) (a₀ / c n) x ∧
          -3 / (a₀ / c n) ≤ metricScalarAt
            (((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).initialMetric 0) x) ∧
        (∀ n, max 1 (c n * aS n / c n) ≤ σ n - (1 / 100 : ℝ) ^ 2) ∧
        (∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, max 1 (c n * aS n / c n) ≤ σ n - T / R n) := by
  classical
  obtain ⟨Ts, hTs⟩ := lateScale_of_delta_HNS records hanti hδq
    (S := max 1 (1 / a₀)) (le_max_left _ _)
  choose Tf hTf using fun n => hfine (Rn n) (ζ n) (m₀ n) (hζ n)
  have hd : ∀ n, ∃ T : ℝ, ∀ s ≥ T, q.delta s ≤ δ₀ n := fun n =>
    Filter.eventually_atTop.mp (hδq.eventually (ge_mem_nhds (hδ₀ n)))
  choose Td hTd using hd
  refine ⟨fun n => max (Tf n) (max (recentThrN_HNS hrcs Nf n) (max (Td n)
    (max (lateLambdaThr_P6HA q hδq) Ts))), ?_⟩
  intro T₀ hT ind c σ L R Tn Tno aS hc hTno hTno0 h2c haS h1 hT0k hroom hRr hRρ hwin
  choose p hpD hpacc hpord rec' hcan hsc using fun n => hTf n (ind n)
  have hRpos : ∀ n, 0 < R n := fun n =>
    lt_of_lt_of_le (Nat.cast_add_one_pos n) (hRr n)
  have hK : ∀ n s, c n * aS n ≤ s → T₀ n ≤ s := fun n s h => (hT0k n).trans h
  have hle1 : ∀ n s, T₀ n ≤ s → Tf n ≤ s := fun n s h =>
    ((le_max_left _ _).trans (hT n)).trans h
  have hle3 : ∀ n s, T₀ n ≤ s → Td n ≤ s := fun n s h =>
    ((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (hT n)).trans h
  have hle5 : ∀ n s, T₀ n ≤ s → Ts ≤ s := fun n s h =>
    (((((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans (hT n)).trans h
  have hrec : ∀ n (i : Fin (F.tower.history (ind n)).eventCount),
      c n * aS n ≤ (F.tower.history (ind n)).time i.succ →
      Tf n ≤ (F.tower.history (ind n)).time i.succ := fun n i hi => hle1 n _ (hK n _ hi)
  have hTrN : ∀ n, recentThrN_HNS hrcs Nf n ≤ T₀ n := fun n =>
    ((le_max_left _ _).trans (le_max_right _ _)).trans (hT n)
  have hΛN : ∀ n, lateLambdaThr_P6HA q hδq ≤ T₀ n := fun n =>
    ((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans (hT n)
  have hρK : ∀ n, ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ =
      c n * (q.neckRadius (Tno n) ^ 2)⁻¹ := by
    intro n
    change ((q.neckRadius (c n * Tn n) / Real.sqrt (c n)) ^ 2)⁻¹ = _
    rw [← hTno n, div_pow, Real.sq_sqrt (hc n).le, inv_div, div_eq_mul_inv]
  have hcoarse : ∀ n (i : Fin (F.tower.history (ind n)).eventCount)
      (hi : c n * aS n ≤ (F.tower.history (ind n)).time i.succ) b,
      max ((n : ℝ) + 1) (Nf n) * (q.neckRadius (Tno n) ^ 2)⁻¹ ≤
        ((rec' n i (hrec n i hi)).static b).neck.scale := by
    intro n i hi b
    rw [hsc n i (hrec n i hi) b]
    exact birthN_aSeed_T0K records hrcs hanti hδq ind Nf hTrN hΛN hT0k hc hTno hTno0 h2c haS
      n i hi b
  refine ⟨p, fun n i hi => rec' n i (hrec n i hi), hpacc, hpD, hpord,
    fun n i hi b => hcan n i (hrec n i hi) b, ?_, ?_, ?_, ?_,
    hT0X_aSeed_T0K hc hRpos haS h1 hroom, t0K_tail_aSeed_T0K hc h1 hwin⟩
  · intro n i hi
    exact (F.tower.history (ind n)).hδF_rescale_P6X3 (hc n) (pF := q)
      (T₀ := c n * aS n) (δ := δ₀ n)
      (fun i' hi' => hTd n _ (hle3 n _ (hK n _ hi'))) i hi
  · intro n i hi b
    have habs : ((n : ℝ) + 1) / c n ≤ (q.neckRadius (Tno n) ^ 2)⁻¹ := by
      rw [div_le_iff₀ (hc n), mul_comm]
      exact (hRr n).trans (hRρ n)
    have key := (F.tower.history (ind n)).hscaleK_rescale_P6X3 (hc n)
      (fun i' hi' => rec' n i' (hrec n i' hi')) (T₀ := c n * aS n)
      (A := max ((n : ℝ) + 1) (Nf n)) (B := (n : ℝ) + 1) (Q := (q.neckRadius (Tno n) ^ 2)⁻¹)
      (fun i' hi' b' => by
        rw [max_eq_right habs]
        exact hcoarse n i' hi' b') i hi b
    rw [hρK n]
    exact key
  · intro n i hi b
    refine (F.tower.history (ind n)).hbirthA_rescale_P6X3 (hc n)
      (fun i' hi' => rec' n i' (hrec n i' hi')) (T₀ := c n * aS n)
      (a₀ := a₀) (fun i' hi' b' => ?_) i hi b
    have hS := hTs (ind n) i' (hle5 n _ (hK n _ hi')) b'
    change 1 ≤ a₀ * ((rec' n i' (hrec n i' hi')).static b').neck.scale
    rw [hsc n i' (hrec n i' hi') b']
    have h1' : 1 / a₀ ≤ ((records (ind n) i').static b').neck.scale :=
      (le_max_right _ _).trans hS
    rw [div_le_iff₀ ha₀] at h1'
    linarith
  · intro n x
    exact (F.tower.history (ind n)).hHI_rescale_P6X3 (hc n) (fun x' => hHI (ind n) x') x

/-- **`hT₀X` 的 `∀ᶠ` 形（`_T0K`，PROVED）**：`DrvResE_DJ3_HNR_JT` / `DrvResE_DJ3_JT` 的
`∀ᶠ n, T₀K n ≤ σ n − (1/100)²` 合取，于 `T₀K := max 1 (c·aSeed/c)`。 -/
theorem hT0X_ev_aSeed_T0K {c a Tn σ L R : ℕ → ℝ} (hc : ∀ n, 0 < c n) (hR : ∀ n, 0 < R n)
    (hclock : ∀ n, a n = Tn n - 1 ^ 2) (h1 : ∀ n, 1 ≤ a n)
    (hroom : ∀ n, Tn n - 1 ^ 2 / 2 ≤ σ n - L n ^ 2 / R n) :
    ∀ᶠ n in atTop, max 1 (c n * a n / c n) ≤ σ n - (1 / 100 : ℝ) ^ 2 :=
  Filter.Eventually.of_forall (hT0X_aSeed_T0K hc hR hclock h1 hroom)

/-- consumer（`_T0K`）：`aSeed` cutoff 的 K 帧阈值即 `aSeed`。 -/
example (c a : ℝ) (hc : 0 < c) (h1 : 1 ≤ a) : max 1 (c * a / c) = a :=
  t0K_eq_aSeed_T0K hc h1

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
