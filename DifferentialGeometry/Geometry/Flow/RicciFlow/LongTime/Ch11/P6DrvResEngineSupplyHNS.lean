import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HgapWireJ6P6HGW
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KdataRescaleP6X3
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GapWireKP6WR
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6LateSupplyAntiP6M3

/-!
# HNRSUP：`DrvResE_*_HNR` 新义务的引擎供给（后缀 `_HNS`）

HNR 孪生给 DrvResE producer 的三项新义务：(i) records 输出档 `ζ n / Rn n / m₀ n / δ₀ n`；
(ii) birth 因子 `max (n+1) (Nf n)`；(iii) `1 ≤ a₀K·scale` 对 `∀ n`。本文件在 K 帧给出供给：

* (i) 逐档 `n`：`hfine`（SCRS⁺ (9) 投影，`hfine_of_scrsPlus_RU`）在档 `(Rn n, ζ n, m₀ n)` 的阈值
  `Tf n`（与 `ind` 无关）并入 hresJ 槽的 `Θ`，故对给定 `ind` 的每个 `n` 成立，不取子列；
* (ii) `j6_of_recent_seq_P6HGW` 同法（recent 阈值并入 `T₀`），因子 `N := max (n+1) (Nf n)`，
  `η = 1/(2N)`；fine records 的 `neck.scale` 等于粗 records 的，粗 records 上用 `RecentCutoffSupply`；
* (iii) 粗 records 晚期 `δ → 0` ⇒ `scale ≥ S := max 1 (1/a₀)`（与 `c` 无关），K 帧 `a₀K := a₀/c`。
元组 `(Nf ζ Rn δ₀ m₀)` 为参数（R53：引擎实际元组传入）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- recent 阈值（因子 `N` 版）：`η_n = 1/(2·max (n+1) (Nf n))` 处 `RecentCutoffSupply_C11S` 的 `T`。 -/
def recentThrN_HNS {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    {records : GC.LongTime.Ch11.CutoffRecords_C11S F q}
    (hrcs : GC.LongTime.Ch11.RecentCutoffSupply_C11S records) (Nf : ℕ → ℝ) (n : ℕ) : ℝ :=
  Classical.choose (hrcs (1 / (2 * max ((n : ℝ) + 1) (Nf n))) (by positivity))

/-- **(ii) Ho 帧（`_HNS`，PROVED）**：`max (n+1) (Nf n) · (ρ(Tno)²)⁻¹ ≤ 粗 records 的 static scale`，
无子列：recent 阈值与 `lateLambda` 阈值并入 `T₀`。 -/
theorem birthN_of_recent_HNS {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (records : GC.LongTime.Ch11.CutoffRecords_C11S F q)
    (hrcs : GC.LongTime.Ch11.RecentCutoffSupply_C11S records)
    (hanti : AntitoneOn q.neckRadius (Ici 0)) (hδq : Tendsto q.delta atTop (𝓝 0))
    (ind : ℕ → ℕ) (Nf : ℕ → ℝ) {T₀ c σ L R Tn Tno : ℕ → ℝ}
    (hTr : ∀ n, recentThrN_HNS hrcs Nf n ≤ T₀ n)
    (hT₀Λ : ∀ n, lateLambdaThr_P6HA q hδq ≤ T₀ n) (hseed : ∀ n, T₀ n ≤ Tno n)
    (hc : ∀ n, 0 < c n) (hTno : ∀ n, Tno n = c n * Tn n) (hTno0 : ∀ n, 0 ≤ Tno n)
    (h2c : ∀ n, 2 * c n < Tno n) (hroom : ∀ n, Tn n - 1 ^ 2 / 2 ≤ σ n - L n ^ 2 / R n)
    (hRr : ∀ n : ℕ, (n : ℝ) + 1 ≤ R n) (n : ℕ) (i : Fin (F.tower.history (ind n)).eventCount)
    (hi : max (T₀ n) (c n * (σ n - L n / R n)) ≤ (F.tower.history (ind n)).time i.succ)
    (b : ((F.tower.history (ind n)).toHistory.event i).RetainedBoundaryIndex) :
    max ((n : ℝ) + 1) (Nf n) * (q.neckRadius (Tno n) ^ 2)⁻¹ ≤
      ((records (ind n) i).static b).neck.scale := by
  have hN : (0 : ℝ) < (n : ℝ) + 1 := Nat.cast_add_one_pos n
  have hM1 : 1 ≤ max ((n : ℝ) + 1) (Nf n) :=
    le_trans (by linarith [Nat.cast_nonneg (α := ℝ) n]) (le_max_left _ _)
  have hMpos : 0 < max ((n : ℝ) + 1) (Nf n) := lt_of_lt_of_le one_pos hM1
  have hR1 : 1 ≤ R n := by
    have := hRr n
    have h0 : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hTn : Tn n = Tno n / c n := by
    rw [hTno n]; field_simp [(hc n).ne']
  have hlate : Tno n ≤ 2 * (F.tower.history (ind n)).time i.succ := by
    have := late_of_Ldomain_P6SF (hc n) hTn (h2c n) hR1 (hroom n)
      ((le_max_right _ _).trans hi)
    linarith
  set η : ℝ := 1 / (2 * max ((n : ℝ) + 1) (Nf n)) with hηdef
  have hηpos : 0 < η := by positivity
  have hηN : 2 * η ^ 2 * max ((n : ℝ) + 1) (Nf n) ≤ 1 := by
    have heq : 2 * η ^ 2 * max ((n : ℝ) + 1) (Nf n) = 1 / (2 * max ((n : ℝ) + 1) (Nf n)) := by
      rw [hηdef]; field_simp
    rw [heq, div_le_one (by positivity)]
    linarith
  obtain ⟨-, hrec⟩ := Classical.choose_spec (hrcs η (by positivity))
  exact sepRhoPlus'_of_recentSupply_P6SF (records (ind n) i) b hanti
    (lateLambda_of_thr_P6HA q hδq ((hT₀Λ n).trans ((le_max_left _ _).trans hi)))
    hηpos.le hηN (hTno0 n) ((hTr n).trans (hseed n)) hlate
    (fun t ht hm h => hrec t ht (ind n) i hm h)

/-- **(iii) 晚期 scale 下界（`_HNS`，PROVED）**：粗 records 上，`δ → 0` 与 `ρ` antitone ⇒
晚于 `Ts` 的 event 有 `S ≤ static scale`（`S ≥ 1`，与 `c`、`ind` 无关）。 -/
theorem lateScale_of_delta_HNS {P : OrientedThreeStage.{u}} {g : P.Metric}
    {F : GC.Interface.RawSurgery P g} {q : CutoffParameters}
    (records : GC.LongTime.Ch11.CutoffRecords_C11S F q)
    (hanti : AntitoneOn q.neckRadius (Ici 0)) (hδq : Tendsto q.delta atTop (𝓝 0))
    {S : ℝ} (hS1 : 1 ≤ S) :
    ∃ Ts : ℝ, ∀ (m : ℕ) (i : Fin (F.tower.history m).eventCount),
      Ts ≤ (F.tower.history m).time i.succ →
      ∀ b, S ≤ ((records m i).static b).neck.scale := by
  have hrc : 0 < q.recenterConstant := by linarith [q.recenterConstant_ge_four]
  have hSpos : 0 < S := lt_of_lt_of_le one_pos hS1
  have hρ₁ : 0 < q.neckRadius 0 := q.neckRadius_pos 0 le_rfl
  have hpos : (0 : ℝ) < min (1 / (2 * q.recenterConstant)) (1 / (2 * S * q.neckRadius 0)) :=
    lt_min (by positivity) (by positivity)
  obtain ⟨Ts, hTs⟩ := Filter.eventually_atTop.mp (hδq.eventually (ge_mem_nhds hpos))
  refine ⟨Ts, fun m i hi b => ?_⟩
  have hδs := hTs _ hi
  have ht0 : 0 ≤ (F.tower.history m).time i.succ := (F.tower.history m).toHistory.time_nonneg i.succ
  have hdel0 : 0 < q.delta ((F.tower.history m).time i.succ) := q.delta_pos _ ht0
  have hρle : q.neckRadius ((F.tower.history m).time i.succ) ≤ q.neckRadius 0 :=
    hanti (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht0) ht0
  have h1 : q.delta ((F.tower.history m).time i.succ) ≤ 1 / (2 * q.recenterConstant) :=
    hδs.trans (min_le_left _ _)
  have h2 : q.delta ((F.tower.history m).time i.succ) ≤ 1 / (2 * S * q.neckRadius 0) :=
    hδs.trans (min_le_right _ _)
  have hΛδ : q.recenterConstant * q.delta ((F.tower.history m).time i.succ) ≤ 1 / 2 := by
    rw [le_div_iff₀ (by positivity)] at h1
    nlinarith
  have hδρ : q.delta ((F.tower.history m).time i.succ) ^ 2 * q.neckRadius 0 ≤ 1 / (2 * S) := by
    have h3 := (le_div_iff₀ (by positivity)).1 h2
    have h4 : q.delta ((F.tower.history m).time i.succ) * q.neckRadius 0 ≤ 1 / (2 * S) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have h5 : q.delta ((F.tower.history m).time i.succ) ^ 2 ≤
        q.delta ((F.tower.history m).time i.succ) := by
      have := q.delta_lt_one _ ht0
      nlinarith
    exact (mul_le_mul_of_nonneg_right h5 hρ₁.le).trans h4
  have hlt := RetainedCoreHistory.inv_two_mul_sq_lt_static_scale_record_delta_P6M3
    (records m i) (δ₀ := q.delta ((F.tower.history m).time i.succ)) (ρ₁ := q.neckRadius 0)
    (ρ₀ := 1 / (2 * S)) hΛδ le_rfl hρle hδρ b
  have heq : (2 * (1 / (2 * S)) ^ 2)⁻¹ = 2 * S ^ 2 := by
    field_simp
  rw [heq] at hlt
  nlinarith [hS1]


/-- **HNR 新义务的引擎供给（`_HNS`，PROVED 相对 `hrcs`、`hfine`、`hanti`、`hδq` 与 HI 常数）**。
`∃ Θ`（档阈值 / recent 阈值 / `δ₀` 阈值 / lateLambda / 晚期 scale 阈值的 max，与 `ind`、`c`、`Tno` 无关），
对一切 `T₀ ≥ Θ`、`ind`、`c σ L R Tn Tno`（数值前提为 DrvResE 合同的原样推论，见
`drvResE_records_of_engine_contract_HNS`），存在原帧参数列 `p` 与 late records `recKHo`
（阈值 `max T₀ (c (σ − L/R))`），其 K 帧搬运（`recordsKRescale_P6X3`，阈值 `max 1 (T̃₀/c)`，
`qK := p.rescale_P6N`）满足：(i) 档 `ζ / Rn / m₀`、canonical window、late `δ ≤ δ₀ n`；
(ii) `max (n+1) (Nf n) · max (n+1) (ρ̃(Tn)²)⁻¹ ≤ scale`（对 `∀ n`）；(iii) `1 ≤ (a₀/c)·scale`（对 `∀ n`）
与 `ã₀ = a₀/c` 的 HI。 -/
theorem drvResE_records_of_engine_HNS {P : OrientedThreeStage.{u}} {g : P.Metric}
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
    ∃ Θ : ℕ → ℝ, ∀ T₀ : ℕ → ℝ, (∀ n, Θ n ≤ T₀ n) → ∀ (ind : ℕ → ℕ) (c σ L R Tn Tno : ℕ → ℝ)
      (hc : ∀ n, 0 < c n), (∀ n, Tno n = c n * Tn n) → (∀ n, 0 ≤ Tno n) →
      (∀ n, 2 * c n < Tno n) → (∀ n, T₀ n ≤ Tno n) →
      (∀ n, Tn n - 1 ^ 2 / 2 ≤ σ n - L n ^ 2 / R n) → (∀ n : ℕ, (n : ℝ) + 1 ≤ R n) →
      (∀ n, R n ≤ c n * (q.neckRadius (Tno n) ^ 2)⁻¹) →
      ∃ (p : ℕ → CutoffParameters)
        (recKHo : ∀ n (i : Fin (F.tower.history (ind n)).eventCount),
          max (T₀ n) (c n * (σ n - L n / R n)) ≤ (F.tower.history (ind n)).time i.succ →
          GeometricCutoffRecord (F.tower.history (ind n)).toHistory i (p n)),
        (∀ n, (p n).modelAccuracy ≤ ζ n) ∧ (∀ n, Rn n ≤ (p n).modelRadius) ∧
        (∀ n, m₀ n ≤ (p n).modelOrder) ∧
        (∀ n i hi b, ((recKHo n i hi).static b).hasCanonicalWindow) ∧
        (∀ n (i : Fin ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).eventCount),
          max 1 (max (T₀ n) (c n * (σ n - L n / R n)) / c n) ≤
            ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time i.succ →
          (q.rescale_P6N (c n) (hc n)).delta
            (((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time i.succ) ≤ δ₀ n) ∧
        (∀ n (i : Fin ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).eventCount)
          (hi : max 1 (max (T₀ n) (c n * (σ n - L n / R n)) / c n) ≤
            ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time i.succ) b,
          max ((n : ℝ) + 1) (Nf n) * max ((n : ℝ) + 1)
              ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ ≤
            ((((F.tower.history (ind n)).recordsKRescale_P6X3 (hc n) (recKHo n) i hi).static b
              ).neck.scale)) ∧
        (∀ n (i : Fin ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).eventCount)
          (hi : max 1 (max (T₀ n) (c n * (σ n - L n / R n)) / c n) ≤
            ((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).time i.succ) b,
          1 ≤ a₀ / c n *
            ((((F.tower.history (ind n)).recordsKRescale_P6X3 (hc n) (recKHo n) i hi).static b
              ).neck.scale)) ∧
        (∀ n x, InFixedHamiltonIveyRegion
            (((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).initialMetric 0) (a₀ / c n) x ∧
          -3 / (a₀ / c n) ≤ metricScalarAt
            (((F.tower.history (ind n)).rescale_P6N (c n) (hc n)).initialMetric 0) x) := by
  classical
  obtain ⟨Ts, hTs⟩ := lateScale_of_delta_HNS records hanti hδq
    (S := max 1 (1 / a₀)) (le_max_left _ _)
  choose Tf hTf using fun n => hfine (Rn n) (ζ n) (m₀ n) (hζ n)
  have hd : ∀ n, ∃ T : ℝ, ∀ s ≥ T, q.delta s ≤ δ₀ n := fun n =>
    Filter.eventually_atTop.mp (hδq.eventually (ge_mem_nhds (hδ₀ n)))
  choose Td hTd using hd
  refine ⟨fun n => max (Tf n) (max (recentThrN_HNS hrcs Nf n) (max (Td n)
    (max (lateLambdaThr_P6HA q hδq) Ts))), ?_⟩
  intro T₀ hT ind c σ L R Tn Tno hc hTno hTno0 h2c hseed hroom hRr hRρ
  choose p hpD hpacc hpord rec' hcan hsc using fun n => hTf n (ind n)
  have hle1 : ∀ n s, T₀ n ≤ s → Tf n ≤ s := fun n s h =>
    ((le_max_left _ _).trans (hT n)).trans h
  have hle2 : ∀ n s, T₀ n ≤ s → recentThrN_HNS hrcs Nf n ≤ s := fun n s h =>
    (((le_max_left _ _).trans (le_max_right _ _)).trans (hT n)).trans h
  have hle3 : ∀ n s, T₀ n ≤ s → Td n ≤ s := fun n s h =>
    ((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans (hT n)).trans h
  have hle4 : ∀ n s, T₀ n ≤ s → lateLambdaThr_P6HA q hδq ≤ s := fun n s h =>
    (((((le_max_left _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans (hT n)).trans h
  have hle5 : ∀ n s, T₀ n ≤ s → Ts ≤ s := fun n s h =>
    (((((le_max_right _ _).trans (le_max_right _ _)).trans (le_max_right _ _)).trans
      (le_max_right _ _)).trans (hT n)).trans h
  have hrec : ∀ n (i : Fin (F.tower.history (ind n)).eventCount),
      max (T₀ n) (c n * (σ n - L n / R n)) ≤ (F.tower.history (ind n)).time i.succ →
      Tf n ≤ (F.tower.history (ind n)).time i.succ := fun n i hi =>
    hle1 n _ ((le_max_left _ _).trans hi)
  have hTrN : ∀ n, recentThrN_HNS hrcs Nf n ≤ T₀ n := fun n =>
    ((le_max_left _ _).trans (le_max_right _ _)).trans (hT n)
  have hΛN : ∀ n, lateLambdaThr_P6HA q hδq ≤ T₀ n := fun n => hle4 n _ le_rfl
  have hρK : ∀ n, ((q.rescale_P6N (c n) (hc n)).neckRadius (Tn n) ^ 2)⁻¹ =
      c n * (q.neckRadius (Tno n) ^ 2)⁻¹ := by
    intro n
    change ((q.neckRadius (c n * Tn n) / Real.sqrt (c n)) ^ 2)⁻¹ = _
    rw [← hTno n, div_pow, Real.sq_sqrt (hc n).le, inv_div, div_eq_mul_inv]
  have hcoarse : ∀ n (i : Fin (F.tower.history (ind n)).eventCount)
      (hi : max (T₀ n) (c n * (σ n - L n / R n)) ≤ (F.tower.history (ind n)).time i.succ) b,
      max ((n : ℝ) + 1) (Nf n) * (q.neckRadius (Tno n) ^ 2)⁻¹ ≤
        ((rec' n i (hrec n i hi)).static b).neck.scale := by
    intro n i hi b
    rw [hsc n i (hrec n i hi) b]
    exact birthN_of_recent_HNS records hrcs hanti hδq ind Nf hTrN hΛN hseed hc hTno hTno0 h2c
      hroom hRr n i hi b
  refine ⟨p, fun n i hi => rec' n i (hrec n i hi), hpacc, hpD, hpord,
    fun n i hi b => hcan n i (hrec n i hi) b, ?_, ?_, ?_, ?_⟩
  · intro n i hi
    exact (F.tower.history (ind n)).hδF_rescale_P6X3 (hc n) (pF := q)
      (T₀ := max (T₀ n) (c n * (σ n - L n / R n))) (δ := δ₀ n)
      (fun i' hi' => hTd n _ (hle3 n _ ((le_max_left _ _).trans hi'))) i hi
  · intro n i hi b
    have habs : ((n : ℝ) + 1) / c n ≤ (q.neckRadius (Tno n) ^ 2)⁻¹ := by
      rw [div_le_iff₀ (hc n), mul_comm]
      exact (hRr n).trans (hRρ n)
    have key := (F.tower.history (ind n)).hscaleK_rescale_P6X3 (hc n)
      (fun i' hi' => rec' n i' (hrec n i' hi')) (T₀ := max (T₀ n) (c n * (σ n - L n / R n)))
      (A := max ((n : ℝ) + 1) (Nf n)) (B := (n : ℝ) + 1) (Q := (q.neckRadius (Tno n) ^ 2)⁻¹)
      (fun i' hi' b' => by
        rw [max_eq_right habs]
        exact hcoarse n i' hi' b') i hi b
    rw [hρK n]
    exact key
  · intro n i hi b
    refine (F.tower.history (ind n)).hbirthA_rescale_P6X3 (hc n)
      (fun i' hi' => rec' n i' (hrec n i' hi')) (T₀ := max (T₀ n) (c n * (σ n - L n / R n)))
      (a₀ := a₀) (fun i' hi' b' => ?_) i hi b
    have hS := hTs (ind n) i' (hle5 n _ ((le_max_left _ _).trans hi')) b'
    change 1 ≤ a₀ * ((rec' n i' (hrec n i' hi')).static b').neck.scale
    rw [hsc n i' (hrec n i' hi') b']
    have h1 : 1 / a₀ ≤ ((records (ind n) i').static b').neck.scale :=
      (le_max_right _ _).trans hS
    rw [div_le_iff₀ ha₀] at h1
    linarith
  · intro n x
    exact (F.tower.history (ind n)).hHI_rescale_P6X3 (hc n) (fun x' => hHI (ind n) x') x

/-- **`T₀K` 的尾部条件（`_HNS`，PROVED）**：HNR 的 `∀ T, ∀ᶠ n, T₀K n ≤ σ n − T/R n`，
`T₀K n := max 1 (max (T₀ n) (c n (σ n − L n/R n)) / c n)`（主定理的 K 帧阈值），
由合同的 `T₀ k ≤ c k·aSeed k`、`1 ≤ aSeed k`、`hwin`、`L → ∞` 给出。 -/
theorem t0K_tail_HNS {T₀ c σ L R a : ℕ → ℝ} (hc : ∀ n, 0 < c n) (hR : ∀ n, 0 < R n)
    (hT₀a : ∀ n, T₀ n ≤ c n * a n) (h1 : ∀ n, 1 ≤ a n)
    (hwin : ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop, a n ≤ σ n - T / R n)
    (hL : Tendsto L atTop atTop) :
    ∀ T : ℝ, 0 < T → ∀ᶠ n in atTop,
      max 1 (max (T₀ n) (c n * (σ n - L n / R n)) / c n) ≤ σ n - T / R n := by
  intro T hT
  filter_upwards [hwin T hT, hL.eventually_ge_atTop T] with n hn hLn
  have hcn := hc n
  have hRn := hR n
  have h2 : T / R n ≤ L n / R n := div_le_div_of_nonneg_right hLn hRn.le
  refine max_le (by linarith [h1 n]) ?_
  rw [div_le_iff₀ hcn]
  refine max_le ?_ ?_
  · have := mul_le_mul_of_nonneg_left hn hcn.le
    nlinarith [hT₀a n]
  · have := mul_le_mul_of_nonneg_left (show σ n - L n / R n ≤ σ n - T / R n by linarith) hcn.le
    nlinarith

/-- consumer（`_HNS`）：标准元组 `Nf n = n + 1` 时 birth 因子退回原 `n + 1`。 -/
example (n : ℕ) (x : ℝ) :
    max ((n : ℝ) + 1) ((fun m : ℕ => (m : ℝ) + 1) n) * x = ((n : ℝ) + 1) * x := by
  simp only [max_self]

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
