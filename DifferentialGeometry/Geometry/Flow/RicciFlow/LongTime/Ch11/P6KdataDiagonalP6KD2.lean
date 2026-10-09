import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6GapWireKP6WR
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6CwsUniformP6SN

/-!
# K 数据供给端的 diagonal 阈值：P5L late supply ⇒ SEPTN (CWS) diagonal 包（S-CH11-KDIAG G1，后缀 `_P6KD2`）

SEPTN G3 `cws_uniform_of_diagonal_P6SN` / `hnotK_of_diagonal_cws_P6SN` 的 diagonal 序列
`Cb Rn ζ δ₀ : ℕ → ℝ`、`m₀ : ℕ → ℕ`（**只依赖 `(Ctime, n)`，先于任何 K 数据**）要求 K 数据满足
`accuracy ≤ ζ n`、`Rn n ≤ modelRadius`、`m₀ n ≤ modelOrder`、`late delta ≤ δ₀ n`、
`max (Q n) 1 ≤ Cb n·scale`（出生尺度）、`1 ≤ a₀·scale`。现有 K 层 producer
（`exists_lateKdata_of_P5L_antitone_P6M3` / `exists_lateThr_free_P6WR`）只给 `1/(n+1)`、`n+1`、`n+2`
的**固定**档。
本文件把它参数化（**INTEGRATION-ONLY**：证明体 = `exists_lateThr_free_P6WR` 的逐项改参，无新数学）：
* **`exists_lateThr_free_diag_P6KD2`**：P5L 形供给 `hP5L`（对 `D ζ' m` 一致，
  `∀ D ζ' m, ∃ T, ∀ k, …`，history 族 `H`）+ `hδq` + `hρa`（antitone）+ 任意标度目标序列 `S n ≥ 1`、
  任意正序列 `ζ δ₀`、任意 `Rn m₀`
  ⇒ **与 history 子列 `ind` 无关**的阈值 `Tmin`：`T₀ ≥ Tmin` 且任一 `ind`，`K n := H (ind n)` 上有 late
  records，`hcanK`、`accuracy ≤ ζ n`、`Rn n ≤ modelRadius`、`m₀ n ≤ modelOrder`、`S n ≤ scale`、
  `q.delta ≤ δ₀ n`（`T₀` 以后）。`1/(n+1)` 档是特例（见文件末 `example`）。
* **`diagonalPack_of_lateKdata_P6KD2`**（adapter）：`S n := max (max (Q n) 1 / Cb n) a₀⁻¹`（`Cb n ≤ 1`
  ⇒ `S n ≥ 1`）⇒ diagonal 出生尺度 `max (Q n) 1 ≤ Cb n·scale` 与 `1 ≤ a₀·scale`（**∀ n**，不是 eventually；
  `a₀ > 0` 给定）。conjunct 顺序 = `hnotK_of_diagonal_cws_P6SN` 的 K 层 binder
  `hcanK hδF hacc hrad hord hbirth hbirthA`。
* **`hnotK_of_P5L_diagonal_P6KD2`**（consumer）：`c` 取自 `hnotK_of_diagonal_cws_P6SN`；对每个 `Ctime = C`，
  P5L 供给 + `hδq` + antitone + 全 records + 序列 `ind`、`Q` + `hslabK`（`Q n` 为 `Ctime` 的事件导数阈值）
  ⇒ `∃ Tmin, ∀ T₀ ≥ Tmin, ∃ p recordsK`，对任意 `j t yG R`，(SEP′) `hsep`（`η := c`）⇒
  cap-window 迹不存在（`hnotK`）。`a₀`、`hHI` 由 `exists_initialHI_P6WR` 供给。
**显式假设（PROVISIONAL 面）**：`hP5L`（S14 P5L late records 供给）、`hδq`、`hanti`、全 records
`CutoffRecords_C11S`、`hslabK`（`Q` 的事件导数阈值，chain 侧 `eventSlabsDerivative_qcanSup_P6WR`）、
(SEP′) `hsep`（selection 侧）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **K 层 late 数据的 diagonal 参数化，ind 无关阈值（`_P6KD2`）**：见文件头。 -/
theorem exists_lateThr_free_diag_P6KD2 {H : ℕ → RetainedCoreHistory.{u}} {q : CutoffParameters}
    (S Rn ζ δ₀ : ℕ → ℝ) (m₀ : ℕ → ℕ) (hS1 : ∀ n, 1 ≤ S n) (hζ : ∀ n, 0 < ζ n)
    (hδ₀ : ∀ n, 0 < δ₀ n)
    (hP5L : ∀ (D ε : ℝ) (m : ℕ), 0 < ε → ∃ T : ℝ, ∀ k, ∃ p : CutoffParameters,
      p.delta = q.delta ∧ p.neckRadius = q.neckRadius ∧ p.fixed = q.fixed ∧
      p.recenterConstant = q.recenterConstant ∧ D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ε ∧
      m ≤ p.modelOrder ∧ ∃ records : ∀ i : Fin (H k).eventCount, T ≤ (H k).time i.succ →
        GeometricCutoffRecord (H k).toHistory i p,
      ∀ i hi b, GC.LongTime.Ch11.linkedCanonicalWindow_C11E ((records i hi).static b))
    (hδq : Tendsto q.delta atTop (𝓝 0)) (hρa : AntitoneOn q.neckRadius (Ici 0)) :
    ∃ Tmin : ℕ → ℝ, ∀ T₀ : ℕ → ℝ, (∀ n, Tmin n ≤ T₀ n) → ∀ ind : ℕ → ℕ,
      ∃ (p : ℕ → CutoffParameters)
        (recordsK : ∀ n (i : Fin (H (ind n)).eventCount), T₀ n ≤ (H (ind n)).time i.succ →
          GeometricCutoffRecord (H (ind n)).toHistory i (p n)),
        (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) ∧
        (∀ n, (p n).modelAccuracy ≤ ζ n) ∧ (∀ n, Rn n ≤ (p n).modelRadius) ∧
        (∀ n, m₀ n ≤ (p n).modelOrder) ∧
        (∀ (n : ℕ) i hi b, S n ≤ ((recordsK n i hi).static b).neck.scale) ∧
        (∀ n (i : Fin (H (ind n)).eventCount), T₀ n ≤ (H (ind n)).time i.succ →
          q.delta ((H (ind n)).time i.succ) ≤ δ₀ n) := by
  choose T₁ hT₁ using fun n : ℕ => hP5L (Rn n) (ζ n) (m₀ n) (hζ n)
  have hrc : 0 < q.recenterConstant := by linarith [q.recenterConstant_ge_four]
  have h2 : ∀ n : ℕ, ∃ T : ℝ, ∀ s ≥ T,
      q.delta s ≤ min (δ₀ n) (1 / (2 * q.recenterConstant)) := by
    intro n
    have hpos : (0 : ℝ) < min (δ₀ n) (1 / (2 * q.recenterConstant)) :=
      lt_min (hδ₀ n) (by positivity)
    exact Filter.eventually_atTop.mp (hδq.eventually (ge_mem_nhds hpos))
  choose Tδ hTδ using h2
  have hSpos : ∀ n, 0 < S n := fun n => lt_of_lt_of_le one_pos (hS1 n)
  have hρ₁ : 0 < q.neckRadius 0 := q.neckRadius_pos 0 le_rfl
  have h3 : ∀ n : ℕ, ∃ T : ℝ, ∀ s ≥ T, q.delta s ≤ 1 / (2 * S n * q.neckRadius 0) := by
    intro n
    have hpos : (0 : ℝ) < 1 / (2 * S n * q.neckRadius 0) :=
      div_pos one_pos (mul_pos (mul_pos two_pos (hSpos n)) hρ₁)
    exact Filter.eventually_atTop.mp (hδq.eventually (ge_mem_nhds hpos))
  choose Tρ hTρ using h3
  refine ⟨fun n => max (T₁ n) (max (Tδ n) (Tρ n)), fun T₀ hT ind => ?_⟩
  choose p hpδ hpρ hpfix hprc hprad hpacc hpord records hlink using fun n => hT₁ n (ind n)
  have hle1 : ∀ n s, T₀ n ≤ s → T₁ n ≤ s := fun n s h =>
    ((le_max_left _ _).trans (hT n)).trans h
  have hle2 : ∀ n s, T₀ n ≤ s → Tδ n ≤ s := fun n s h =>
    (((le_max_left _ _).trans (le_max_right _ _)).trans (hT n)).trans h
  have hle3 : ∀ n s, T₀ n ≤ s → Tρ n ≤ s := fun n s h =>
    (((le_max_right _ _).trans (le_max_right _ _)).trans (hT n)).trans h
  refine ⟨p, fun n i hi => records n i (hle1 n _ hi),
    fun n i hi b => GC.LongTime.Ch11.linkedCanonicalWindow_hasCanonicalWindow_C11E _
      (hlink n i (hle1 n _ hi) b), hpacc, hprad, hpord, ?_, ?_⟩
  · intro n i hi b
    have hδs := hTδ n _ (hle2 n _ hi)
    have hρs := hTρ n _ (hle3 n _ hi)
    have ht0 : 0 ≤ (H (ind n)).time i.succ := (H (ind n)).toHistory.time_nonneg i.succ
    have hdel1 : q.delta ((H (ind n)).time i.succ) < 1 := q.delta_lt_one _ ht0
    have hdel0 : 0 < q.delta ((H (ind n)).time i.succ) := q.delta_pos _ ht0
    have hρle : q.neckRadius ((H (ind n)).time i.succ) ≤ q.neckRadius 0 :=
      hρa (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht0) ht0
    have hδρ : q.delta ((H (ind n)).time i.succ) ^ 2 * q.neckRadius 0 ≤ 1 / (2 * S n) := by
      have hc := hSpos n
      have h1 : q.delta ((H (ind n)).time i.succ) * q.neckRadius 0 ≤ 1 / (2 * S n) := by
        have h2 := (le_div_iff₀ (by positivity)).1 hρs
        rw [le_div_iff₀ (by positivity)]
        nlinarith
      have h3 : q.delta ((H (ind n)).time i.succ) ^ 2 * q.neckRadius 0 ≤
          q.delta ((H (ind n)).time i.succ) * q.neckRadius 0 := by
        have : q.delta ((H (ind n)).time i.succ) ^ 2 ≤ q.delta ((H (ind n)).time i.succ) := by
          nlinarith
        exact mul_le_mul_of_nonneg_right this hρ₁.le
      exact h3.trans h1
    have hΛδ' : (p n).recenterConstant * q.delta ((H (ind n)).time i.succ) ≤ 1 / 2 := by
      rw [hprc n]
      have h1 : q.delta ((H (ind n)).time i.succ) ≤ 1 / (2 * q.recenterConstant) :=
        hδs.trans (min_le_right _ _)
      rw [le_div_iff₀ (by positivity)] at h1
      nlinarith
    have hlt := RetainedCoreHistory.inv_two_mul_sq_lt_static_scale_record_delta_P6M3
      (records n i (hle1 n _ hi))
      (δ₀ := q.delta ((H (ind n)).time i.succ)) (ρ₁ := q.neckRadius 0)
      (ρ₀ := 1 / (2 * S n)) hΛδ' (by rw [hpδ n]) (by rw [hpρ n]; exact hρle) hδρ b
    have heq : (2 * (1 / (2 * S n)) ^ 2)⁻¹ = 2 * S n ^ 2 := by
      have := (hSpos n).ne'
      field_simp
    rw [heq] at hlt
    change S n ≤ ((records n i (hle1 n _ hi)).static b).neck.scale
    nlinarith [hS1 n]
  · intro n i hi
    exact (hTδ n _ (hle2 n _ hi)).trans (min_le_left _ _)

/-- **adapter：P5L late supply ⇒ SEPTN diagonal 包的 K 层 binder（`_P6KD2`）**。给定 diagonal 序列
`Cb Rn ζ δ₀ m₀`（`0 < Cb n ≤ 1/(n+1)²`、`ζ δ₀ > 0`）、`a₀ > 0`、阈值序列 `Q`：与 `ind` 无关的 `Tmin`，
`T₀ ≥ Tmin` 后任一 `ind` 有 late records 满足 `hcanK hδF hacc hrad hord`（diagonal 档）、
`hbirth : max (Q n) 1 ≤ Cb n·scale`、`hbirthA : 1 ≤ a₀·scale`（∀ n）。 -/
theorem diagonalPack_of_lateKdata_P6KD2 {H : ℕ → RetainedCoreHistory.{u}} {q : CutoffParameters}
    (Cb Rn ζ δ₀ : ℕ → ℝ) (m₀ : ℕ → ℕ) (hCb : ∀ n : ℕ, 0 < Cb n ∧ Cb n ≤ 1 / ((n : ℝ) + 1) ^ 2)
    (hζ : ∀ n, 0 < ζ n) (hδ₀ : ∀ n, 0 < δ₀ n) {a₀ : ℝ} (ha₀ : 0 < a₀) (Q : ℕ → ℝ)
    (hP5L : ∀ (D ε : ℝ) (m : ℕ), 0 < ε → ∃ T : ℝ, ∀ k, ∃ p : CutoffParameters,
      p.delta = q.delta ∧ p.neckRadius = q.neckRadius ∧ p.fixed = q.fixed ∧
      p.recenterConstant = q.recenterConstant ∧ D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ε ∧
      m ≤ p.modelOrder ∧ ∃ records : ∀ i : Fin (H k).eventCount, T ≤ (H k).time i.succ →
        GeometricCutoffRecord (H k).toHistory i p,
      ∀ i hi b, GC.LongTime.Ch11.linkedCanonicalWindow_C11E ((records i hi).static b))
    (hδq : Tendsto q.delta atTop (𝓝 0)) (hρa : AntitoneOn q.neckRadius (Ici 0)) :
    ∃ Tmin : ℕ → ℝ, ∀ T₀ : ℕ → ℝ, (∀ n, Tmin n ≤ T₀ n) → ∀ ind : ℕ → ℕ,
      ∃ (p : ℕ → CutoffParameters)
        (recordsK : ∀ n (i : Fin (H (ind n)).eventCount), T₀ n ≤ (H (ind n)).time i.succ →
          GeometricCutoffRecord (H (ind n)).toHistory i (p n)),
        (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) ∧
        (∀ n (i : Fin (H (ind n)).eventCount), T₀ n ≤ (H (ind n)).time i.succ →
          q.delta ((H (ind n)).time i.succ) ≤ δ₀ n) ∧
        (∀ n, (p n).modelAccuracy ≤ ζ n) ∧ (∀ n, Rn n ≤ (p n).modelRadius) ∧
        (∀ n, m₀ n ≤ (p n).modelOrder) ∧
        (∀ n i hi b, max (Q n) 1 ≤ Cb n * ((recordsK n i hi).static b).neck.scale) ∧
        (∀ n i hi b, 1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) := by
  have hCb1 : ∀ n : ℕ, Cb n ≤ 1 := fun n => by
    refine (hCb n).2.trans ?_
    rw [div_le_one (by positivity)]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hS1 : ∀ n, 1 ≤ max (max (Q n) 1 / Cb n) a₀⁻¹ := fun n => by
    refine le_trans ?_ (le_max_left _ _)
    rw [le_div_iff₀ (hCb n).1]
    linarith [hCb1 n, le_max_right (Q n) 1]
  obtain ⟨Tmin, hT⟩ := exists_lateThr_free_diag_P6KD2 (fun n => max (max (Q n) 1 / Cb n) a₀⁻¹)
    Rn ζ δ₀ m₀ hS1 hζ hδ₀ hP5L hδq hρa
  refine ⟨Tmin, fun T₀ hT₀ ind => ?_⟩
  obtain ⟨p, recordsK, hcan, hacc, hrad, hord, hsc, hδ⟩ := hT T₀ hT₀ ind
  refine ⟨p, recordsK, hcan, hδ, hacc, hrad, hord, fun n i hi b => ?_, fun n i hi b => ?_⟩
  · have h1 : max (Q n) 1 / Cb n ≤ max (max (Q n) 1 / Cb n) a₀⁻¹ := le_max_left _ _
    have h2 := h1.trans (hsc n i hi b)
    rw [div_le_iff₀ (hCb n).1] at h2
    linarith
  · have h1 : a₀⁻¹ ≤ max (max (Q n) 1 / Cb n) a₀⁻¹ := le_max_right _ _
    have h2 := h1.trans (hsc n i hi b)
    calc (1 : ℝ) = a₀ * a₀⁻¹ := (mul_inv_cancel₀ ha₀.ne').symm
      _ ≤ a₀ * ((recordsK n i hi).static b).neck.scale := mul_le_mul_of_nonneg_left h2 ha₀.le

/-- **consumer：P5L supply + (SEP′) ⇒ `hnotK`（`_P6KD2`）**。`c` 与 diagonal 序列取自
`hnotK_of_diagonal_cws_P6SN`；K 层 `hcanK hδF hacc hrad hord hbirth hbirthA` 全由
`diagonalPack_of_lateKdata_P6KD2`（`H := F.tower.history`，`pF := q`）供给，`a₀ hHI` 由
`exists_initialHI_P6WR`。残余显式义务：`hP5L hδq hanti records`、`hslabK`、(SEP′) `hsep`。 -/
theorem hnotK_of_P5L_diagonal_P6KD2 :
    ∃ c : ℝ, 0 < c ∧ ∀ C : ℝ≥0, ∀ {P : OrientedThreeStage.{u}} {g : P.Metric}
      {F : GC.Interface.RawSurgery P g} {q : CutoffParameters},
      AntitoneOn q.neckRadius (Ici 0) →
      GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q → Tendsto q.delta atTop (𝓝 0) →
      GC.LongTime.Ch11.CutoffRecords_C11S F q →
      ∀ (ind : ℕ → ℕ) (Q : ℕ → ℝ),
      (∀ n, (F.tower.history (ind n)).EventSlabsDerivative C (Q n)
        (Fin.last (F.tower.history (ind n)).eventCount)) →
      ∃ Tmin : ℕ → ℝ, ∀ T₀ : ℕ → ℝ, (∀ n, Tmin n ≤ T₀ n) →
      ∃ (p : ℕ → CutoffParameters)
        (recordsK : ∀ n (i : Fin (F.tower.history (ind n)).eventCount),
          T₀ n ≤ (F.tower.history (ind n)).time i.succ →
          GeometricCutoffRecord (F.tower.history (ind n)).toHistory i (p n)),
      ∀ {j : ∀ n, Fin (F.tower.history (ind n)).eventCount} {t : ℕ → ℝ},
      (∀ n, (F.tower.history (ind n)).time (j n).castSucc < t n) →
      (∀ n, t n < (F.tower.history (ind n)).time (j n).succ) →
      ∀ {yG : ∀ n, ((F.tower.history (ind n)).stage (j n).castSucc).Carrier} {R : ℕ → ℝ},
      (∀ n, R n = ((F.tower.history (ind n)).toHistory.event (j n)).incoming.flow.scalar (t n)
        (yG n)) →
      (∀ n (i : Fin (F.tower.history (ind n)).eventCount)
        (hi : T₀ n ≤ (F.tower.history (ind n)).time i.succ)
        (b : ((F.tower.history (ind n)).toHistory.event i).RetainedBoundaryIndex),
        i.succ ≤ (j n).castSucc →
        t n - (F.tower.history (ind n)).time i.succ ≤
          (((recordsK n i hi).static b).neck.scale)⁻¹ →
        R n < c * ((recordsK n i hi).static b).neck.scale) →
      ∀ n, ¬ ∃ (i : Fin (F.tower.history (ind n)).eventCount)
          (hi : T₀ n ≤ (F.tower.history (ind n)).time i.succ)
          (hl : i.succ ≤ (j n).castSucc)
          (A : BackwardPointTrace (F.tower.history (ind n)).toHistory i.succ (j n).castSucc hl
            (yG n))
          (b : ((F.tower.history (ind n)).toHistory.event i).RetainedBoundaryIndex)
          (x : standardCapWindow (p n).modelRadius),
          A.point i.succ le_rfl hl = ((recordsK n i hi).static b).window x ∧
            ‖x.val‖ < ((n : ℝ) + 1) + 1 ∧
            t n - (F.tower.history (ind n)).time i.succ ≤
              (1 - 1 / ((n : ℝ) + 2)) * (((recordsK n i hi).static b).neck.scale)⁻¹ := by
  obtain ⟨c, hc, hall⟩ := hnotK_of_diagonal_cws_P6SN.{u}
  refine ⟨c, hc, fun C {P g F q} hanti hP5L hδq records ind Q hslab => ?_⟩
  obtain ⟨Cb, Rn, ζ, δ₀, m₀, hCb, hζ, hδ, hRn, hm₀, hdiag⟩ := hall C
  obtain ⟨a₀, ha₀, hHI⟩ := exists_initialHI_P6WR F
  obtain ⟨Tmin, hT⟩ := diagonalPack_of_lateKdata_P6KD2 (H := F.tower.history) (q := q) Cb Rn ζ δ₀
    m₀ hCb (fun n => (hζ n).1) (fun n => (hδ n).1) ha₀ Q hP5L hδq hanti
  refine ⟨Tmin, fun T₀ hT₀ => ?_⟩
  obtain ⟨p, recordsK, hcan, hδF, hacc, hrad, hord, hbirth, hbirthA⟩ := hT T₀ hT₀ ind
  refine ⟨p, recordsK, fun {j t} hjt htj {yG R} hRn' hsep => ?_⟩
  exact hdiag (K := fun n => F.tower.history (ind n)) hjt htj (pF := fun _ => q)
    (fun n i => records (ind n) i) (a₀ := a₀) (fun n x => hHI (ind n) x) hcan hδF hacc hrad hord
    hslab hbirth hbirthA hRn' hsep

/-- consumer（`exists_lateThr_free_diag_P6KD2`）：固定档（`Rn n = n+1`、`ζ n = δ₀ n = 1/(n+1)`、
`m₀ n = n+2`）恰是 `exists_lateThr_free_P6WR`（`H := F.tower.history`，`hP5L` 展开）。 -/
example {P : OrientedThreeStage.{u}} {g : P.Metric} {F : GC.Interface.RawSurgery P g}
    {q : CutoffParameters} (S : ℕ → ℝ) (hS1 : ∀ n, 1 ≤ S n)
    (hP5L : GC.LongTime.Ch11.LateLinkedRecordsSupply_C11E F q)
    (hδq : Tendsto q.delta atTop (𝓝 0)) (hρa : AntitoneOn q.neckRadius (Ici 0)) :
    ∃ Tmin : ℕ → ℝ, ∀ T₀ : ℕ → ℝ, (∀ n, Tmin n ≤ T₀ n) → ∀ ind : ℕ → ℕ,
      ∃ (p : ℕ → CutoffParameters)
        (recordsK : ∀ n (i : Fin (F.tower.history (ind n)).eventCount),
          T₀ n ≤ (F.tower.history (ind n)).time i.succ →
          GeometricCutoffRecord (F.tower.history (ind n)).toHistory i (p n)),
        (∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow) ∧
        (∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) ∧
        (∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) ∧
        (∀ n : ℕ, n + 2 ≤ (p n).modelOrder) ∧
        (∀ (n : ℕ) i hi b, S n ≤ ((recordsK n i hi).static b).neck.scale) ∧
        (∀ n (i : Fin (F.tower.history (ind n)).eventCount),
          T₀ n ≤ (F.tower.history (ind n)).time i.succ →
          q.delta ((F.tower.history (ind n)).time i.succ) ≤ 1 / ((n : ℝ) + 1)) :=
  exists_lateThr_free_diag_P6KD2 (H := F.tower.history) S (fun n => (n : ℝ) + 1)
    (fun n => 1 / ((n : ℝ) + 1)) (fun n => 1 / ((n : ℝ) + 1)) (fun n => n + 2) hS1
    (fun n => by positivity) (fun n => by positivity) hP5L hδq hρa

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
