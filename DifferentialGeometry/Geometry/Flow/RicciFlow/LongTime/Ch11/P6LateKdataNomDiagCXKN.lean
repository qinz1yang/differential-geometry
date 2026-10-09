import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6KdataDiagonalP6KD2

/-!
# nominal-preserving diagonal late-Kdata 联合 witness（CX-KNOM，后缀 `_CXKN`）

D-7：NOMID `exists_lateKdata_of_P5L_antitone_nominal_P6NI`（固定 `1/(n+1)` 档 + nominal /
reparameterization 合取）与 KDIAG `exists_lateThr_free_diag_P6KD2`（任意 diagonal 档，`Tmin` 与 `ind`
无关，但结论无 nominal 合取）是两个独立 ∃。本文件在**同一 `recordsK`** 上给联合 witness：
* `exists_lateKdata_nominal_diag_CXKN`：`hP5L`（对 `D ε m` 一致、对 `k` 全称，**每个 `k` 的 record 族
  多带 nominal 合取，参考 records `recs k i`**——NOMID 的 binder 形）+ `hδq` + antitone ⇒ 量词序照
  KDIAG（`S Rn ζ δ₀ m₀` 在 `Tmin` 之前，`Tmin` 在 `T₀`、`ind` 之前）的 `Tmin`；`T₀ ≥ Tmin`、任一 `ind`
  ⇒ `p recordsK`：KDIAG 六项 ∧ `(p n).delta = q.delta` ∧
  `(p n).recenterConstant = q.recenterConstant` ∧
  对参考 `recs (ind n) i` 的 nominalRadius / delta / order / neck / static scale / inclusion∘cap 识别。
  证法 = NOMID 的构造上参数化精度档（`choose` 的 `hT₁ n := hP5L (Rn n) (ζ n) (m₀ n)`，nominal 合取与
  `records` 同一个 witness 一起取出），不是两次 ∃。
* `diagonalPack_nom_CXKN`：`diagonalPack_of_lateKdata_P6KD2` 的 nominal 孪生（同一 `recordsK`）。
* `hnotK_of_P5L_diagonal_CXKN`：`hnotK_of_P5L_diagonal_P6KD2` 的孪生；`hP5L` 换成带 nominal 合取的形，
  结论多一个 nominal 合取块（同一 `recordsK`）。
**NOMID 固定档四项**（`accuracy ≤ 1/(n+1)`、`n+1 ≤ modelRadius`、`n+2 ≤ modelOrder`、
`(n+1)·max(n+1)(Q n) ≤ scale`）是 diagonal 档的特例，不另列；见文件末 `example`。
**显式假设（PROVISIONAL 面）**：与 KDIAG 同（`hP5L` 的 nominal 增强、`hδq`、`hanti`、records、
`hslabK`、(SEP′) `hsep`）。nominal 合取在 `hP5L` 里是 binder——供给侧（astra 链）由
`P5LNominalSupplyP6NI` 给固定 `n` 档；是否对一致的 `D ε m` 全称给出见 `example` 与 HANDOVER。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold NNReal Topology ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **联合 witness（`_CXKN`）**：见文件头。 -/
theorem exists_lateKdata_nominal_diag_CXKN {H : ℕ → RetainedCoreHistory.{u}}
    {q : CutoffParameters}
    (recs : ∀ k (i : Fin (H k).eventCount), GeometricCutoffRecord (H k).toHistory i q)
    (S Rn ζ δ₀ : ℕ → ℝ) (m₀ : ℕ → ℕ) (hS1 : ∀ n, 1 ≤ S n) (hζ : ∀ n, 0 < ζ n)
    (hδ₀ : ∀ n, 0 < δ₀ n)
    (hP5L : ∀ (D ε : ℝ) (m : ℕ), 0 < ε → ∃ T : ℝ, ∀ k, ∃ p : CutoffParameters,
      p.delta = q.delta ∧ p.neckRadius = q.neckRadius ∧ p.fixed = q.fixed ∧
      p.recenterConstant = q.recenterConstant ∧ D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ε ∧
      m ≤ p.modelOrder ∧ ∃ records : ∀ i : Fin (H k).eventCount, T ≤ (H k).time i.succ →
        GeometricCutoffRecord (H k).toHistory i p,
      (∀ i hi b, GC.LongTime.Ch11.linkedCanonicalWindow_C11E ((records i hi).static b)) ∧
      ∀ i hi, (records i hi).nominalRadius = (recs k i).nominalRadius ∧
        (records i hi).delta = (recs k i).delta ∧
        (records i hi).order = (recs k i).order ∧
        (∀ α, HEq ((records i hi).neck α) ((recs k i).neck α)) ∧
        (∀ b, ((records i hi).static b).neck.scale = ((recs k i).static b).neck.scale) ∧
        ∀ (b) (z : ThreeBall),
          ((records i hi).static b).inclusion (((records i hi).static b).witness.cap z) =
            ((recs k i).static b).inclusion (((recs k i).static b).witness.cap z))
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
          q.delta ((H (ind n)).time i.succ) ≤ δ₀ n) ∧
        (∀ n, (p n).delta = q.delta) ∧ (∀ n, (p n).recenterConstant = q.recenterConstant) ∧
        (∀ n (i : Fin (H (ind n)).eventCount) (hi : T₀ n ≤ (H (ind n)).time i.succ),
          (recordsK n i hi).nominalRadius = (recs (ind n) i).nominalRadius ∧
          (recordsK n i hi).delta = (recs (ind n) i).delta ∧
          (recordsK n i hi).order = (recs (ind n) i).order ∧
          (∀ α, HEq ((recordsK n i hi).neck α) ((recs (ind n) i).neck α)) ∧
          (∀ b, ((recordsK n i hi).static b).neck.scale =
            ((recs (ind n) i).static b).neck.scale) ∧
          ∀ (b) (z : ThreeBall),
            ((recordsK n i hi).static b).inclusion
                (((recordsK n i hi).static b).witness.cap z) =
              ((recs (ind n) i).static b).inclusion
                (((recs (ind n) i).static b).witness.cap z)) := by
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
      ((hlink n).1 i (hle1 n _ hi) b), hpacc, hprad, hpord, ?_, ?_, hpδ, hprc,
    fun n i hi => (hlink n).2 i (hle1 n _ hi)⟩
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

/-- **adapter（`_CXKN`）**：`diagonalPack_of_lateKdata_P6KD2` 的 nominal 孪生——同一 `recordsK` 上
diagonal 包（`hcanK hδF hacc hrad hord hbirth hbirthA`）∧ `p.delta/recenter` ∧ nominal 识别。 -/
theorem diagonalPack_nom_CXKN {H : ℕ → RetainedCoreHistory.{u}} {q : CutoffParameters}
    (recs : ∀ k (i : Fin (H k).eventCount), GeometricCutoffRecord (H k).toHistory i q)
    (Cb Rn ζ δ₀ : ℕ → ℝ) (m₀ : ℕ → ℕ) (hCb : ∀ n : ℕ, 0 < Cb n ∧ Cb n ≤ 1 / ((n : ℝ) + 1) ^ 2)
    (hζ : ∀ n, 0 < ζ n) (hδ₀ : ∀ n, 0 < δ₀ n) {a₀ : ℝ} (ha₀ : 0 < a₀) (Q : ℕ → ℝ)
    (hP5L : ∀ (D ε : ℝ) (m : ℕ), 0 < ε → ∃ T : ℝ, ∀ k, ∃ p : CutoffParameters,
      p.delta = q.delta ∧ p.neckRadius = q.neckRadius ∧ p.fixed = q.fixed ∧
      p.recenterConstant = q.recenterConstant ∧ D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ε ∧
      m ≤ p.modelOrder ∧ ∃ records : ∀ i : Fin (H k).eventCount, T ≤ (H k).time i.succ →
        GeometricCutoffRecord (H k).toHistory i p,
      (∀ i hi b, GC.LongTime.Ch11.linkedCanonicalWindow_C11E ((records i hi).static b)) ∧
      ∀ i hi, (records i hi).nominalRadius = (recs k i).nominalRadius ∧
        (records i hi).delta = (recs k i).delta ∧
        (records i hi).order = (recs k i).order ∧
        (∀ α, HEq ((records i hi).neck α) ((recs k i).neck α)) ∧
        (∀ b, ((records i hi).static b).neck.scale = ((recs k i).static b).neck.scale) ∧
        ∀ (b) (z : ThreeBall),
          ((records i hi).static b).inclusion (((records i hi).static b).witness.cap z) =
            ((recs k i).static b).inclusion (((recs k i).static b).witness.cap z))
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
        (∀ n i hi b, 1 ≤ a₀ * ((recordsK n i hi).static b).neck.scale) ∧
        (∀ n, (p n).delta = q.delta) ∧ (∀ n, (p n).recenterConstant = q.recenterConstant) ∧
        (∀ n (i : Fin (H (ind n)).eventCount) (hi : T₀ n ≤ (H (ind n)).time i.succ),
          (recordsK n i hi).nominalRadius = (recs (ind n) i).nominalRadius ∧
          (recordsK n i hi).delta = (recs (ind n) i).delta ∧
          (recordsK n i hi).order = (recs (ind n) i).order ∧
          (∀ α, HEq ((recordsK n i hi).neck α) ((recs (ind n) i).neck α)) ∧
          (∀ b, ((recordsK n i hi).static b).neck.scale =
            ((recs (ind n) i).static b).neck.scale) ∧
          ∀ (b) (z : ThreeBall),
            ((recordsK n i hi).static b).inclusion
                (((recordsK n i hi).static b).witness.cap z) =
              ((recs (ind n) i).static b).inclusion
                (((recs (ind n) i).static b).witness.cap z)) := by
  have hCb1 : ∀ n : ℕ, Cb n ≤ 1 := fun n => by
    refine (hCb n).2.trans ?_
    rw [div_le_one (by positivity)]
    nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hS1 : ∀ n, 1 ≤ max (max (Q n) 1 / Cb n) a₀⁻¹ := fun n => by
    refine le_trans ?_ (le_max_left _ _)
    rw [le_div_iff₀ (hCb n).1]
    linarith [hCb1 n, le_max_right (Q n) 1]
  obtain ⟨Tmin, hT⟩ := exists_lateKdata_nominal_diag_CXKN recs
    (fun n => max (max (Q n) 1 / Cb n) a₀⁻¹) Rn ζ δ₀ m₀ hS1 hζ hδ₀ hP5L hδq hρa
  refine ⟨Tmin, fun T₀ hT₀ ind => ?_⟩
  obtain ⟨p, recordsK, hcan, hacc, hrad, hord, hsc, hδ, hpδ, hprc, hnom⟩ := hT T₀ hT₀ ind
  refine ⟨p, recordsK, hcan, hδ, hacc, hrad, hord, fun n i hi b => ?_, fun n i hi b => ?_,
    hpδ, hprc, hnom⟩
  · have h1 : max (Q n) 1 / Cb n ≤ max (max (Q n) 1 / Cb n) a₀⁻¹ := le_max_left _ _
    have h2 := h1.trans (hsc n i hi b)
    rw [div_le_iff₀ (hCb n).1] at h2
    linarith
  · have h1 : a₀⁻¹ ≤ max (max (Q n) 1 / Cb n) a₀⁻¹ := le_max_right _ _
    have h2 := h1.trans (hsc n i hi b)
    calc (1 : ℝ) = a₀ * a₀⁻¹ := (mul_inv_cancel₀ ha₀.ne').symm
      _ ≤ a₀ * ((recordsK n i hi).static b).neck.scale := mul_le_mul_of_nonneg_left h2 ha₀.le

/-- **consumer 孪生（`_CXKN`）**：`hnotK_of_P5L_diagonal_P6KD2` 的 nominal 版。`hP5L` 为带 nominal 合取的
形（参考 records = `records`，即 `CutoffRecords_C11S F q`）；结论在**同一** `p recordsK` 上先给
`p.delta/recenter` 与 nominal 识别（对 `records (ind n) i`），再给 `hnotK` 的 `∀ j …`（逐字同
`_P6KD2`）。J4/J5/J7/J8/J12/J13 取同一 witness。 -/
theorem hnotK_of_P5L_diagonal_CXKN :
    ∃ c : ℝ, 0 < c ∧ ∀ C : ℝ≥0, ∀ {P : OrientedThreeStage.{u}} {g : P.Metric}
      {F : GC.Interface.RawSurgery P g} {q : CutoffParameters},
      AntitoneOn q.neckRadius (Ici 0) →
      Tendsto q.delta atTop (𝓝 0) →
      ∀ (records : GC.LongTime.Ch11.CutoffRecords_C11S F q),
      (∀ (D ε : ℝ) (m : ℕ), 0 < ε → ∃ T : ℝ, ∀ k, ∃ p : CutoffParameters,
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
              ((records k i).static b).inclusion (((records k i).static b).witness.cap z)) →
      ∀ (ind : ℕ → ℕ) (Q : ℕ → ℝ),
      (∀ n, (F.tower.history (ind n)).EventSlabsDerivative C (Q n)
        (Fin.last (F.tower.history (ind n)).eventCount)) →
      ∃ Tmin : ℕ → ℝ, ∀ T₀ : ℕ → ℝ, (∀ n, Tmin n ≤ T₀ n) →
      ∃ (p : ℕ → CutoffParameters)
        (recordsK : ∀ n (i : Fin (F.tower.history (ind n)).eventCount),
          T₀ n ≤ (F.tower.history (ind n)).time i.succ →
          GeometricCutoffRecord (F.tower.history (ind n)).toHistory i (p n)),
      ((∀ n, (p n).delta = q.delta) ∧ (∀ n, (p n).recenterConstant = q.recenterConstant) ∧
        ∀ n (i : Fin (F.tower.history (ind n)).eventCount)
          (hi : T₀ n ≤ (F.tower.history (ind n)).time i.succ),
          (recordsK n i hi).nominalRadius = (records (ind n) i).nominalRadius ∧
          (recordsK n i hi).delta = (records (ind n) i).delta ∧
          (recordsK n i hi).order = (records (ind n) i).order ∧
          (∀ α, HEq ((recordsK n i hi).neck α) ((records (ind n) i).neck α)) ∧
          (∀ b, ((recordsK n i hi).static b).neck.scale =
            ((records (ind n) i).static b).neck.scale) ∧
          ∀ (b) (z : ThreeBall),
            ((recordsK n i hi).static b).inclusion
                (((recordsK n i hi).static b).witness.cap z) =
              ((records (ind n) i).static b).inclusion
                (((records (ind n) i).static b).witness.cap z)) ∧
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
  refine ⟨c, hc, fun C {P g F q} hanti hδq records hP5L ind Q hslab => ?_⟩
  obtain ⟨Cb, Rn, ζ, δ₀, m₀, hCb, hζ, hδ, hRn, hm₀, hdiag⟩ := hall C
  obtain ⟨a₀, ha₀, hHI⟩ := exists_initialHI_P6WR F
  obtain ⟨Tmin, hT⟩ := diagonalPack_nom_CXKN (H := F.tower.history) (q := q) records Cb Rn ζ δ₀
    m₀ hCb (fun n => (hζ n).1) (fun n => (hδ n).1) ha₀ Q hP5L hδq hanti
  refine ⟨Tmin, fun T₀ hT₀ => ?_⟩
  obtain ⟨p, recordsK, hcan, hδF, hacc, hrad, hord, hbirth, hbirthA, hpδ, hprc, hnom⟩ :=
    hT T₀ hT₀ ind
  refine ⟨p, recordsK, ⟨hpδ, hprc, hnom⟩, fun {j t} hjt htj {yG R} hRn' hsep => ?_⟩
  exact hdiag (K := fun n => F.tower.history (ind n)) hjt htj (pF := fun _ => q)
    (fun n i => records (ind n) i) (a₀ := a₀) (fun n x => hHI (ind n) x) hcan hδF hacc hrad hord
    hslab hbirth hbirthA hRn' hsep

/-- consumer（`exists_lateKdata_nominal_diag_CXKN`）：NOMID 固定档（`Rn n = n+1`、
`ζ n = δ₀ n = 1/(n+1)`、`m₀ n = n+2`、`S n := (n+1)·max(n+1)(Q n)`）作为特例——
NOMID 的 accuracy/radius/order/scale 四项 ∧ 联合 nominal 合取（同一 `recordsK`）。 -/
example {H : ℕ → RetainedCoreHistory.{u}} {q : CutoffParameters}
    (recs : ∀ k (i : Fin (H k).eventCount), GeometricCutoffRecord (H k).toHistory i q)
    (Q : ℕ → ℝ)
    (hP5L : ∀ (D ε : ℝ) (m : ℕ), 0 < ε → ∃ T : ℝ, ∀ k, ∃ p : CutoffParameters,
      p.delta = q.delta ∧ p.neckRadius = q.neckRadius ∧ p.fixed = q.fixed ∧
      p.recenterConstant = q.recenterConstant ∧ D ≤ p.modelRadius ∧ p.modelAccuracy ≤ ε ∧
      m ≤ p.modelOrder ∧ ∃ records : ∀ i : Fin (H k).eventCount, T ≤ (H k).time i.succ →
        GeometricCutoffRecord (H k).toHistory i p,
      (∀ i hi b, GC.LongTime.Ch11.linkedCanonicalWindow_C11E ((records i hi).static b)) ∧
      ∀ i hi, (records i hi).nominalRadius = (recs k i).nominalRadius ∧
        (records i hi).delta = (recs k i).delta ∧
        (records i hi).order = (recs k i).order ∧
        (∀ α, HEq ((records i hi).neck α) ((recs k i).neck α)) ∧
        (∀ b, ((records i hi).static b).neck.scale = ((recs k i).static b).neck.scale) ∧
        ∀ (b) (z : ThreeBall),
          ((records i hi).static b).inclusion (((records i hi).static b).witness.cap z) =
            ((recs k i).static b).inclusion (((recs k i).static b).witness.cap z))
    (hδq : Tendsto q.delta atTop (𝓝 0)) (hρa : AntitoneOn q.neckRadius (Ici 0)) :
    ∃ Tmin : ℕ → ℝ, ∀ T₀ : ℕ → ℝ, (∀ n, Tmin n ≤ T₀ n) → ∀ ind : ℕ → ℕ,
      ∃ (p : ℕ → CutoffParameters)
        (recordsK : ∀ n (i : Fin (H (ind n)).eventCount), T₀ n ≤ (H (ind n)).time i.succ →
          GeometricCutoffRecord (H (ind n)).toHistory i (p n)),
        (∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1)) ∧
        (∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius) ∧ (∀ n : ℕ, n + 2 ≤ (p n).modelOrder) ∧
        (∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
          ((recordsK n i hi).static b).neck.scale) ∧
        (∀ n (i : Fin (H (ind n)).eventCount) (hi : T₀ n ≤ (H (ind n)).time i.succ),
          (recordsK n i hi).nominalRadius = (recs (ind n) i).nominalRadius) := by
  obtain ⟨Tmin, hT⟩ := exists_lateKdata_nominal_diag_CXKN recs
    (fun n => ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n)) (fun n => (n : ℝ) + 1)
    (fun n => 1 / ((n : ℝ) + 1)) (fun n => 1 / ((n : ℝ) + 1)) (fun n => n + 2)
    (fun n => by
      have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
      have h2 : (n : ℝ) + 1 ≤ max ((n : ℝ) + 1) (Q n) := le_max_left _ _
      nlinarith)
    (fun n => by positivity) (fun n => by positivity) hP5L hδq hρa
  refine ⟨Tmin, fun T₀ hT₀ ind => ?_⟩
  obtain ⟨p, recordsK, -, hacc, hrad, hord, hsc, -, -, -, hnom⟩ := hT T₀ hT₀ ind
  exact ⟨p, recordsK, hacc, hrad, hord, hsc, fun n i hi => (hnom n i hi).1⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
