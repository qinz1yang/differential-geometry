import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6SepNeckP6CD
import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6NormalizePrefixP6X3

/-!
# `Tn → ∞` 的来源 + frame-covariant 的 (SEP)/(SEP′) 核（S-CH11-SEPTN G1，后缀 `_P6SN`）

**`Tn → ∞` 来自 selection 的输入，不是输出。** `selection_of_bad_sequence_retained_P6R2` 以 `Tn pT r x` 为
输入、输出 `σ y R L`；`Tn` 的发散在 P6X3 prefix 形里是坏点序列的选取性质 `(k : ℝ) + 1 ≤ Tno k`（
`T = max (k+1) (2 T₀ k)`），在**原尺度** frame（`K = Ho`）里它就是 `hTn`：
* `tendsto_Tn_atTop_P6SN`：`(n : ℝ) + 1 ≤ Tn n` ⇒ `Tendsto Tn atTop atTop`；consumer
  `hdistC_of_native_late_P6SN`：`hdistC_of_native_P6CD` 的 `hTn` 换成 `hlate`；
* **重标度 frame（`c = r²`）里 `Tn = Tno / c`**：`mul_rescaleTime_P6X` 只给 `c k * Tn k = Tno k ≥ k+1`
  （`tendsto_mul_Tn_atTop_P6SN`），而 `2 r² < Tno` 只给 `Tn > 2`——`Tn → ∞` **不可证**（需额外 `r²` 有界
  `tendsto_Tn_atTop_of_scale_le_P6SN`，或 `r² / Tno → 0`）。(SEP) 真正需要的是**原时间** `Tno → ∞`：
  ρ̃ₙ(τ̃) = ρ(c τ̃)/√c 随 `n` 变，`recent_cutoff_smallness` 在 `τ := Tno` 处取。
* 因此给出**不含 `Tn → ∞`** 的 at-Tn 核：`sepWK_of_smallAtTn_P6SN` /
  `sepK_eventually_of_smallAtTn_P6SN`（`ρn : ℕ → ℝ` 逐 `n`；小性 / (DLT) 只在 `n` 充分大时的单个时刻
  `Tn n` 处的半窗 `[Tn n / 2, Tn n]` 上给出）；适配器 `smallAtTn_of_tendsto_P6SN` /
  `deltaAtTn_of_tendsto_P6SN` 由 `Tn → ∞` + 旧 `∀ ε ∃ T` 形产生 at-Tn 形；文末 `example`：
  `sepWK_of_smallness_P6CD`、`sepK_eventually_of_smallness_P6CD` 由新核推出（新核严格更强）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open DifferentialGeometry.Geometry.Curvature
open scoped Manifold NNReal Topology ContDiff ENNReal

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- 自然数下标的实序列 `T n ≥ n + 1` ⇒ `T → ∞`（`Tn → ∞` 的内核）。 -/
theorem tendsto_atTop_of_nat_succ_le_P6SN {T : ℕ → ℝ} (h : ∀ n : ℕ, (n : ℝ) + 1 ≤ T n) :
    Tendsto T atTop atTop :=
  tendsto_atTop_mono h (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)

/-- **`Tn → ∞`（`_P6SN`）**：selection 的输入 `Tn`（P6X3 prefix 的 `(k : ℝ) + 1 ≤ Tno k`，原尺度
frame 里 `Tn = Tno`）发散。 -/
theorem tendsto_Tn_atTop_P6SN {H : ℕ → ObservedHistory.{u}} (Tn : ∀ n, Icc (0 : ℝ) (H n).horizon)
    (hlate : ∀ n : ℕ, (n : ℝ) + 1 ≤ (Tn n : ℝ)) :
    Tendsto (fun n => (Tn n : ℝ)) atTop atTop :=
  tendsto_atTop_of_nat_succ_le_P6SN hlate

/-- 沿子列：`Tn → ∞` 与 `ψ → ∞` ⇒ `Tn ∘ ψ → ∞`。 -/
theorem tendsto_Tn_comp_atTop_P6SN {Tn : ℕ → ℝ} (hTn : Tendsto Tn atTop atTop) {ψ : ℕ → ℕ}
    (hψ : Tendsto ψ atTop atTop) : Tendsto (fun n => Tn (ψ n)) atTop atTop :=
  hTn.comp hψ

/-- **重标度 frame 只得 `c · Tn → ∞`（`_P6SN`）**：prefix 的 `Tn = Tno / r²`（`c = r²`），
`mul_rescaleTime_P6X`：`r² · Tn = Tno ≥ k + 1`。 -/
theorem tendsto_mul_Tn_atTop_P6SN {Ho : ℕ → RetainedCoreHistory.{u}} {r : ℕ → ℝ}
    (hr : ∀ k, 0 < r k) (Tno : ∀ k, Icc (0 : ℝ) (Ho k).toHistory.horizon)
    (hlate : ∀ k : ℕ, (k : ℝ) + 1 ≤ (Tno k : ℝ)) :
    Tendsto (fun k => r k ^ 2 * (((Ho k).rescaleTime_P6X (pow_pos (hr k) 2) (Tno k) :
      Icc (0 : ℝ) ((Ho k).rescale_P6N (r k ^ 2) (pow_pos (hr k) 2)).toHistory.horizon) : ℝ))
      atTop atTop := by
  refine tendsto_atTop_of_nat_succ_le_P6SN fun k => ?_
  rw [(Ho k).mul_rescaleTime_P6X (pow_pos (hr k) 2) (Tno k)]
  exact hlate k

/-- **重标度 frame 的 `Tn → ∞` 需要额外 `r²` 有界（`_P6SN`）**：`c k * Tn k ≥ k + 1` 且 `c k ≤ C` ⇒
`Tn → ∞`。（`r² / Tno → 0` 是充要条件；`2 r² < Tno` 本身只给 `Tn > 2`。） -/
theorem tendsto_Tn_atTop_of_scale_le_P6SN {Tn c : ℕ → ℝ} {C : ℝ} (hc : ∀ k, 0 < c k)
    (hbd : ∀ k, c k ≤ C) (hlate : ∀ k : ℕ, (k : ℝ) + 1 ≤ c k * Tn k) :
    Tendsto Tn atTop atTop := by
  have hC : 0 < C := (hc 0).trans_le (hbd 0)
  have h1 : Tendsto (fun k : ℕ => ((k : ℝ) + 1) / C) atTop atTop :=
    (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop).atTop_div_const hC
  refine tendsto_atTop_mono (fun k => ?_) h1
  rw [div_le_iff₀ hC]
  have hTk : 0 ≤ Tn k := by
    by_contra h
    have := mul_neg_of_pos_of_neg (hc k) (not_le.mp h)
    have : (0 : ℝ) ≤ k := k.cast_nonneg
    linarith [hlate k]
  calc (k : ℝ) + 1 ≤ c k * Tn k := hlate k
    _ ≤ C * Tn k := mul_le_mul_of_nonneg_right (hbd k) hTk
    _ = Tn k * C := mul_comm _ _

/-- **at-Tn 小性 ⇐ `Tn → ∞` + 旧 `∀ ε ∃ T` 形（`_P6SN`）**：`ρn n := ρ (Tn n)`。 -/
theorem smallAtTn_of_tendsto_P6SN {K : ℕ → RetainedCoreHistory.{u}} {T₀ : ℕ → ℝ}
    {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    {Tn : ℕ → ℝ} {ρ : ℝ → ℝ} (hTn : Tendsto Tn atTop atTop)
    (hsmallK : ∀ ε : ℝ, 0 < ε → ∃ T : ℝ, 0 < T ∧ ∀ τ : ℝ, T ≤ τ → ∀ n (i : Fin (K n).eventCount),
      (K n).time i.succ ∈ Icc (τ / 2) τ → ∀ (hi : T₀ n ≤ (K n).time i.succ) h,
        (recordsK n i hi).nominalRadius h ≤ ε * ρ τ) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount),
      (K n).time i.succ ∈ Icc (Tn n / 2) (Tn n) → ∀ (hi : T₀ n ≤ (K n).time i.succ) h,
        (recordsK n i hi).nominalRadius h ≤ ε * ρ (Tn n) := by
  intro ε hε
  obtain ⟨T, -, hT⟩ := hsmallK ε hε
  filter_upwards [hTn.eventually_ge_atTop T] with n hn i hti hi h
  exact hT (Tn n) hn n i hti hi h

/-- **at-Tn (DLT) ⇐ `Tn → ∞` + 旧 `∃ Tδ` 形（`_P6SN`）**。 -/
theorem deltaAtTn_of_tendsto_P6SN {K : ℕ → RetainedCoreHistory.{u}} {p : ℕ → CutoffParameters}
    {Tn : ℕ → ℝ} (hTn : Tendsto Tn atTop atTop)
    (hδK : ∃ Tδ : ℝ, ∀ (n : ℕ) (τ : ℝ), Tδ ≤ τ →
      (p n).recenterConstant * (p n).delta τ ≤ 1 / 2) :
    ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount), (K n).time i.succ ∈ Icc (Tn n / 2) (Tn n) →
      (p n).recenterConstant * (p n).delta ((K n).time i.succ) ≤ 1 / 2 := by
  obtain ⟨Tδ, hδ⟩ := hδK
  filter_upwards [hTn.eventually_ge_atTop (2 * Tδ)] with n hn i hti
  exact hδ n _ (by linarith [hti.1])

/-- **(SEP) 的 at-Tn 核（`_P6SN`）**：`sepWK_of_smallness_P6CD` 去掉 `Tn → ∞`。`ρn : ℕ → ℝ` 逐 `n`
（重标度 frame 里 `ρ̃ₙ(Tn) = ρ(c Tn)/√c`），小性与 (DLT) 只在单个时刻 `Tn n` 的半窗 `[Tn n / 2, Tn n]`
上、对充分大的 `n` 给出。其余与 `sepWK_of_smallness_P6CD` 逐字。 -/
theorem sepWK_of_smallAtTn_P6SN {K : ℕ → RetainedCoreHistory.{u}} {j : ∀ n, Fin (K n).eventCount}
    {T₀ : ℕ → ℝ} {p : ℕ → CutoffParameters}
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n))
    {s t Tn r R ρn : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htT : ∀ n, t n ≤ Tn n)
    (hhalf : ∀ n, Tn n - r n ^ 2 / 2 ≤ s n) (htime : ∀ n, 2 * r n ^ 2 < Tn n)
    (hRpos : ∀ n, 0 < R n) (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop)
    (hsel4 : ∀ n, R n ≤ (ρn n ^ 2)⁻¹)
    (hδ : ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount),
      (K n).time i.succ ∈ Icc (Tn n / 2) (Tn n) →
      (p n).recenterConstant * (p n).delta ((K n).time i.succ) ≤ 1 / 2)
    (hsm : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount),
      (K n).time i.succ ∈ Icc (Tn n / 2) (Tn n) → ∀ (hi : T₀ n ≤ (K n).time i.succ) h,
        (recordsK n i hi).nominalRadius h ≤ ε * ρn n) :
    ∀ T : ℝ, 0 < T → ∀ C : ℝ, 0 ≤ C → ∀ᶠ n in atTop,
      ∀ (i : Fin (K n).eventCount) (_hij : i.val < (j n).val) (hi : T₀ n ≤ (K n).time i.succ) b,
        s n - T / R n < (K n).time i.succ →
        2 * max (3 / (r n / 100) ^ 2) (C * R n) < ((recordsK n i hi).static b).neck.scale := by
  intro T _ C _
  set M : ℝ := max C 1 with hMdef
  have hM1 : 1 ≤ M := le_max_right _ _
  have hM0 : 0 < M := by linarith
  set ε : ℝ := 1 / (4 * M) with hεdef
  have hε : 0 < ε := by positivity
  have h4 : 4 * M * ε = 1 := by
    rw [hεdef]
    field_simp
  have hε1 : ε < 1 := by nlinarith
  filter_upwards [hsm ε hε, hδ, hRr.eventually_ge_atTop (max 30000 (4 * T))] with n hsmn hδn hRrn
  intro i hij hi b hwin
  have hR := hRpos n
  have hx : 30000 ≤ R n * r n ^ 2 := (le_max_left _ _).trans hRrn
  have hx4 : 4 * T ≤ R n * r n ^ 2 := (le_max_right _ _).trans hRrn
  have hr2 : 0 < r n ^ 2 := by
    rcases (sq_nonneg (r n)).lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hx
      linarith
  have hTR : T / R n ≤ r n ^ 2 / 4 := by
    rw [div_le_iff₀ hR]
    nlinarith
  have hle : i.succ ≤ (j n).castSucc := by
    rw [Fin.le_iff_val_le_val]
    simp only [Fin.val_succ, Fin.val_castSucc]
    omega
  have hti_hi : (K n).time i.succ ≤ Tn n :=
    ((K n).time_strictMono.monotone hle).trans ((hjt n).le.trans (htT n))
  have hti_lo : Tn n / 2 ≤ (K n).time i.succ := by
    have h1 := hhalf n
    have h2 := htime n
    have h3 := sq_nonneg (r n)
    linarith
  have hnom := hsmn i ⟨hti_lo, hti_hi⟩ hi ⟨b.1.1⟩
  have hS := static_scale_ge_of_recenter_P6CD (recordsK n i hi) (hδn i ⟨hti_lo, hti_hi⟩) b
  set rn := (recordsK n i hi).nominalRadius ⟨b.1.1⟩
  have hrn : 0 < rn := (recordsK n i hi).nominal_pos _
  set ρ0 := ρn n
  have hερ : 0 < ε * ρ0 := hrn.trans_le hnom
  have hρ : 0 < ρ0 := pos_of_mul_pos_right hερ hε.le
  have hRρ : R n * ρ0 ^ 2 ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right (hsel4 n) (sq_nonneg ρ0)
    rwa [inv_mul_cancel₀ (pow_pos hρ 2).ne'] at h
  have hrn2 : rn ^ 2 ≤ ε ^ 2 * ρ0 ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hrn.le hnom 2
  have h3 : 3 / (r n / 100) ^ 2 ≤ R n := by
    have hpos : 0 < (r n / 100) ^ 2 := by
      have e : (r n / 100) ^ 2 = r n ^ 2 / 10000 := by ring
      rw [e]
      exact div_pos hr2 (by norm_num)
    rw [div_le_iff₀ hpos]
    have e : R n * (r n / 100) ^ 2 = R n * r n ^ 2 / 10000 := by ring
    rw [e]
    linarith
  have hmax : max (3 / (r n / 100) ^ 2) (C * R n) ≤ M * R n :=
    max_le (h3.trans (le_mul_of_one_le_left hR.le hM1))
      (mul_le_mul_of_nonneg_right (le_max_left _ _) hR.le)
  have hkey : 2 * (M * R n) * (2 * rn ^ 2) < 1 := by
    have h4MR : 0 ≤ 4 * M * R n := mul_nonneg (mul_nonneg (by norm_num) hM0.le) hR.le
    calc 2 * (M * R n) * (2 * rn ^ 2) = 4 * M * R n * rn ^ 2 := by ring
      _ ≤ 4 * M * R n * (ε ^ 2 * ρ0 ^ 2) := mul_le_mul_of_nonneg_left hrn2 h4MR
      _ = (4 * M * ε) * ε * (R n * ρ0 ^ 2) := by ring
      _ ≤ (4 * M * ε) * ε * 1 :=
        mul_le_mul_of_nonneg_left hRρ (mul_nonneg (by rw [h4]; norm_num) hε.le)
      _ = ε := by rw [h4]; ring
      _ < 1 := hε1
  have hpos2 : 0 < 2 * rn ^ 2 := mul_pos two_pos (pow_pos hrn 2)
  have hlt : 2 * (M * R n) < (2 * rn ^ 2)⁻¹ := by
    rw [← one_div]
    exact (lt_div_iff₀ hpos2).2 hkey
  calc 2 * max (3 / (r n / 100) ^ 2) (C * R n) ≤ 2 * (M * R n) := by linarith
    _ < (2 * rn ^ 2)⁻¹ := hlt
    _ ≤ ((recordsK n i hi).static b).neck.scale := hS

/-- **(SEP′) eventually 的 at-Tn 核（`_P6SN`）**：`sepK_eventually_of_smallness_P6CD` 去掉 `Tn → ∞`，
只留 `Tn` eventually 有正下界 `τ₀`（原尺度 `Tn ≥ n+1`；重标度 `Tn ≥ 2`）：`hscaleK ⇒ scale ≥ n + 1`，窗口
`t − tᵢ ≤ scale⁻¹ ≤ 1/(n+1) ≤ τ₀/4 ≤ Tn/4` 对充分大 `n`。 -/
theorem sepK_eventually_of_smallAtTn_P6SN {K : ℕ → RetainedCoreHistory.{u}}
    {j : ∀ n, Fin (K n).eventCount} {T₀ Q : ℕ → ℝ} {p : ℕ → CutoffParameters}
    {recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n)}
    {t Tn r R ρn : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htT : ∀ n, t n ≤ Tn n)
    (hhalf : ∀ n, Tn n - r n ^ 2 / 2 ≤ t n) (htime : ∀ n, 2 * r n ^ 2 < Tn n)
    (hRpos : ∀ n, 0 < R n) (hsel4 : ∀ n, R n ≤ (ρn n ^ 2)⁻¹)
    (hTn0 : ∃ τ₀ : ℝ, 0 < τ₀ ∧ ∀ᶠ n in atTop, τ₀ ≤ Tn n)
    (hscaleK : ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) * max ((n : ℝ) + 1) (Q n) ≤
      ((recordsK n i hi).static b).neck.scale)
    (hδ : ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount),
      (K n).time i.succ ∈ Icc (Tn n / 2) (Tn n) →
      (p n).recenterConstant * (p n).delta ((K n).time i.succ) ≤ 1 / 2)
    (hsm : ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount),
      (K n).time i.succ ∈ Icc (Tn n / 2) (Tn n) → ∀ (hi : T₀ n ≤ (K n).time i.succ) h,
        (recordsK n i hi).nominalRadius h ≤ ε * ρn n)
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in atTop, ∀ (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ)
      (b : ((K n).toHistory.event i).RetainedBoundaryIndex),
      i.succ ≤ (j n).castSucc →
      t n - (K n).time i.succ ≤ (((recordsK n i hi).static b).neck.scale)⁻¹ →
      R n < η * ((recordsK n i hi).static b).neck.scale := by
  obtain ⟨τ₀, hτ₀, hτev⟩ := hTn0
  set ε : ℝ := min 1 (η / 4) with hεdef
  have hε : 0 < ε := lt_min one_pos (by positivity)
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hεη : ε ≤ η / 4 := min_le_right _ _
  filter_upwards [hsm ε hε, hδ, hτev, tendsto_natCast_atTop_atTop.eventually_ge_atTop (4 / τ₀)]
    with n hsmn hδn hτn hn4
  intro i hi b hle hwin
  have hR := hRpos n
  set S := ((recordsK n i hi).static b).neck.scale with hSdef
  have hS1 : (n : ℝ) + 1 ≤ S := by
    have h := hscaleK n i hi b
    have hn0 : (0 : ℝ) ≤ n := n.cast_nonneg
    have hm : (n : ℝ) + 1 ≤ max ((n : ℝ) + 1) (Q n) := le_max_left _ _
    nlinarith
  have hSpos : 0 < S := by
    have : (0 : ℝ) ≤ n := n.cast_nonneg
    linarith
  have hSinv : S⁻¹ ≤ τ₀ / 4 := by
    have h1 : S⁻¹ ≤ ((n : ℝ) + 1)⁻¹ := inv_anti₀ (by positivity) hS1
    have h2 : ((n : ℝ) + 1)⁻¹ ≤ τ₀ / 4 := by
      rw [inv_eq_one_div, div_le_div_iff₀ (by positivity) (by norm_num)]
      rw [div_le_iff₀ hτ₀] at hn4
      nlinarith
    exact h1.trans h2
  have hti_hi : (K n).time i.succ ≤ Tn n :=
    ((K n).time_strictMono.monotone hle).trans ((hjt n).le.trans (htT n))
  have hti_lo : Tn n / 2 ≤ (K n).time i.succ := by
    have h1 := hhalf n
    have h2 := htime n
    have h3 := sq_nonneg (r n)
    have h4 := hτn
    linarith
  have hnom := hsmn i ⟨hti_lo, hti_hi⟩ hi ⟨b.1.1⟩
  have hSlow := static_scale_ge_of_recenter_P6CD (recordsK n i hi) (hδn i ⟨hti_lo, hti_hi⟩) b
  set rn := (recordsK n i hi).nominalRadius ⟨b.1.1⟩
  have hrn : 0 < rn := (recordsK n i hi).nominal_pos _
  set ρ0 := ρn n
  have hερ : 0 < ε * ρ0 := hrn.trans_le hnom
  have hρ : 0 < ρ0 := pos_of_mul_pos_right hερ hε.le
  have hRρ : R n * ρ0 ^ 2 ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right (hsel4 n) (sq_nonneg ρ0)
    rwa [inv_mul_cancel₀ (pow_pos hρ 2).ne'] at h
  have hrn2 : rn ^ 2 ≤ ε ^ 2 * ρ0 ^ 2 := by
    rw [← mul_pow]
    exact pow_le_pow_left₀ hrn.le hnom 2
  have hε2 : 2 * ε ^ 2 ≤ η / 2 := by nlinarith
  have hkey : R n * (2 * rn ^ 2) < η := by
    calc R n * (2 * rn ^ 2) ≤ R n * (2 * (ε ^ 2 * ρ0 ^ 2)) := by
          have := mul_le_mul_of_nonneg_left hrn2 (by norm_num : (0 : ℝ) ≤ 2)
          exact mul_le_mul_of_nonneg_left this hR.le
      _ = (2 * ε ^ 2) * (R n * ρ0 ^ 2) := by ring
      _ ≤ (2 * ε ^ 2) * 1 := mul_le_mul_of_nonneg_left hRρ (by positivity)
      _ < η := by linarith
  have hpos2 : 0 < 2 * rn ^ 2 := mul_pos two_pos (pow_pos hrn 2)
  have hlt : R n < η * (2 * rn ^ 2)⁻¹ := by
    rw [← div_eq_mul_inv]
    exact (lt_div_iff₀ hpos2).2 hkey
  exact hlt.trans_le (mul_le_mul_of_nonneg_left hSlow hη.le)

/-- **consumer：`hdistC_of_native_P6CD` 的 `hTn` 换成选取性质 `hlate`（`_P6SN`）**：`Tn n ≥ n + 1`
（P6X3 prefix 的 `(k : ℝ) + 1 ≤ Tno k`，原尺度 frame）⇒ `Tn → ∞`（`tendsto_Tn_atTop_P6SN`）⇒ 条件形
`hdistC` 只剩 native / 识别输入。 -/
theorem hdistC_of_native_late_P6SN {K : ℕ → RetainedCoreHistory.{u}}
    {j : ∀ n, Fin (K n).eventCount} {t : ℕ → ℝ}
    (hjt : ∀ n, (K n).time (j n).castSucc < t n) (htj : ∀ n, t n < (K n).time (j n).succ)
    (σ : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (y : ∀ n, ((K n).toHistory.stageAt (σ
        n)).Carrier)
    (R : ℕ → ℝ) (hσ : ∀ n, (σ n : ℝ) = t n) (hRpos : ∀ n, 0 < R n)
    (d : GC.LongTime.Ch11.Pre841Data_C11K (fun n => (K n).toHistory) σ y R
      hRpos)
    (Tn aSeed : ∀ n, Icc (0 : ℝ) (K n).toHistory.horizon) (haT : ∀ n, aSeed n ≤ Tn n)
    (hsT : ∀ n, σ n ≤ Tn n) (has : ∀ n, aSeed n ≤ σ n)
    (pT : ∀ n, ((K n).toHistory.stageAt (Tn n)).Carrier)
    (seedTrace : ∀ n, BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage (aSeed n))
      ((K n).toHistory.activeStage (Tn n)) ((K n).toHistory.activeStage_mono (haT n)) (pT n))
    (r L : ℕ → ℝ) (hL : Tendsto L atTop atTop)
    (hroom : ∀ n, (Tn n : ℝ) - r n ^ 2 / 2 ≤ σ n - L n ^ 2 / R n)
    (htime : ∀ n, 2 * r n ^ 2 < (Tn n : ℝ))
    (hsmall : ∀ n, GC.LongTime.hasSmallParabolicCurvature (K n).toHistory (Tn n) (pT n) (r n))
    (hclock : ∀ n, (aSeed n : ℝ) = (Tn n : ℝ) - r n ^ 2)
    (hRr : Tendsto (fun n => R n * r n ^ 2) atTop atTop)
    {p : ℕ → CutoffParameters} {T₀ : ℕ → ℝ}
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n))
    (hcanK : ∀ n i hi b, ((recordsK n i hi).static b).hasCanonicalWindow)
    (hacc : ∀ n : ℕ, (p n).modelAccuracy ≤ 1 / ((n : ℝ) + 1))
    (hrad : ∀ n : ℕ, (n : ℝ) + 1 ≤ (p n).modelRadius)
    (hord : ∀ n : ℕ, n + 2 ≤ (p n).modelOrder)
    (hT₀ : ∀ B : ℝ, ∀ᶠ n in atTop, T₀ n ≤ (σ n : ℝ) - B / R n)
    (hlate : ∀ n : ℕ, (n : ℝ) + 1 ≤ (Tn n : ℝ))
    (hsel4 : ∀ n, R n ≤ (d.native.params.neckRadius (Tn n) ^ 2)⁻¹)
    (hδK : ∃ Tδ : ℝ, ∀ (n : ℕ) (τ : ℝ), Tδ ≤ τ →
      (p n).recenterConstant * (p n).delta τ ≤ 1 / 2)
    (hnomId : ∀ n (i : Fin (K n).eventCount) (hi : T₀ n ≤ (K n).time i.succ) h,
      (recordsK n i hi).nominalRadius h = (d.native.records n i).nominalRadius h) :
    ∀ φ : ℕ → ℕ, StrictMono φ → ∀ D T Kc : ℝ, 0 < D → 0 < T → 0 ≤ Kc →
      (∀ᶠ n in map φ atTop, (K n).toHistory.isTracedRegion (σ n) (y n) (2 * D / Real.sqrt (R n))
        (T / R n) (Kc * R n)) → ∀ᶠ n in map φ atTop,
      ∀ x ∈ riemannianBallOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ
          n)) (y n)
          (D / Real.sqrt (R n)),
      ∀ (v : Icc (0 : ℝ) (K n).toHistory.horizon) (hav : aSeed n ≤ v) (hvs : v ≤ σ n),
        (σ n : ℝ) - T / R n ≤ v →
      ∀ tr : BackwardPointTrace (K n).toHistory ((K n).toHistory.activeStage v) ((K
          n).toHistory.activeStage (σ n))
          ((K n).toHistory.activeStage_mono hvs) x,
        riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage v) v)
            ((seedTrace n).point ((K n).toHistory.activeStage v) ((K n).toHistory.activeStage_mono
                hav)
              ((K n).toHistory.activeStage_mono (hvs.trans (hsT n))))
            (tr.point ((K n).toHistory.activeStage v) le_rfl ((K n).toHistory.activeStage_mono
                hvs)) ≤
          riemannianEDistOf ((K n).toHistory.stageMetric ((K n).toHistory.activeStage (σ n)) (σ n))
              ((seedTrace n).point ((K n).toHistory.activeStage (σ n)) ((K
                  n).toHistory.activeStage_mono (has n))
                ((K n).toHistory.activeStage_mono (hsT n))) (y n) +
            ENNReal.ofReal (L n / 4 / Real.sqrt (R n)) := by
  exact hdistC_of_native_P6CD hjt htj σ y R hσ hRpos d Tn aSeed haT hsT has pT seedTrace r L hL
    hroom htime hsmall hclock hRr recordsK hcanK hacc hrad hord hT₀
    (tendsto_Tn_atTop_P6SN Tn hlate) hsel4 hδK hnomId

/-- consumer（旧 ⇐ 新，(SEP)）：`sepWK_of_smallness_P6CD` 由 at-Tn 核推出。 -/
example : type_of% @sepWK_of_smallness_P6CD.{u} := by
  intro K j T₀ p recordsK s t Tn r R ρ hjt htT hhalf htime hRpos hRr hTn hsel4 hδK hsmallK
  exact sepWK_of_smallAtTn_P6SN recordsK hjt htT hhalf htime hRpos hRr hsel4
    (deltaAtTn_of_tendsto_P6SN hTn hδK) (smallAtTn_of_tendsto_P6SN hTn hsmallK)

/-- consumer（旧 ⇐ 新，(SEP′)）：`sepK_eventually_of_smallness_P6CD` 由 at-Tn 核推出（`Tn → ∞` ⇒ eventually
`1 ≤ Tn`）。 -/
example : type_of% @sepK_eventually_of_smallness_P6CD.{u} := by
  intro K j T₀ Q p recordsK t Tn r R ρ hjt htT hhalf htime hRpos hTn hsel4 hscaleK hδK hsmallK η hη
  exact sepK_eventually_of_smallAtTn_P6SN hjt htT hhalf htime hRpos hsel4
    ⟨1, one_pos, hTn.eventually_ge_atTop 1⟩ hscaleK (deltaAtTn_of_tendsto_P6SN hTn hδK)
    (smallAtTn_of_tendsto_P6SN hTn hsmallK) hη

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
