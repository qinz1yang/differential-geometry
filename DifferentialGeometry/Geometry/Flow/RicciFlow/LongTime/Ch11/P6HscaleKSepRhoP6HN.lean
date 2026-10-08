import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.P6HnotLocalP6HN

/-!
# kernel `hscaleK` 的付款：(SEP-ρ⁺) 过去窗 + 未来 records 自动（O-CH11-HNOT-LOCALDT G3，后缀 `_P6HN`）

kernel 冻结 Prop `NotKKernelNoJ10_P6JB`（P6HrestNoJ10P6JB）对 `T₀` 全称，只要求
`hT₀ : ∀ B, ∀ᶠ n, T₀ n ≤ σ n − B/R n`；`recordsK n` 含 `[T₀ n, ∞)` 的**全部** events——过去窗
`T₀ n ≤ time i⁺ ≤ σ n` 与 `σ n` 之后的未来 events。`hscaleK` 槽对两者都要
`(n+1)·max (n+1) (Q n) ≤ scale`。
* 过去窗：producer 取 `T₀ n := σ n − B_n/R n`（`B_n → ∞` 由 (SEP-ρ⁺) 左支 (W) 的 `∀ B ∀ᶠ n` 对角抽出），
  过去 records 恰是 (W) 窗内 records ⇒ (SEP-ρ⁺) 逐字付。
* 未来 records（`σ < time i⁺`）：**不需要跳比**——`ρ` antitone ⇒ `ρ(tᵢ) ≤ ρ(σ) ≤ ρ(0)`，锐形 birth
  `static_scale_gt_birth_P6HN` + late `δ(tᵢ)⁴·2N·max 1 (N·ρ(0)²) ≤ 1`（`N = n+1`，δ 对角趋 0）即得。
`hscaleK_of_sepRhoPlus_P6HN`（PROVED，单个 history、单个 `N`）：两部分拼成槽形（`Q := max N (ρ(σ)²)⁻¹`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Function
open scoped NNReal Topology

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

universe u

/-- **未来 record 的 (SEP-ρ⁺)（`_P6HN`，PROVED）**：`σ ≤ tᵢ`、`ρ` antitone、late `δ(tᵢ)` 足够小 ⇒
`N·max N (ρ(σ)²)⁻¹ ≤ scale`。 -/
theorem sepRhoPlus_future_P6HN {H : ObservedHistory.{u}} {i : Fin H.eventCount}
    {p : CutoffParameters} (R : GeometricCutoffRecord H i p)
    (b : (H.event i).RetainedBoundaryIndex) (hanti : AntitoneOn p.neckRadius (Ici 0))
    {σ N : ℝ} (hσ0 : 0 ≤ σ) (hσi : σ ≤ H.time i.succ) (hN : 1 ≤ N)
    (hΛδ : p.recenterConstant * p.delta (H.time i.succ) ≤ 1 / 2)
    (hδ : p.delta (H.time i.succ) ^ 4 * (2 * N * max 1 (N * p.neckRadius 0 ^ 2)) ≤ 1) :
    N * max N (p.neckRadius σ ^ 2)⁻¹ ≤ (R.static b).neck.scale := by
  have hS := static_scale_gt_birth_P6HN R b hΛδ
  have ht : 0 ≤ H.time i.succ := hσ0.trans hσi
  have hρi := p.neckRadius_pos _ ht
  have hρσ := p.neckRadius_pos _ hσ0
  have hδpos := p.delta_pos _ ht
  have hiσ : p.neckRadius (H.time i.succ) ≤ p.neckRadius σ :=
    hanti (mem_Ici.mpr hσ0) (mem_Ici.mpr ht) hσi
  have hi0 : p.neckRadius (H.time i.succ) ≤ p.neckRadius 0 :=
    hanti (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht
  set a := p.delta (H.time i.succ) ^ 4 with ha
  set ri := p.neckRadius (H.time i.succ) with hri
  set rσ := p.neckRadius σ with hrσ
  set r0 := p.neckRadius 0 with hr0
  have ha0 : 0 < a := by positivity
  have hX : (2 * (p.delta (H.time i.succ) ^ 2 * ri) ^ 2) = 2 * a * ri ^ 2 := by
    rw [ha]
    ring
  rw [hX] at hS
  have hXpos : 0 < 2 * a * ri ^ 2 := by positivity
  have hm1 : 1 ≤ max 1 (N * r0 ^ 2) := le_max_left _ _
  have hm2 : N * r0 ^ 2 ≤ max 1 (N * r0 ^ 2) := le_max_right _ _
  have hri2 : ri ^ 2 ≤ r0 ^ 2 := pow_le_pow_left₀ hρi.le hi0 2
  have hriσ : ri ^ 2 ≤ rσ ^ 2 := pow_le_pow_left₀ hρi.le hiσ 2
  have hN0 : 0 < N := lt_of_lt_of_le one_pos hN
  have h2aN : 2 * a * N ≤ 1 := by
    have := mul_le_mul_of_nonneg_left hm1 (by positivity : (0 : ℝ) ≤ a * (2 * N))
    nlinarith
  rw [mul_max_of_nonneg _ _ hN0.le]
  refine max_le ?_ ?_
  · have h1 : N * N * (2 * a * ri ^ 2) ≤ 1 := by
      have h3 : N * N * (2 * a * ri ^ 2) ≤ N * N * (2 * a * r0 ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hri2 (by positivity))
          (by positivity)
      have h4 := mul_le_mul_of_nonneg_left hm2 (by positivity : (0 : ℝ) ≤ a * (2 * N))
      nlinarith
    have h5 : N * N ≤ (2 * a * ri ^ 2)⁻¹ := by
      rw [show (2 * a * ri ^ 2)⁻¹ = 1 / (2 * a * ri ^ 2) from (one_div _).symm,
        le_div_iff₀ hXpos]
      linarith
    exact h5.trans hS.le
  · have h1 : N * (rσ ^ 2)⁻¹ * (2 * a * ri ^ 2) ≤ 1 := by
      have hq : ri ^ 2 * (rσ ^ 2)⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_one (by positivity)]
        exact hriσ
      have h6 : N * (rσ ^ 2)⁻¹ * (2 * a * ri ^ 2) = 2 * a * N * (ri ^ 2 * (rσ ^ 2)⁻¹) := by
        ring
      rw [h6]
      calc 2 * a * N * (ri ^ 2 * (rσ ^ 2)⁻¹) ≤ 2 * a * N * 1 :=
            mul_le_mul_of_nonneg_left hq (by positivity)
        _ ≤ 1 := by linarith
    have h5 : N * (rσ ^ 2)⁻¹ ≤ (2 * a * ri ^ 2)⁻¹ := by
      rw [show (2 * a * ri ^ 2)⁻¹ = 1 / (2 * a * ri ^ 2) from (one_div _).symm,
        le_div_iff₀ hXpos]
      linarith
    exact h5.trans hS.le

/-- **kernel `hscaleK` 付款（`_P6HN`，PROVED）**：单个 history，`recordsK` 以 `T₀` 为阈。过去 records
（`time i⁺ ≤ σ`）由 (SEP-ρ⁺) 左支 `hpast` 付；未来 records 由 `sepRhoPlus_future_P6HN` 付。结论 = kernel
`hscaleK` 槽在 `N = n+1`、`Q = max N (ρ(σ)²)⁻¹` 处的形。 -/
theorem hscaleK_of_sepRhoPlus_P6HN {H : RetainedCoreHistory.{u}} {p : CutoffParameters}
    {T₀ σ N : ℝ}
    (records : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ →
      GeometricCutoffRecord H.toHistory i p)
    (hanti : AntitoneOn p.neckRadius (Ici 0)) (hσ0 : 0 ≤ σ) (hN : 1 ≤ N)
    (hpast : ∀ i hi b, H.time i.succ ≤ σ →
      N * max N (p.neckRadius σ ^ 2)⁻¹ ≤ ((records i hi).static b).neck.scale)
    (hΛδ : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ → σ < H.time i.succ →
      p.recenterConstant * p.delta (H.time i.succ) ≤ 1 / 2)
    (hδ : ∀ i : Fin H.eventCount, T₀ ≤ H.time i.succ → σ < H.time i.succ →
      p.delta (H.time i.succ) ^ 4 * (2 * N * max 1 (N * p.neckRadius 0 ^ 2)) ≤ 1) :
    ∀ i hi b, N * max N (max N (p.neckRadius σ ^ 2)⁻¹) ≤ ((records i hi).static b).neck.scale := by
  intro i hi b
  rw [← max_assoc, max_self]
  by_cases hiσ : H.time i.succ ≤ σ
  · exact hpast i hi b hiσ
  · have hlt : σ < H.time i.succ := lt_of_not_ge hiσ
    exact sepRhoPlus_future_P6HN (records i hi) b hanti hσ0 hlt.le hN (hΛδ i hi hlt)
      (hδ i hi hlt)

/-- consumer（`_P6HN`）：`hscaleK_of_sepRhoPlus_P6HN` 的结论逐字喂 kernel `hscaleK` 槽形
（`∀ (n : ℕ) i hi b, (n+1)·max (n+1) (Q n) ≤ scale`，`Q n := max (n+1) (ρ(σ n)²)⁻¹`）。 -/
example {K : ℕ → RetainedCoreHistory.{u}} {p : ℕ → CutoffParameters} {T₀ σ : ℕ → ℝ}
    (recordsK : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ →
      GeometricCutoffRecord (K n).toHistory i (p n))
    (hanti : ∀ n, AntitoneOn (p n).neckRadius (Ici 0)) (hσ0 : ∀ n, 0 ≤ σ n)
    (hpast : ∀ (n : ℕ) i hi b, (K n).time i.succ ≤ σ n →
      ((n : ℝ) + 1) * max ((n : ℝ) + 1) ((p n).neckRadius (σ n) ^ 2)⁻¹ ≤
        ((recordsK n i hi).static b).neck.scale)
    (hΛδ : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ → σ n < (K n).time i.succ →
      (p n).recenterConstant * (p n).delta ((K n).time i.succ) ≤ 1 / 2)
    (hδ : ∀ n (i : Fin (K n).eventCount), T₀ n ≤ (K n).time i.succ → σ n < (K n).time i.succ →
      (p n).delta ((K n).time i.succ) ^ 4 *
        (2 * ((n : ℝ) + 1) * max 1 (((n : ℝ) + 1) * (p n).neckRadius 0 ^ 2)) ≤ 1) :
    ∀ (n : ℕ) i hi b, ((n : ℝ) + 1) *
      max ((n : ℝ) + 1) (max ((n : ℝ) + 1) ((p n).neckRadius (σ n) ^ 2)⁻¹) ≤
        ((recordsK n i hi).static b).neck.scale :=
  fun n => hscaleK_of_sepRhoPlus_P6HN (recordsK n) (hanti n) (hσ0 n)
    (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) (hpast n) (hΛδ n) (hδ n)

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
