import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.Kappa.KappaSeedScaleWideC11Q4b

/-!
# 块半径比有界 ⇒ late doubling（S-CH11-DOUBLE G2，后缀 `_C11ND`）

SMALLVOL5 / KAPPA3 G7 的显式前提（逐字）

  `hnrDoubling : ∃ C T₀ : ℝ, ∀ t, T₀ ≤ t → nr (3 * t / 4) ≤ C * nr t`

在 `nr` 单调不增、处处正的前提下，等价于（只差常数）"几何块边界上的 nr 的相邻比有界"：

  `∃ C k₀, ∀ k ≥ k₀, nr (b ^ k) ≤ C * nr (b ^ (k + 1))`，块长 `b = 3`（astra `3^n`）或 `b = 2`。

**不需要块内常数**：`nr` 单调 ⇒ 块内任一点的值夹在两端值之间；`t ∈ [b^(m+1), b^(m+2))` 时
`3t/4 ≥ b^m`（`b ≥ 4/3`），所以 `nr (3t/4) ≤ nr (b^m) ≤ C² · nr (b^(m+2)) ≤ C² · nr t`。

* `nrDoubling_of_blockRatio_C11ND`：一般块长底 `b ≥ 4/3`；
* `nrDoubling_of_blockRatio_three_C11ND` / `…_two_C11ND`：`b = 3` / `b = 2`；
* `seedScale_of_blockRatio_C11ND`：`seedScale_of_doubling_C11Q4b` 的 `hnrDoubling` 换成块比前提。

块比本身（`nr (3^k) = rad (k+1)`，`rad (k+2) ≥ rad (k+1)/C`）的来源见 `KappaBlockRadiusC11ND`。
-/

set_option autoImplicit false

noncomputable section

open Set Filter

namespace GC.LongTime.Ch11

/-- **块比 ⇒ late doubling（一般底 `b ≥ 4/3`）**。 -/
theorem nrDoubling_of_blockRatio_C11ND {nr : ℝ → ℝ} {b : ℝ} (hb : 4 / 3 ≤ b)
    (hanti : AntitoneOn nr (Ici 0)) (hpos : ∀ t, 0 ≤ t → 0 < nr t)
    (hratio : ∃ C : ℝ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k → nr (b ^ k) ≤ C * nr (b ^ (k + 1))) :
    ∃ C T₀ : ℝ, ∀ t : ℝ, T₀ ≤ t → nr (3 * t / 4) ≤ C * nr t := by
  obtain ⟨C, k₀, hC⟩ := hratio
  have hb1 : 1 < b := by linarith
  have hbpos : 0 < b := by linarith
  have hpow : ∀ k : ℕ, 0 < b ^ k := fun k => pow_pos hbpos k
  have hCpos : 0 < C := by
    have h1 := hC k₀ le_rfl
    have h2 := hpos (b ^ k₀) (hpow k₀).le
    have h3 := hpos (b ^ (k₀ + 1)) (hpow (k₀ + 1)).le
    by_contra hneg
    have hneg' := not_lt.mp hneg
    nlinarith
  refine ⟨C * C, b ^ (k₀ + 1), fun t ht => ?_⟩
  have ht1 : 1 ≤ t := le_trans (one_le_pow₀ hb1.le) ht
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near ht1 hb1
  have hn : k₀ + 1 ≤ n := by
    by_contra hlt
    have hlt' := not_le.mp hlt
    have : b ^ (n + 1) ≤ b ^ (k₀ + 1) := pow_le_pow_right₀ hb1.le (by omega)
    linarith
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  have hm : k₀ ≤ m := by omega
  have e1 := hC m hm
  have e2 := hC (m + 1) (by omega)
  have hbm : b ^ m ≤ 3 * t / 4 := by
    have h1 : b ^ (m + 1) = b * b ^ m := by ring
    have h2 : 4 / 3 * b ^ m ≤ b * b ^ m := mul_le_mul_of_nonneg_right hb (hpow m).le
    linarith
  have hnr1 : nr (3 * t / 4) ≤ nr (b ^ m) :=
    hanti (mem_Ici.mpr (hpow m).le) (mem_Ici.mpr (by linarith [hpow m])) hbm
  have hnr2 : nr t ≥ nr (b ^ (m + 1 + 1)) :=
    hanti (mem_Ici.mpr (by linarith)) (mem_Ici.mpr (hpow _).le) hn2.le
  calc nr (3 * t / 4) ≤ nr (b ^ m) := hnr1
    _ ≤ C * nr (b ^ (m + 1)) := e1
    _ ≤ C * (C * nr (b ^ (m + 1 + 1))) := mul_le_mul_of_nonneg_left e2 hCpos.le
    _ = C * C * nr (b ^ (m + 1 + 1)) := by ring
    _ ≤ C * C * nr t := mul_le_mul_of_nonneg_left hnr2 (mul_nonneg hCpos.le hCpos.le)

/-- **astra 块长 `3^n`** 的形：`nr (3^k) ≤ C · nr (3^(k+1))` ⇒ `hnrDoubling`。 -/
theorem nrDoubling_of_blockRatio_three_C11ND {nr : ℝ → ℝ} (hanti : AntitoneOn nr (Ici 0))
    (hpos : ∀ t, 0 ≤ t → 0 < nr t)
    (hratio : ∃ C : ℝ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      nr ((3 : ℝ) ^ k) ≤ C * nr ((3 : ℝ) ^ (k + 1))) :
    ∃ C T₀ : ℝ, ∀ t : ℝ, T₀ ≤ t → nr (3 * t / 4) ≤ C * nr t :=
  nrDoubling_of_blockRatio_C11ND (b := 3) (by norm_num) hanti hpos hratio

/-- **二进块 `2^k`** 的形：`nr (2^k) ≤ C · nr (2^(k+1))` ⇒ `hnrDoubling`。 -/
theorem nrDoubling_of_blockRatio_two_C11ND {nr : ℝ → ℝ} (hanti : AntitoneOn nr (Ici 0))
    (hpos : ∀ t, 0 ≤ t → 0 < nr t)
    (hratio : ∃ C : ℝ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      nr ((2 : ℝ) ^ k) ≤ C * nr ((2 : ℝ) ^ (k + 1))) :
    ∃ C T₀ : ℝ, ∀ t : ℝ, T₀ ≤ t → nr (3 * t / 4) ≤ C * nr t :=
  nrDoubling_of_blockRatio_C11ND (b := 2) (by norm_num) hanti hpos hratio

/-- **consumer**：`seedScale_of_doubling_C11Q4b` 的 `hnrDoubling` 换成块比前提（块长 `3^k`），
结论原样（P6 种子的 shift 尺度条件 `nr v ≤ r n`）。 -/
theorem seedScale_of_blockRatio_C11ND {nr : ℝ → ℝ} (hanti : AntitoneOn nr (Ici 0))
    (hpos : ∀ t, 0 ≤ t → 0 < nr t)
    (hratio : ∃ C : ℝ, ∃ k₀ : ℕ, ∀ k : ℕ, k₀ ≤ k →
      nr ((3 : ℝ) ^ k) ≤ C * nr ((3 : ℝ) ^ (k + 1)))
    {Tn r : ℕ → ℝ} (hT : ∀ n, 2 * r n ^ 2 < Tn n) (hlate : Tendsto Tn atTop atTop)
    (hrat : Tendsto (fun n => r n / nr (Tn n)) atTop atTop) :
    ∀ᶠ n in atTop, ∀ v : ℝ, Tn n - r n ^ 2 / 2 ≤ v → v ≤ Tn n → nr v ≤ r n :=
  seedScale_of_doubling_C11Q4b hanti hpos
    (nrDoubling_of_blockRatio_three_C11ND hanti hpos hratio) hT hlate hrat

end GC.LongTime.Ch11
