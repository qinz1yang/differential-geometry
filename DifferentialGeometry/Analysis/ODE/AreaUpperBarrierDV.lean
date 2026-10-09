import DifferentialGeometry.Analysis.ODE.AreaUpperBarrier

/-!
# G1（S-A10-DERIV）：`hasLocalSmoothUpperBarrier` 的 assembly 引理

IMS09 给出 smooth majorant `Ā ≥ A`（`Ā t₀ = A t₀`，`Ā' (t₀) = d`），本文件把它装配成
`hasLocalSmoothUpperBarrier A S t₀ b`（`AreaUpperBarrier.lean:13`），并给出
`deriv F t₀ = d` 的转换。全部 `theorem`，没有新 def / structure。
-/

set_option autoImplicit false

open Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

/-- G1 主定理：smooth majorant `F`（在开邻域 `U` 上 `C^∞`，`F t₀ = A t₀`，
在 `U ∩ S` 上 `A ≤ F`，`HasDerivAt F d t₀`，`d < b`）⇒ `hasLocalSmoothUpperBarrier A S t₀ b`。 -/
theorem hasLocalSmoothUpperBarrier_of_smooth_majorant_DV
    {A F : ℝ → ℝ} {S U : Set ℝ} {t₀ d b : ℝ}
    (hU : IsOpen U) (ht₀ : t₀ ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (heq : F t₀ = A t₀) (hle : ∀ s ∈ U ∩ S, A s ≤ F s)
    (hd : HasDerivAt F d t₀) (hdb : d < b) :
    hasLocalSmoothUpperBarrier A S t₀ b :=
  ⟨U, F, hU, ht₀, hF, heq, hle, by rw [hd.deriv]; exact hdb⟩

/-- `ContDiffOn ℝ ∞ F U`（`U` 开）在内点处给出 `HasDerivAt F (deriv F t₀) t₀`。 -/
theorem hasDerivAt_of_contDiffOn_infty_DV
    {F : ℝ → ℝ} {U : Set ℝ} {t₀ : ℝ} (hU : IsOpen U) (ht₀ : t₀ ∈ U)
    (hF : ContDiffOn ℝ ∞ F U) : HasDerivAt F (deriv F t₀) t₀ :=
  ((hF.contDiffAt (hU.mem_nhds ht₀)).differentiableAt (by simp)).hasDerivAt

/-- G1 的 `deriv` 版本：不另给 `d`，直接用 `deriv F t₀ < b`。 -/
theorem hasLocalSmoothUpperBarrier_of_smooth_majorant_deriv_DV
    {A F : ℝ → ℝ} {S U : Set ℝ} {t₀ b : ℝ}
    (hU : IsOpen U) (ht₀ : t₀ ∈ U) (hF : ContDiffOn ℝ ∞ F U)
    (heq : F t₀ = A t₀) (hle : ∀ s ∈ U ∩ S, A s ≤ F s)
    (hdb : deriv F t₀ < b) :
    hasLocalSmoothUpperBarrier A S t₀ b :=
  ⟨U, F, hU, ht₀, hF, heq, hle, hdb⟩

/-- `HasDerivAt F d t₀` 与 `ContDiffOn` 同时给出时，`deriv F t₀ = d`（G1 的转换引理）。 -/
theorem deriv_eq_of_hasDerivAt_DV {F : ℝ → ℝ} {d t₀ : ℝ} (hd : HasDerivAt F d t₀) :
    deriv F t₀ = d := hd.deriv

/-- barrier 对 `b` 单调：`b ≤ b'` 时可放宽。 -/
theorem hasLocalSmoothUpperBarrier_mono_DV {A : ℝ → ℝ} {S : Set ℝ} {t₀ b b' : ℝ}
    (h : hasLocalSmoothUpperBarrier A S t₀ b) (hb : b ≤ b') :
    hasLocalSmoothUpperBarrier A S t₀ b' := by
  obtain ⟨U, F, hU, ht₀, hF, heq, hle, hd⟩ := h
  exact ⟨U, F, hU, ht₀, hF, heq, hle, lt_of_lt_of_le hd hb⟩

/-- Consumer：把逐点的 smooth majorant 数据直接喂给 `not_nonnegative_area_upper_barriers_pi_shift`
（`AreaUpperBarrier.lean`，结论 `False`）。 -/
theorem not_nonnegative_of_smooth_majorants_pi_shift_DV
    (A : ℝ → ℝ) (T c : ℝ) (hT : 0 < T + c)
    (hcontinuous : ContinuousOn A (Ici T))
    (hnonnegative : ∀ t ∈ Ici T, 0 ≤ A t)
    (hmaj : ∀ t ∈ Ici T, ∃ (U : Set ℝ) (F : ℝ → ℝ) (d : ℝ),
      IsOpen U ∧ t ∈ U ∧ ContDiffOn ℝ ∞ F U ∧ F t = A t ∧
        (∀ s ∈ U ∩ Ici T, A s ≤ F s) ∧ HasDerivAt F d t ∧
        d < 3 * A t / (4 * (t + c)) - Real.pi) : False := by
  refine not_nonnegative_area_upper_barriers_pi_shift A T c hT hcontinuous hnonnegative ?_
  intro t ht
  obtain ⟨U, F, d, hU, htU, hF, heq, hle, hd, hdb⟩ := hmaj t ht
  exact hasLocalSmoothUpperBarrier_of_smooth_majorant_DV hU htU hF heq hle hd hdb

end DifferentialGeometry.Analysis
