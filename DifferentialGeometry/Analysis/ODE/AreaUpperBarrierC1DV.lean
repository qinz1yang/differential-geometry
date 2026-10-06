import DifferentialGeometry.Analysis.ODE.AreaUpperBarrierDV

/-!
# G3-alt（S-A10-DERIV）：HG14 的 C¹ barrier 变体

`AreaUpperBarrier.lean` 的 `not_nonnegative_of_upper_barriers_div_time` 的证明只用到
`B` 在 `t` 处可导（`ContDiffOn ℝ ∞ B U` 仅经 `contDiffAt.differentiableAt` 使用）。这里把
`hasLocalSmoothUpperBarrier` 换成显式 `∃ U B d, … HasDerivAt B d t …`（不引入新 Prop），
得到 `False` 的 C¹ 版本。原文件不改动；光滑版本是本变体的特例（G1 的
`hasLocalSmoothUpperBarrier_of_smooth_majorant_DV` + `hasDerivAt_of_contDiffOn_infty_DV`）。
跨 surgery event 的 `Ā` 只能证到 C¹ 时（S-A14-SURGERY），下游用这个变体。
-/

set_option autoImplicit false
noncomputable section

open Set Filter
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

/-- C¹ 版 `not_nonnegative_of_upper_barriers_div_time`：barrier 只要求 `HasDerivAt B d t`、
`B t = A t`、在 `U ∩ Ici T` 上 `A ≤ B`（`U` 开邻域）、`d < k A t / (t + c) - b`。 -/
theorem not_nonnegative_of_C1_upper_barriers_div_time_DV
    (A : ℝ → ℝ) (T c k b : ℝ) (hT : 0 < T + c) (hk : k ≤ 1) (hb : 0 < b)
    (hc : ContinuousOn A (Ici T)) (hn : ∀ t ∈ Ici T, 0 ≤ A t)
    (hs : ∀ t ∈ Ici T, ∃ (U : Set ℝ) (B : ℝ → ℝ) (d : ℝ),
      IsOpen U ∧ t ∈ U ∧ HasDerivAt B d t ∧ B t = A t ∧
        (∀ s ∈ U ∩ Ici T, A s ≤ B s) ∧ d < k * A t / (t + c) - b) : False := by
  let F : ℝ → ℝ := fun t => A t / (t + c) + b * Real.log (t + c)
  have hpos (t : ℝ) (ht : t ∈ Ici T) : 0 < t + c := by
    have h := ht
    change T ≤ t at h
    linarith
  have hcont : ContinuousOn F (Ici T) := by
    apply (hc.div (continuous_id.add continuous_const).continuousOn
      (fun t ht => (hpos t ht).ne')).add
    apply continuousOn_const.mul
    exact (continuous_id.add continuous_const).continuousOn.log
      (fun t ht => (hpos t ht).ne')
  have hsupport (t : ℝ) (ht : t ∈ Ici T) :
      ∃ φ : ℝ → ℝ, ∃ d : ℝ, φ t = F t ∧ F ≤ᶠ[𝓝[>] t] φ ∧
        HasDerivAt φ d t ∧ d ≤ 0 := by
    obtain ⟨U, B, dB, hU, htU, hdB, heq, hupper, hder⟩ := hs t ht
    have hdtime : HasDerivAt (fun z : ℝ => z + c) 1 t :=
      (hasDerivAt_id t).add_const c
    have hdlog : HasDerivAt (fun z : ℝ => Real.log (z + c)) (1 / (t + c)) t := by
      simpa only [mul_one, one_div, Function.comp_def] using
        (Real.hasDerivAt_log (hpos t ht).ne').comp t hdtime
    let d := (dB * (t + c) - B t) / (t + c) ^ 2 + b * (1 / (t + c))
    refine ⟨fun z => B z / (z + c) + b * Real.log (z + c), d, by simp [F, heq], ?_, ?_, ?_⟩
    · filter_upwards [show U ∈ 𝓝[>] t from nhdsWithin_le_nhds (hU.mem_nhds htU),
        self_mem_nhdsWithin] with z hzU htz
      have hzT : z ∈ Ici T := (show T ≤ t from ht).trans (show t < z from htz).le
      change A z / (z + c) + b * Real.log (z + c) ≤ B z / (z + c) + b * Real.log (z + c)
      exact add_le_add (div_le_div_of_nonneg_right
        (hupper z ⟨hzU, hzT⟩) (hpos z hzT).le) le_rfl
    · convert (hdB.div hdtime (hpos t ht).ne').add (hdlog.const_mul b) using 1
      all_goals first | rfl | simp [d]
    · have hder' : dB * (t + c) < k * A t - b * (t + c) := by
        have h := (lt_div_iff₀ (hpos t ht)).mp (show dB + b < k * A t / (t + c) by linarith)
        nlinarith
      have hcoeff := mul_le_mul_of_nonneg_right hk (hn t ht)
      have hnum : dB * (t + c) - A t + b * (t + c) ≤ 0 := by
        nlinarith
      have hd : d = (dB * (t + c) - A t + b * (t + c)) / (t + c) ^ 2 := by
        dsimp [d]
        rw [heq]
        field_simp
      rw [hd]
      exact div_nonpos_of_nonpos_of_nonneg hnum (sq_nonneg _)
  have hbound (t : ℝ) (ht : T ≤ t) : F t ≤ F T := by
    have hanti := DifferentialGeometry.antitoneOn_of_deriv_upper_support_nonpos
      (hcont.mono (show Icc T t ⊆ Ici T from fun _ hx => hx.1))
      (fun z hz => hsupport z hz.1)
    exact hanti ⟨le_rfl, ht⟩ ⟨ht, le_rfl⟩ ht
  let q := (F T + 1) / b
  let t := Real.exp q + T + |T + c| + 1
  have ht : T ≤ t := by dsimp [t]; linarith [Real.exp_pos q, abs_nonneg (T + c)]
  have hsize : Real.exp q ≤ t + c := by dsimp [t]; linarith [neg_le_abs (T + c)]
  have hlog : q ≤ Real.log (t + c) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos q) hsize
  have hlog' := mul_le_mul_of_nonneg_left hlog hb.le
  have hq : b * q = F T + 1 := by dsimp [q]; field_simp
  rw [hq] at hlog'
  have hnonneg : 0 ≤ A t / (t + c) := div_nonneg (hn t ht) (hpos t ht).le
  have hlast := hbound t ht
  dsimp only [F] at hlast hlog'
  linarith

/-- C¹ 版 `not_nonnegative_area_upper_barriers_shift`：barrier 上界
`3 A t / (4 (t + c)) - 2π + D`。 -/
theorem not_nonnegative_of_C1_majorants_shift_DV
    (A : ℝ → ℝ) (T c D : ℝ) (hT : 0 < T + c)
    (_hD : 0 < D) (hDpi : D < 2 * Real.pi)
    (hcontinuous : ContinuousOn A (Ici T))
    (hnonnegative : ∀ t ∈ Ici T, 0 ≤ A t)
    (hmaj : ∀ t ∈ Ici T, ∃ (U : Set ℝ) (B : ℝ → ℝ) (d : ℝ),
      IsOpen U ∧ t ∈ U ∧ HasDerivAt B d t ∧ B t = A t ∧
        (∀ s ∈ U ∩ Ici T, A s ≤ B s) ∧
        d < 3 * A t / (4 * (t + c)) - 2 * Real.pi + D) : False := by
  apply not_nonnegative_of_C1_upper_barriers_div_time_DV A T c (3 / 4) (2 * Real.pi - D)
    hT (by norm_num) (by linarith) hcontinuous hnonnegative
  intro t ht
  obtain ⟨U, B, d, hU, htU, hB, heq, hle, hd⟩ := hmaj t ht
  refine ⟨U, B, d, hU, htU, hB, heq, hle, ?_⟩
  convert hd using 1
  rw [div_mul_eq_div_div]
  ring

/-- C¹ 版 `not_nonnegative_area_upper_barriers_pi_shift`（lead 点名的 G3-alt 形状）：
对每个 `t ∈ Ici T` 给 `∃ U B d`，`HasDerivAt B d t`、`B t = A t`、`U ∩ Ici T` 上 `A ≤ B`、
`d < 3 A t / (4 (t + c)) - π` ⇒ `False`。 -/
theorem not_nonnegative_of_C1_majorants_pi_shift_DV
    (A : ℝ → ℝ) (T c : ℝ) (hT : 0 < T + c)
    (hcontinuous : ContinuousOn A (Ici T))
    (hnonnegative : ∀ t ∈ Ici T, 0 ≤ A t)
    (hmaj : ∀ t ∈ Ici T, ∃ (U : Set ℝ) (B : ℝ → ℝ) (d : ℝ),
      IsOpen U ∧ t ∈ U ∧ HasDerivAt B d t ∧ B t = A t ∧
        (∀ s ∈ U ∩ Ici T, A s ≤ B s) ∧
        d < 3 * A t / (4 * (t + c)) - Real.pi) : False := by
  apply not_nonnegative_of_C1_majorants_shift_DV A T c Real.pi hT
    Real.pi_pos (by linarith [Real.pi_pos]) hcontinuous hnonnegative
  intro t ht
  obtain ⟨U, B, d, hU, htU, hB, heq, hle, hd⟩ := hmaj t ht
  refine ⟨U, B, d, hU, htU, hB, heq, hle, ?_⟩
  linarith

/-- `DifferentiableOn ℝ B U` 形式（lead 的另一个备选形状）：`deriv B t < …`，
`B` 在开集 `U` 上可微。 -/
theorem not_nonnegative_of_C1_majorants_pi_shift_of_differentiableOn_DV
    (A : ℝ → ℝ) (T c : ℝ) (hT : 0 < T + c)
    (hcontinuous : ContinuousOn A (Ici T))
    (hnonnegative : ∀ t ∈ Ici T, 0 ≤ A t)
    (hmaj : ∀ t ∈ Ici T, ∃ (U : Set ℝ) (B : ℝ → ℝ),
      IsOpen U ∧ t ∈ U ∧ DifferentiableOn ℝ B U ∧ B t = A t ∧
        (∀ s ∈ U ∩ Ici T, A s ≤ B s) ∧
        deriv B t < 3 * A t / (4 * (t + c)) - Real.pi) : False := by
  apply not_nonnegative_of_C1_majorants_pi_shift_DV A T c hT hcontinuous hnonnegative
  intro t ht
  obtain ⟨U, B, hU, htU, hB, heq, hle, hd⟩ := hmaj t ht
  exact ⟨U, B, deriv B t, hU, htU, ((hB t htU).differentiableAt (hU.mem_nhds htU)).hasDerivAt,
    heq, hle, hd⟩

/-- Consumer（向后兼容）：光滑 barrier 版 `not_nonnegative_area_upper_barriers_pi_shift`
的假设（`hasLocalSmoothUpperBarrier`）经 G1 的 `hasDerivAt_of_contDiffOn_infty_DV`
喂给 C¹ 变体，恢复原结论。 -/
theorem not_nonnegative_area_upper_barriers_pi_shift_via_C1_DV
    (A : ℝ → ℝ) (T c : ℝ) (hT : 0 < T + c)
    (hcontinuous : ContinuousOn A (Ici T))
    (hnonnegative : ∀ t ∈ Ici T, 0 ≤ A t)
    (hbarrier : ∀ t ∈ Ici T,
      hasLocalSmoothUpperBarrier A (Ici T) t
        (3 * A t / (4 * (t + c)) - Real.pi)) : False := by
  apply not_nonnegative_of_C1_majorants_pi_shift_DV A T c hT hcontinuous hnonnegative
  intro t ht
  obtain ⟨U, F, hU, htU, hF, heq, hle, hd⟩ := hbarrier t ht
  exact ⟨U, F, deriv F t, hU, htU, hasDerivAt_of_contDiffOn_infty_DV hU htU hF, heq, hle, hd⟩

end DifferentialGeometry.Analysis
