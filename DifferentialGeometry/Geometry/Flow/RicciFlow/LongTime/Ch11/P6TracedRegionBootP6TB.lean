import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# BCD 时间 bootstrap：ODE 比较路线的精确障碍（O-CH11-HTR-BCD G1，后缀 `_P6TB`；**BLOCKED 证据**）

本文件**不**证 `hTR`（BCDBOOT traced-region 合同）。它给出简报 G1 路线
"canonical nbhd 曲率界 + ODE 比较 ⇒ 在 sup 深度 `T*` 处延伸一步" 为什么**单独**推不出 `hTR` 的
精确证据（纯实分析，无新 Prop、无 binder）：
* `odeCeiling_le_P6TB`（PROVED，ODE comparison）：沿一条 trace，若 `R(0) ≤ M₀`、`R > 0` 且
  `∂_s R ≤ C·R²`（深度 `s` 方向，即 canonical nbhd 的 `|∂_t R| ≤ C R²`），则在 `C·M₀·S < 1` 时
  `R(s) ≤ M₀ / (1 − C·M₀·s)`。⇒ ODE 路线从 anchor `M₀` 出发**最多**到深度 `1/(C·M₀)`。
* `odeCeiling_double_P6TB`（PROVED）：步长 `1/(2·C·M₀)` 上 ceiling 恰好翻倍（`≤ 2·M₀`）——即
  BCDBOOT 置顶口径的"ceiling 每段翻倍"；逐段重启时步长几何收缩、总深度 `< 1/(C·M₀)`。
* `odeCeiling_sharp_P6TB`（PROVED，**反例**）：饱和 profile `f(s) = M₀ / (1 − C·M₀·s)` 满足
  `f(0) = M₀`、`f′ = C·f²`（导数界取等号），在每个 `[0, T′]`（`T′ < T* := 1/(C·M₀)`）上有界，
  但在 `[0, T*)` 上**无界**。⇒ 只用导数信息（canonical nbhd 的时间导数估计 + 任意 `T′ < T*` 的
  traced region），**推不出** `T*` 处一致的 window anchor（`depthExtendable_add_of_windowAnchorBound`
  的 `∀ T′ < Tstar` 一致 `M` 前提）。
缺的是**非 ODE** 的输入：极限流 `(−T*, 0]` 上的一致标量界（树内
`exists_uniform_scalar_bound_of_local_flow_limit_on_window`，其非结构输入为极限的 κ `hpar` 与切片
BCBD `happrox`），见 DELIVERIES 块的障碍表。
-/

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry.PDE.RicciFlow.Surgery.Topology

/-- **ODE ceiling（`_P6TB`，PROVED）**：`g > 0`、`g′ ≤ C·g²`、`g(0) ≤ M₀`、`C·M₀·S < 1` ⇒
`[0, S]` 上 `g(s) ≤ M₀ / (1 − C·M₀·s)`。证明：`s ↦ g(s)⁻¹ + C·s` 单调不减。 -/
theorem odeCeiling_le_P6TB {C M₀ S : ℝ} {g g' : ℝ → ℝ} (hC : 0 ≤ C) (hM₀ : 0 < M₀)
    (hS : C * M₀ * S < 1) (hpos : ∀ s ∈ Icc 0 S, 0 < g s)
    (hder : ∀ s ∈ Icc 0 S, HasDerivAt g (g' s) s)
    (hg' : ∀ s ∈ Icc 0 S, g' s ≤ C * g s ^ 2) (h0 : g 0 ≤ M₀) :
    ∀ s ∈ Icc 0 S, g s ≤ M₀ / (1 - C * M₀ * s) := by
  have hD : ∀ s ∈ Icc 0 S, HasDerivAt (fun x => (g x)⁻¹ + C * x)
      (-(g' s) / g s ^ 2 + C * 1) s := fun s hs =>
    ((hder s hs).inv (hpos s hs).ne').add ((hasDerivAt_id s).const_mul C)
  have hmono : MonotoneOn (fun x => (g x)⁻¹ + C * x) (Icc 0 S) := by
    refine monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc 0 S)
      (f' := fun s => -(g' s) / g s ^ 2 + C * 1) ?_ ?_ ?_
    · intro s hs
      exact (hD s hs).continuousAt.continuousWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      exact (hD s (Ioo_subset_Icc_self hs)).hasDerivWithinAt
    · intro s hs
      rw [interior_Icc] at hs
      have hs' := Ioo_subset_Icc_self hs
      have hg := hpos s hs'
      have hb := hg' s hs'
      have hq : g' s / g s ^ 2 ≤ C := by
        rw [div_le_iff₀ (by positivity)]
        exact hb
      have e : -(g' s) / g s ^ 2 = -(g' s / g s ^ 2) := neg_div _ _
      rw [e]
      linarith
  intro s hs
  have h0mem : (0 : ℝ) ∈ Icc 0 S := ⟨le_rfl, hs.1.trans hs.2⟩
  have hm := hmono h0mem hs hs.1
  simp only [mul_zero, add_zero] at hm
  have hg0 := hpos 0 h0mem
  have hgs := hpos s hs
  have hinv0 : M₀⁻¹ ≤ (g 0)⁻¹ := inv_anti₀ hg0 h0
  have hCs : C * M₀ * s ≤ C * M₀ * S := mul_le_mul_of_nonneg_left hs.2 (by positivity)
  have hden : 0 < 1 - C * M₀ * s := by linarith
  have key : (1 - C * M₀ * s) / M₀ ≤ (g s)⁻¹ := by
    have e : (1 - C * M₀ * s) / M₀ = M₀⁻¹ - C * s := by
      field_simp
    rw [e]
    linarith
  have key2 : 1 - C * M₀ * s ≤ (g s)⁻¹ * M₀ := (div_le_iff₀ hM₀).1 key
  rw [le_div_iff₀ hden]
  calc g s * (1 - C * M₀ * s) ≤ g s * ((g s)⁻¹ * M₀) :=
        mul_le_mul_of_nonneg_left key2 hgs.le
    _ = M₀ := by field_simp

/-- **ceiling 翻倍（`_P6TB`，PROVED）**：步长 `S = 1/(2·C·M₀)` 上 `g ≤ 2·M₀`（BCDBOOT 的逐段翻倍）。 -/
theorem odeCeiling_double_P6TB {C M₀ : ℝ} {g g' : ℝ → ℝ} (hC : 0 < C) (hM₀ : 0 < M₀)
    (hpos : ∀ s ∈ Icc 0 (1 / (2 * C * M₀)), 0 < g s)
    (hder : ∀ s ∈ Icc 0 (1 / (2 * C * M₀)), HasDerivAt g (g' s) s)
    (hg' : ∀ s ∈ Icc 0 (1 / (2 * C * M₀)), g' s ≤ C * g s ^ 2) (h0 : g 0 ≤ M₀) :
    ∀ s ∈ Icc 0 (1 / (2 * C * M₀)), g s ≤ 2 * M₀ := by
  have hS : C * M₀ * (1 / (2 * C * M₀)) = 1 / 2 := by
    field_simp
  have hS1 : C * M₀ * (1 / (2 * C * M₀)) < 1 := by
    rw [hS]
    norm_num
  intro s hs
  have hb := odeCeiling_le_P6TB hC.le hM₀ hS1 hpos hder hg' h0 s hs
  have hCs : C * M₀ * s ≤ 1 / 2 := by
    rw [← hS]
    exact mul_le_mul_of_nonneg_left hs.2 (by positivity)
  have hden : 1 / 2 ≤ 1 - C * M₀ * s := by linarith
  have h2 : M₀ / (1 - C * M₀ * s) ≤ M₀ / (1 / 2) :=
    div_le_div_of_nonneg_left hM₀.le (by norm_num) hden
  have e : M₀ / (1 / 2) = 2 * M₀ := by ring
  linarith

/-- **饱和反例（`_P6TB`，PROVED）**：`f(s) = M₀ / (1 − C·M₀·s)` 满足 `f(0) = M₀`、`f′ = C·f²`，在每个
`[0, S]`（`C·M₀·S < 1`）上 `≤ f(S)`，但在 `[0, 1/(C·M₀))` 上无界。 -/
theorem odeCeiling_sharp_P6TB {C M₀ : ℝ} (hC : 0 < C) (hM₀ : 0 < M₀) :
    M₀ / (1 - C * M₀ * 0) = M₀ ∧
    (∀ s : ℝ, C * M₀ * s < 1 → 0 < M₀ / (1 - C * M₀ * s) ∧
      HasDerivAt (fun x => M₀ / (1 - C * M₀ * x)) (C * (M₀ / (1 - C * M₀ * s)) ^ 2) s) ∧
    (∀ S : ℝ, C * M₀ * S < 1 → ∀ s ∈ Icc 0 S,
      M₀ / (1 - C * M₀ * s) ≤ M₀ / (1 - C * M₀ * S)) ∧
    ¬ ∃ M : ℝ, ∀ s ∈ Ico 0 (1 / (C * M₀)), M₀ / (1 - C * M₀ * s) ≤ M := by
  refine ⟨by simp, ?_, ?_, ?_⟩
  · intro s hs
    have hden : 0 < 1 - C * M₀ * s := by linarith
    refine ⟨div_pos hM₀ hden, ?_⟩
    have hd : HasDerivAt (fun x => 1 - C * M₀ * x) (-(C * M₀ * 1)) s :=
      ((hasDerivAt_id s).const_mul (C * M₀)).const_sub 1
    have hq := (hasDerivAt_const s M₀).div hd hden.ne'
    convert hq using 1
    field_simp
    ring
  · intro S hS s hs
    have hCs : C * M₀ * s ≤ C * M₀ * S := mul_le_mul_of_nonneg_left hs.2 (by positivity)
    have hden : 0 < 1 - C * M₀ * S := by linarith
    exact div_le_div_of_nonneg_left hM₀.le hden (by linarith)
  · rintro ⟨M, hM⟩
    set ε : ℝ := M₀ / (2 * (|M| + M₀)) with hε
    have hMa : 0 ≤ |M| := abs_nonneg M
    have hε0 : 0 < ε := by positivity
    have hε1 : ε ≤ 1 / 2 := by
      rw [hε, div_le_iff₀ (by positivity)]
      linarith
    set s : ℝ := (1 - ε) / (C * M₀) with hs
    have hCM : 0 < C * M₀ := mul_pos hC hM₀
    have hsC : C * M₀ * s = 1 - ε := by
      rw [hs]
      field_simp
    have hs0 : 0 ≤ s := by
      rw [hs]
      exact div_nonneg (by linarith) hCM.le
    have hs1 : s < 1 / (C * M₀) := by
      rw [hs]
      exact div_lt_div_of_pos_right (by linarith) hCM
    have hb := hM s ⟨hs0, hs1⟩
    rw [hsC, show 1 - (1 - ε) = ε by ring, hε] at hb
    have e : M₀ / (M₀ / (2 * (|M| + M₀))) = 2 * (|M| + M₀) := by
      field_simp
    rw [e] at hb
    have hMle : M ≤ |M| := le_abs_self M
    linarith

/-- **consumer（`_P6TB`）**：饱和 profile 满足 `odeCeiling_le_P6TB` 的全部前提（导数界取等号），
ceiling 在 `[0, S]` 上被逐点达到——ODE 比较的深度 `1/(C·M₀)` 不能再改进；同时 `[0, 1/(C·M₀))` 上无界。 -/
example {C M₀ S : ℝ} (hC : 0 < C) (hM₀ : 0 < M₀) (hS : C * M₀ * S < 1) :
    (∀ s ∈ Icc 0 S, M₀ / (1 - C * M₀ * s) ≤ M₀ / (1 - C * M₀ * s)) ∧
    ¬ ∃ M : ℝ, ∀ s ∈ Ico 0 (1 / (C * M₀)), M₀ / (1 - C * M₀ * s) ≤ M := by
  obtain ⟨h0, hder, -, hunb⟩ := odeCeiling_sharp_P6TB hC hM₀
  have hlt : ∀ s ∈ Icc 0 S, C * M₀ * s < 1 := fun s hs =>
    lt_of_le_of_lt (mul_le_mul_of_nonneg_left hs.2 (by positivity)) hS
  refine ⟨odeCeiling_le_P6TB hC.le hM₀ hS (fun s hs => (hder s (hlt s hs)).1)
    (fun s hs => (hder s (hlt s hs)).2) (fun s _ => le_rfl) h0.le, hunb⟩

end DifferentialGeometry.PDE.RicciFlow.Surgery.Topology
