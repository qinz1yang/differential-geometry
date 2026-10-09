import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Real

set_option autoImplicit false

/-!
# G3 障碍见证：Riccati 饱和解（O-CH11-LOCALDT G3，后缀 `_P6LD`；PROVED 见证，目标 BLOCKED）

`hslabsLoc` 的 ∀ `c` 档要沿 backward trace 在 `(t − v)·R(t) ≤ c` 上一致 `|∂ᵥR| ≤ Ctime·R²`。若只用"已知 Dt
的段 + ODE 比较"（SLTPROD c⋆ 档的做法）去控制 trace 上的 `R(v)`，比较函数就是 Riccati 解
`f(v) = R₀ / (1 − C·R₀·(t − v))`：它**取等号** `|f′| = C·f²`，`f(t) = R₀`，并在 `(t − v)·R₀ = 1/C` 处爆破。
所以 Dt(C) + `R(t) = R₀` 推不出 `(t − v)·R₀ ≥ 1/C` 段上任何 `R(v)` 上界；c⋆ 窗迭代的步长
`c⋆ / (2ᵏ R₀)` 成几何级数，总和 `≤ 2c⋆ / R₀`。这是 G3（∀ `c` 档）BLOCKED 的形式化障碍；修复需要区域无关的
早期 CN / Dt 输入（全局 `EventSlabsDerivative` 型）或 consumer 只用 c⋆ 档。
-/

noncomputable section

open Set Filter
open scoped Topology

namespace GC.LongTime.Ch11

/-- Riccati 饱和解。 -/
def riccatiSat_P6LD (C R₀ t : ℝ) (v : ℝ) : ℝ := R₀ / (1 - C * R₀ * (t - v))

/-- 爆破时刻 `v₀ = t − 1/(C·R₀)`。 -/
def riccatiBlowup_P6LD (C R₀ t : ℝ) : ℝ := t - 1 / (C * R₀)

theorem riccatiSat_at_t_P6LD (C R₀ t : ℝ) : riccatiSat_P6LD C R₀ t t = R₀ := by
  simp [riccatiSat_P6LD]

/-- 分母在 `(v₀, t]` 上为正。 -/
theorem riccatiSat_den_pos_P6LD {C R₀ t v : ℝ} (hC : 0 < C) (hR₀ : 0 < R₀)
    (hv : riccatiBlowup_P6LD C R₀ t < v) : 0 < 1 - C * R₀ * (t - v) := by
  have hCR : 0 < C * R₀ := mul_pos hC hR₀
  unfold riccatiBlowup_P6LD at hv
  have h1 : t - v < 1 / (C * R₀) := by linarith
  have h2 : C * R₀ * (t - v) < C * R₀ * (1 / (C * R₀)) := mul_lt_mul_of_pos_left h1 hCR
  rw [mul_one_div_cancel hCR.ne'] at h2
  linarith

/-- **饱和**：`(v₀, ∞)` 上 `f′ = −C·f²`，即 `|f′| = C·f²`（Dt 界取等号）。 -/
theorem riccatiSat_hasDerivAt_P6LD {C R₀ t v : ℝ} (hC : 0 < C) (hR₀ : 0 < R₀)
    (hv : riccatiBlowup_P6LD C R₀ t < v) :
    HasDerivAt (riccatiSat_P6LD C R₀ t) (-(C * riccatiSat_P6LD C R₀ t v ^ 2)) v := by
  have hden := riccatiSat_den_pos_P6LD hC hR₀ hv
  have hd : HasDerivAt (fun w : ℝ => 1 - C * R₀ * (t - w)) (C * R₀) v := by
    have h := (HasDerivAt.const_mul (C * R₀) (hasDerivAt_id v)).add_const (1 - C * R₀ * t)
    have hfun : (fun w : ℝ => 1 - C * R₀ * (t - w)) =
        (fun w : ℝ => C * R₀ * id w + (1 - C * R₀ * t)) := by
      funext w
      simp only [id]
      ring
    rw [hfun]
    simpa using h
  have hq := (hasDerivAt_const v R₀).div hd hden.ne'
  unfold riccatiSat_P6LD
  convert hq using 1
  field_simp
  ring

theorem riccatiSat_pos_P6LD {C R₀ t v : ℝ} (hC : 0 < C) (hR₀ : 0 < R₀)
    (hv : riccatiBlowup_P6LD C R₀ t < v) : 0 < riccatiSat_P6LD C R₀ t v :=
  div_pos hR₀ (riccatiSat_den_pos_P6LD hC hR₀ hv)

/-- **爆破**：`v ↓ v₀` 时 `f(v) → +∞`；`v₀` 处 `(t − v₀)·R₀ = 1/C`。 -/
theorem riccatiSat_tendsto_atTop_P6LD {C R₀ t : ℝ} (hC : 0 < C) (hR₀ : 0 < R₀) :
    Tendsto (riccatiSat_P6LD C R₀ t) (𝓝[>] riccatiBlowup_P6LD C R₀ t) atTop := by
  have hCR : 0 < C * R₀ := mul_pos hC hR₀
  set d : ℝ → ℝ := fun w => 1 - C * R₀ * (t - w) with hd_def
  have hd0 : d (riccatiBlowup_P6LD C R₀ t) = 0 := by
    simp only [hd_def, riccatiBlowup_P6LD]
    field_simp
    ring
  have hcont : Continuous d := by
    simp only [hd_def]
    fun_prop
  have hlim : Tendsto d (𝓝[>] riccatiBlowup_P6LD C R₀ t) (𝓝[>] 0) := by
    apply tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within
    · have h := hcont.tendsto (riccatiBlowup_P6LD C R₀ t)
      rw [hd0] at h
      exact h.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with w hw
      exact riccatiSat_den_pos_P6LD hC hR₀ hw
  have hinv := (tendsto_inv_nhdsGT_zero).comp hlim
  have hmul := hinv.const_mul_atTop hR₀
  refine hmul.congr ?_
  intro w
  simp [riccatiSat_P6LD, hd_def, div_eq_mul_inv]

/-- **障碍（PROVED 见证）**：对任意 `C, R₀ > 0` 与任意界 `B`，存在 `v` 使 `(t − v)·R₀ < 1/C`、
`f(v) > B`，且 `f` 在 `[v, t]` 上处处满足 `|f′| ≤ C·f²`（取等号）、`f(t) = R₀`。所以"Dt(C) + 端点值"
不能给出 `(t − v)·R₀ → 1/C` 时 `R(v)` 的任何一致上界。 -/
theorem riccati_no_uniform_bound_P6LD {C R₀ : ℝ} (hC : 0 < C) (hR₀ : 0 < R₀) (t B : ℝ) :
    ∃ v : ℝ, v < t ∧ (t - v) * R₀ < 1 / C ∧ B < riccatiSat_P6LD C R₀ t v ∧
      riccatiSat_P6LD C R₀ t t = R₀ ∧
      ∀ w ∈ Icc v t, 0 < riccatiSat_P6LD C R₀ t w ∧
        HasDerivAt (riccatiSat_P6LD C R₀ t) (-(C * riccatiSat_P6LD C R₀ t w ^ 2)) w := by
  have hCR : 0 < C * R₀ := mul_pos hC hR₀
  set v₀ := riccatiBlowup_P6LD C R₀ t with hv₀
  have hv₀t : v₀ < t := by
    simp only [hv₀, riccatiBlowup_P6LD]
    have : 0 < 1 / (C * R₀) := by positivity
    linarith
  have hev := (riccatiSat_tendsto_atTop_P6LD (t := t) hC hR₀).eventually_gt_atTop B
  have hev2 : ∀ᶠ w in 𝓝[>] v₀, w ∈ Ioo v₀ t := Ioo_mem_nhdsGT hv₀t
  obtain ⟨v, hvB, hvI⟩ := (hev.and hev2).exists
  refine ⟨v, hvI.2, ?_, hvB, riccatiSat_at_t_P6LD C R₀ t, ?_⟩
  · have h1 : t - v < 1 / (C * R₀) := by
      have := hvI.1
      simp only [hv₀, riccatiBlowup_P6LD] at this
      linarith
    have h2 : (t - v) * R₀ < 1 / (C * R₀) * R₀ := mul_lt_mul_of_pos_right h1 hR₀
    have h3 : 1 / (C * R₀) * R₀ = 1 / C := by field_simp
    linarith
  · intro w hw
    have hw0 : v₀ < w := hvI.1.trans_le hw.1
    exact ⟨riccatiSat_pos_P6LD hC hR₀ hw0, riccatiSat_hasDerivAt_P6LD hC hR₀ hw0⟩

end GC.LongTime.Ch11
