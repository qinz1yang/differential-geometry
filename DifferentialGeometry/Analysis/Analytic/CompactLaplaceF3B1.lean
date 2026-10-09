import Mathlib.Analysis.Normed.Algebra.Exponential
import Mathlib.Analysis.Analytic.Linear
import Mathlib.Analysis.Analytic.Composition
import Mathlib.Analysis.InnerProductSpace.Continuous
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.ContinuousMap.Bounded.Normed

/-!
# F3-b (b1) 之一：紧支撑函数的 Laplace 变换是整函数（S-MY-F3B1 G1，后缀 `_F3B1`）

`g : E → F` 连续紧支撑 ⇒ `a ↦ ∫ y, exp ⟪a, y⟫ • g y ∂μ` 在 `E` 上 `AnalyticOnNhd ℝ`。

Mathlib 没有"参数积分的解析性"，这里用 Banach 代数技巧绕开幂级数的多线性簿记：
- `Φ : E →L[ℝ] (E →ᵇ ℝ)`，`a ↦ (y ↦ ⟪a, r y⟫)`，其中 `r` 是径向 clip 到 `closedBall 0 R`
  （`supp g ⊆ closedBall 0 R`，所以在 `supp g` 上 `r y = y`）；
- `NormedSpace.exp : (E →ᵇ ℝ) → (E →ᵇ ℝ)` 解析（Banach 代数的 exp，`NormedSpace.exp_analytic`），
  且逐点 `exp h y = Real.exp (h y)`；
- `ψ : (E →ᵇ ℝ) →L[ℝ] F`，`h ↦ ∫ y, h y • g y ∂μ`。
于是 `a ↦ ∫ exp⟪a,y⟫ • g y = ψ (exp (Φ a))` 是解析映射的复合。
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped Topology BoundedContinuousFunction

namespace DifferentialGeometry.Analysis.Analytic

section Clip

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- 径向 clip：`clipF3B1 R y = (R / max R ‖y‖) • y`，像落在 `closedBall 0 R`，在该球上是恒等。 -/
def clipF3B1 (R : ℝ) (y : E) : E := (R / max R ‖y‖) • y

theorem continuous_clipF3B1 {R : ℝ} (hR : 0 < R) : Continuous (clipF3B1 (E := E) R) := by
  unfold clipF3B1
  refine Continuous.smul ?_ continuous_id
  refine continuous_const.div (continuous_const.max continuous_norm) fun y => ?_
  exact (lt_of_lt_of_le hR (le_max_left _ _)).ne'

theorem norm_clipF3B1_le {R : ℝ} (hR : 0 < R) (y : E) : ‖clipF3B1 R y‖ ≤ R := by
  unfold clipF3B1
  have hpos : 0 < max R ‖y‖ := lt_of_lt_of_le hR (le_max_left _ _)
  rw [norm_smul, Real.norm_of_nonneg (div_nonneg hR.le hpos.le), div_mul_eq_mul_div,
    div_le_iff₀ hpos]
  exact mul_le_mul_of_nonneg_left (le_max_right _ _) hR.le

theorem clipF3B1_of_norm_le {R : ℝ} (hR : 0 < R) {y : E} (hy : ‖y‖ ≤ R) : clipF3B1 R y = y := by
  unfold clipF3B1
  rw [max_eq_left hy, div_self hR.ne', one_smul]

end Clip

section InnerClip

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- 线性嵌入 `a ↦ (y ↦ ⟪a, clip y⟫)` 进有界连续函数代数。 -/
def innerClipCLM_F3B1 {R : ℝ} (hR : 0 < R) : E →L[ℝ] (E →ᵇ ℝ) :=
  LinearMap.mkContinuous
    { toFun := fun a =>
        BoundedContinuousFunction.ofNormedAddCommGroup (fun y => inner ℝ a (clipF3B1 R y))
          ((continuous_const.inner (continuous_clipF3B1 hR))) (‖a‖ * R) fun y => by
            refine (norm_inner_le_norm _ _).trans ?_
            exact mul_le_mul_of_nonneg_left (norm_clipF3B1_le hR y) (norm_nonneg _)
      map_add' := fun a b => by
        ext y
        simp [inner_add_left]
      map_smul' := fun c a => by
        ext y
        simp [inner_smul_left] }
    R fun a => by
      refine (BoundedContinuousFunction.norm_le (by positivity)).2 fun y => ?_
      change ‖inner ℝ a (clipF3B1 R y)‖ ≤ R * ‖a‖
      rw [mul_comm]
      exact (norm_inner_le_norm _ _).trans
        (mul_le_mul_of_nonneg_left (norm_clipF3B1_le hR y) (norm_nonneg _))

theorem innerClipCLM_F3B1_apply {R : ℝ} (hR : 0 < R) (a y : E) :
    innerClipCLM_F3B1 hR a y = inner ℝ a (clipF3B1 R y) := rfl

end InnerClip

section IntegralCLM

variable {E F : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [OpensMeasurableSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] (μ : Measure E)
  [IsFiniteMeasureOnCompacts μ]

/-- 积分泛函 `h ↦ ∫ y, h y • g y ∂μ` 是 `(E →ᵇ ℝ) →L[ℝ] F`（`g` 连续紧支撑）。 -/
def integralSmulCLM_F3B1 {g : E → F} (hg : Continuous g)
    (hc : HasCompactSupport g) : (E →ᵇ ℝ) →L[ℝ] F :=
  LinearMap.mkContinuous
    { toFun := fun h => ∫ y, h y • g y ∂μ
      map_add' := fun h h' => by
        have hi : ∀ k : E →ᵇ ℝ, Integrable (fun y => k y • g y) μ := fun k =>
          (k.continuous.smul hg).integrable_of_hasCompactSupport (hc.smul_left)
        change ∫ y, (h + h') y • g y ∂μ = (∫ y, h y • g y ∂μ) + ∫ y, h' y • g y ∂μ
        rw [← integral_add (hi h) (hi h')]
        exact integral_congr_ae (Eventually.of_forall fun y => by simp [add_smul])
      map_smul' := fun c h => by
        change ∫ y, (c • h) y • g y ∂μ = c • ∫ y, h y • g y ∂μ
        rw [← integral_smul c]
        exact integral_congr_ae (Eventually.of_forall fun y => by
          simp [mul_smul]) }
    (∫ y, ‖g y‖ ∂μ) fun h => by
      have hi : Integrable (fun y => ‖g y‖) μ :=
        (hg.norm).integrable_of_hasCompactSupport hc.norm
      calc ‖∫ y, h y • g y ∂μ‖ ≤ ∫ y, ‖h‖ * ‖g y‖ ∂μ := by
            refine norm_integral_le_of_norm_le (hi.const_mul ‖h‖) (Eventually.of_forall fun y => ?_)
            rw [norm_smul]
            exact mul_le_mul_of_nonneg_right (h.norm_coe_le_norm y) (norm_nonneg _)
        _ = (∫ y, ‖g y‖ ∂μ) * ‖h‖ := by
            rw [integral_const_mul, mul_comm]

omit [CompleteSpace F] in
theorem integralSmulCLM_F3B1_apply {g : E → F} (hg : Continuous g) (hc : HasCompactSupport g)
    (h : E →ᵇ ℝ) : integralSmulCLM_F3B1 μ hg hc h = ∫ y, h y • g y ∂μ := rfl

end IntegralCLM

section ExpEval

variable {E : Type*} [TopologicalSpace E]

/-- Banach 代数 `E →ᵇ ℝ` 里的 `exp` 逐点就是 `Real.exp`。 -/
theorem exp_apply_F3B1 (h : E →ᵇ ℝ) (y : E) : NormedSpace.exp h y = Real.exp (h y) := by
  have h1 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) h
  have h2 := h1.mapL (BoundedContinuousFunction.evalCLM ℝ y)
  have h3 := NormedSpace.exp_series_hasSum_exp' (𝕂 := ℝ) (h y)
  rw [Real.exp_eq_exp_ℝ]
  have h2' : HasSum (fun n : ℕ => ((n.factorial : ℝ)⁻¹) • (h y) ^ n) (NormedSpace.exp h y) := by
    simpa [BoundedContinuousFunction.evalCLM] using h2
  exact h2'.unique h3

end ExpEval

section Laplace

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [ProperSpace E]
  [MeasurableSpace E] [OpensMeasurableSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]
  [CompleteSpace F] (μ : Measure E) [IsFiniteMeasureOnCompacts μ]

omit [ProperSpace E] [CompleteSpace F] in
/-- **紧支撑函数的 Laplace 变换是整函数**：`g` 连续紧支撑 ⇒
`a ↦ ∫ y, Real.exp ⟪a, y⟫ • g y ∂μ` 在 `univ` 上 `AnalyticOnNhd ℝ`。 -/
theorem analyticOnNhd_integral_exp_inner_smul_F3B1 {g : E → F} (hg : Continuous g)
    (hc : HasCompactSupport g) :
    AnalyticOnNhd ℝ (fun a : E => ∫ y, Real.exp (inner ℝ a y) • g y ∂μ) univ := by
  obtain ⟨R₀, hR₀⟩ := hc.isCompact.isBounded.subset_closedBall (0 : E)
  set R : ℝ := max R₀ 1 with hRdef
  have hR : 0 < R := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hsupp : ∀ y, g y ≠ 0 → ‖y‖ ≤ R := fun y hy => by
    have := hR₀ (subset_tsupport g (Function.mem_support.2 hy))
    rw [Metric.mem_closedBall, dist_zero_right] at this
    exact this.trans (le_max_left _ _)
  have heq : (fun a : E => ∫ y, Real.exp (inner ℝ a y) • g y ∂μ) =
      fun a => integralSmulCLM_F3B1 μ hg hc (NormedSpace.exp (innerClipCLM_F3B1 hR a)) := by
    funext a
    rw [integralSmulCLM_F3B1_apply]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    by_cases hy : g y = 0
    · simp [hy]
    · simp only [exp_apply_F3B1, innerClipCLM_F3B1_apply, clipF3B1_of_norm_le hR (hsupp y hy)]
  rw [heq]
  intro a _
  have h1 : AnalyticAt ℝ (fun a => innerClipCLM_F3B1 hR a) a := (innerClipCLM_F3B1 hR).analyticAt a
  have h2 : AnalyticAt ℝ (NormedSpace.exp : (E →ᵇ ℝ) → (E →ᵇ ℝ)) (innerClipCLM_F3B1 hR a) :=
    NormedSpace.exp_analytic _
  exact (integralSmulCLM_F3B1 μ hg hc).analyticAt _ |>.comp (h2.comp h1)

end Laplace

end DifferentialGeometry.Analysis.Analytic
