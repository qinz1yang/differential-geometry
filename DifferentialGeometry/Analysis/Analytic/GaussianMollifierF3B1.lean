import DifferentialGeometry.Analysis.Analytic.CompactLaplaceF3B1
import Mathlib.Analysis.SpecialFunctions.Gaussian.FourierTransform
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# F3-b (b1)：Gaussian mollifier 是整函数（S-MY-F3B1 G1，后缀 `_F3B1`）

`E` 有限维实内积空间，`volume` 取 `measureSpaceOfInnerProductSpace`。
- `gaussProfileF3B1 w = c · exp(-‖w‖²)`，`c = (∫ exp(-‖v‖²))⁻¹`，所以 `∫ gaussProfileF3B1 = 1`；
- `gaussMollifyF3B1 δ f x = ∫ w, gaussProfileF3B1 w • f (x - δ • w)`（`δ`-缩放的 Gaussian 卷积，
  `δ → 0⁺` 时是 approximate identity）。

**G1 `analyticOnNhd_gaussMollify_F3B1`**：`f : E → F` 连续紧支撑、`δ ≠ 0` ⇒ `gaussMollifyF3B1 δ f`
在 `univ` 上 `AnalyticOnNhd ℝ`。路线：换元 `y = x - δ w` 得 `∫ y, φ(δ⁻¹(x - y)) • f y`，
`exp(-s‖x-y‖²) = exp(-s‖x‖²) · exp⟪2s x, y⟫ · exp(-s‖y‖²)`，剩下的 `a ↦ ∫ exp⟪a,y⟫ • g y`
是 `CompactLaplaceF3B1` 里的整函数。
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Set Filter
open scoped Topology RealInnerProductSpace

namespace DifferentialGeometry.Analysis.Analytic

section Kernel

variable (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]

/-- 归一化常数 `(∫ exp(-‖v‖²))⁻¹`。 -/
def gaussConstF3B1 : ℝ := (∫ v : E, Real.exp (-‖v‖ ^ 2))⁻¹

theorem integrable_exp_neg_sq_norm_F3B1 : Integrable (fun v : E => Real.exp (-‖v‖ ^ 2)) := by
  have h := (GaussianFourier.integrable_cexp_neg_mul_sq_norm_add (V := E) (b := 1)
    (by simp) 0 0).norm
  refine h.congr (Eventually.of_forall fun v => ?_)
  have hre : ((‖v‖ : ℂ) ^ 2).re = ‖v‖ ^ 2 := by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  simp [Complex.norm_exp, hre]

theorem integral_exp_neg_sq_norm_pos_F3B1 : 0 < ∫ v : E, Real.exp (-‖v‖ ^ 2) := by
  have h := GaussianFourier.integral_rexp_neg_mul_sq_norm (V := E) (b := 1) one_pos
  simp only [neg_mul, one_mul, div_one] at h
  rw [h]
  exact Real.rpow_pos_of_pos Real.pi_pos _

theorem gaussConstF3B1_pos : 0 < gaussConstF3B1 E :=
  inv_pos.2 (integral_exp_neg_sq_norm_pos_F3B1 E)

variable {E}

/-- 归一化 Gaussian 轮廓 `φ(w) = c · exp(-‖w‖²)`，`∫ φ = 1`。 -/
def gaussProfileF3B1 (w : E) : ℝ := gaussConstF3B1 E * Real.exp (-‖w‖ ^ 2)

theorem gaussProfileF3B1_nonneg (w : E) : 0 ≤ gaussProfileF3B1 w :=
  mul_nonneg (gaussConstF3B1_pos E).le (Real.exp_pos _).le

theorem continuous_gaussProfileF3B1 : Continuous (gaussProfileF3B1 (E := E)) := by
  unfold gaussProfileF3B1
  fun_prop

theorem integrable_gaussProfileF3B1 : Integrable (gaussProfileF3B1 (E := E)) :=
  (integrable_exp_neg_sq_norm_F3B1 E).const_mul _

theorem integral_gaussProfileF3B1 : ∫ w : E, gaussProfileF3B1 w = 1 := by
  unfold gaussProfileF3B1 gaussConstF3B1
  rw [integral_const_mul, inv_mul_cancel₀ (integral_exp_neg_sq_norm_pos_F3B1 E).ne']

end Kernel

section Mollifier

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- `δ`-缩放的 Gaussian mollifier：`∫ w, φ(w) • f (x - δ w)`。 -/
def gaussMollifyF3B1 (δ : ℝ) (f : E → F) (x : E) : F :=
  ∫ w, gaussProfileF3B1 w • f (x - δ • w)

/-- 换元：`M_δ f x = |δⁿ|⁻¹ • ∫ y, φ(δ⁻¹ (x - y)) • f y`（卷积形式）。 -/
theorem gaussMollifyF3B1_eq_integral_kernel {δ : ℝ} (hδ : δ ≠ 0) (f : E → F) (x : E) :
    gaussMollifyF3B1 δ f x =
      |(δ ^ Module.finrank ℝ E)⁻¹| • ∫ y, gaussProfileF3B1 (δ⁻¹ • (x - y)) • f y := by
  unfold gaussMollifyF3B1
  set H : E → F := fun v => gaussProfileF3B1 (δ⁻¹ • v) • f (x - v) with hH
  have h1 : (fun w : E => gaussProfileF3B1 w • f (x - δ • w)) = fun w => H (δ • w) := by
    funext w
    simp only [hH, inv_smul_smul₀ hδ]
  rw [h1, Measure.integral_comp_smul volume H δ]
  congr 1
  rw [← integral_sub_left_eq_self H volume x]
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp [hH]

end Mollifier

section Factor

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- 核的因子分解：`exp(-s‖x-y‖²) = exp(-s‖x‖²) · exp⟪2s x, y⟫ · exp(-s‖y‖²)`。 -/
theorem exp_neg_mul_sq_norm_sub_F3B1 (s : ℝ) (x y : E) :
    Real.exp (-s * ‖x - y‖ ^ 2) =
      Real.exp (-s * ‖x‖ ^ 2) * Real.exp (⟪(2 * s) • x, y⟫) * Real.exp (-s * ‖y‖ ^ 2) := by
  rw [← Real.exp_add, ← Real.exp_add, norm_sub_sq_real, real_inner_smul_left]
  congr 1
  ring

end Factor

section Analytic

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- **G1：Gaussian mollifier 是整函数。** `f` 连续紧支撑、`δ ≠ 0` ⇒ `x ↦ ∫ w, φ(w) • f (x - δ w)`
在 `univ` 上 `AnalyticOnNhd ℝ`。 -/
theorem analyticOnNhd_gaussMollify_F3B1 {δ : ℝ} (hδ : δ ≠ 0) {f : E → F} (hf : Continuous f)
    (hc : HasCompactSupport f) : AnalyticOnNhd ℝ (gaussMollifyF3B1 δ f) univ := by
  set s : ℝ := (δ⁻¹) ^ 2 with hs
  set c : ℝ := gaussConstF3B1 E with hcdef
  -- 紧支撑连续的 `g y = exp(-s‖y‖²) • f y`
  set g : E → F := fun y => Real.exp (-s * ‖y‖ ^ 2) • f y with hg
  have hgc : Continuous g := by
    refine Continuous.smul ?_ hf
    fun_prop
  have hgs : HasCompactSupport g := hc.smul_left
  have hL := analyticOnNhd_integral_exp_inner_smul_F3B1 (volume : Measure E) hgc hgs
  have hkey : ∀ x, gaussMollifyF3B1 δ f x =
      (|(δ ^ Module.finrank ℝ E)⁻¹| * (c * Real.exp (-s * ‖x‖ ^ 2))) •
        ∫ y, Real.exp (⟪(2 * s) • x, y⟫) • g y := by
    intro x
    have hpt : ∀ y : E, gaussProfileF3B1 (δ⁻¹ • (x - y)) • f y =
        (c * Real.exp (-s * ‖x‖ ^ 2)) • (Real.exp (⟪(2 * s) • x, y⟫) • g y) := by
      intro y
      have hn : ‖δ⁻¹ • (x - y)‖ ^ 2 = s * ‖x - y‖ ^ 2 := by
        rw [norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
      have e1 : gaussProfileF3B1 (δ⁻¹ • (x - y)) =
          c * (Real.exp (-s * ‖x‖ ^ 2) * Real.exp (⟪(2 * s) • x, y⟫) *
            Real.exp (-s * ‖y‖ ^ 2)) := by
        rw [← exp_neg_mul_sq_norm_sub_F3B1, gaussProfileF3B1, hn, neg_mul]
      rw [e1, hg]
      simp only [smul_smul]
      congr 1
      ring
    rw [gaussMollifyF3B1_eq_integral_kernel hδ f x]
    simp_rw [hpt]
    rw [integral_smul, smul_smul]
  have hfun : gaussMollifyF3B1 δ f = fun x =>
      (|(δ ^ Module.finrank ℝ E)⁻¹| * (c * Real.exp (-s * ‖x‖ ^ 2))) •
        ∫ y, Real.exp (⟪(2 * s) • x, y⟫) • g y := funext hkey
  rw [hfun]
  intro x _
  have hA : AnalyticAt ℝ (fun x : E => |(δ ^ Module.finrank ℝ E)⁻¹| * (c * Real.exp (-s * ‖x‖ ^ 2)))
      x := by
    refine analyticAt_const.mul (analyticAt_const.mul ?_)
    have hn : AnalyticAt ℝ (fun x : E => ‖x‖ ^ 2) x := by
      have : (fun x : E => ‖x‖ ^ 2) = fun x => ⟪x, x⟫ := by
        funext x
        rw [real_inner_self_eq_norm_sq]
      rw [this]
      exact (innerSL ℝ : E →L[ℝ] E →L[ℝ] ℝ).analyticAt_bilinear (x, x) |>.comp
        (f := fun x : E => (x, x)) (analyticAt_id.prod analyticAt_id)
    exact (analyticAt_const.mul hn).rexp'
  have hB : AnalyticAt ℝ (fun x : E => ∫ y, Real.exp (⟪(2 * s) • x, y⟫) • g y) x :=
    (hL ((2 * s) • x) (mem_univ _)).comp (f := fun x : E => (2 * s) • x)
      (analyticAt_const.smul analyticAt_id)
  exact hA.smul hB

end Analytic

end DifferentialGeometry.Analysis.Analytic
