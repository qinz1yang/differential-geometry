import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Topology.Order.IntermediateValue

/-!
# 弧长重参数化（O-W-GEO-MIN G1，后缀 `_GM`）

Hopf–Rinow 的输出按 `ĝ`-弧长参数化；S-W-GEO 的 `harc` 要 `g_Σ`-弧长参数化。这里给两件工具：

* `exists_reparam_GM`：`w` 光滑、`w ≥ c₀ > 0` ⇒ `σ(t) = ∫₀ᵗ w` 是 `ℝ` 的光滑自同胚，逆 `τ` 光滑，
  `σ′ = w`、`τ′ = 1 / w ∘ τ`、`σ 0 = 0`、两者严格单调；
* `weightedLength_comp_GM`：加权长度 `∫ ρ(η)‖η′‖` 在重参数化 `η ∘ σ` 下不变（换元
  `intervalIntegral.integral_comp_mul_deriv'`）。
-/

set_option autoImplicit false

noncomputable section

open Set Filter
open scoped Topology ContDiff Interval

namespace DifferentialGeometry.Geometry

/-- 光滑正权 `w ≥ c₀ > 0` 的原函数 `σ` 与其逆 `τ`：都光滑、严格单调，`σ′ = w`，`τ′ = (w ∘ τ)⁻¹`。 -/
theorem exists_reparam_GM {w : ℝ → ℝ} (hw : ContDiff ℝ ∞ w) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hwc : ∀ t, c₀ ≤ w t) :
    ∃ σ τ : ℝ → ℝ, ContDiff ℝ ∞ σ ∧ ContDiff ℝ ∞ τ ∧ (∀ t, σ (τ t) = t) ∧
      (∀ t, τ (σ t) = t) ∧ (∀ t, HasDerivAt σ (w t) t) ∧
      (∀ s, HasDerivAt τ (w (τ s))⁻¹ s) ∧ StrictMono σ ∧ StrictMono τ ∧ σ 0 = 0 := by
  set σ : ℝ → ℝ := fun t => ∫ s in (0 : ℝ)..t, w s with hσdef
  have hder : ∀ t, HasDerivAt σ (w t) t :=
    fun t => (hw.continuous.integral_hasStrictDerivAt 0 t).hasDerivAt
  have hdiff : Differentiable ℝ σ := fun t => (hder t).differentiableAt
  have hderiv : deriv σ = w := funext fun t => (hder t).deriv
  have hσsm : ContDiff ℝ ∞ σ := contDiff_infty_iff_deriv.mpr ⟨hdiff, by rw [hderiv]; exact hw⟩
  have hmono : StrictMono σ :=
    strictMono_of_deriv_pos fun t => by rw [hderiv]; exact hc₀.trans_le (hwc t)
  have hσ0 : σ 0 = 0 := by simp [hσdef]
  have hlow : ∀ x y, x ≤ y → c₀ * (y - x) ≤ σ y - σ x := fun x y hxy =>
    mul_sub_le_image_sub_of_le_deriv hdiff (fun t => by rw [hderiv]; exact hwc t) hxy
  have htop : Tendsto σ atTop atTop := by
    refine tendsto_atTop_mono' atTop ?_ ((tendsto_id.const_mul_atTop hc₀))
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    have := hlow 0 t ht
    rw [hσ0] at this
    simpa using this
  have hbot : Tendsto σ atBot atBot := by
    refine tendsto_atBot_mono' atBot ?_ ((tendsto_id.const_mul_atBot hc₀))
    filter_upwards [eventually_le_atBot (0 : ℝ)] with t ht
    have := hlow t 0 ht
    rw [hσ0] at this
    simp only [id]
    linarith
  have hsurj : Function.Surjective σ := hσsm.continuous.surjective htop hbot
  let e : ℝ ≃o ℝ := StrictMono.orderIsoOfSurjective σ hmono hsurj
  have he : ∀ t, e t = σ t := fun t => rfl
  have hτsm : ContDiff ℝ ∞ (e.toHomeomorph.symm : ℝ → ℝ) :=
    Homeomorph.contDiff_symm_deriv e.toHomeomorph (f' := w)
      (fun t => (hc₀.trans_le (hwc t)).ne') (fun t => hder t) hσsm
  have hστ : ∀ t, σ (e.symm t) = t := fun t => e.apply_symm_apply t
  have hτσ : ∀ t, e.symm (σ t) = t := fun t => e.symm_apply_apply t
  refine ⟨σ, e.symm, hσsm, hτsm, hστ, hτσ, hder, fun s => ?_, hmono, e.symm.strictMono, hσ0⟩
  refine HasDerivAt.of_local_left_inverse e.symm.toHomeomorph.continuous.continuousAt
    (hder _) (hc₀.trans_le (hwc _)).ne' (Eventually.of_forall hστ)

/-- 加权长度在重参数化下不变：`∫ₐᵇ ρ(η(σ t)) ‖(η ∘ σ)′ t‖ dt = ∫_{σ a}^{σ b} ρ(η)‖η′‖`。 -/
theorem weightedLength_comp_GM {Ω : Set ℂ} {ρ : ℂ → ℝ} (hρ : ContinuousOn ρ Ω)
    {σ w : ℝ → ℝ} (hσ : ∀ t, HasDerivAt σ (w t) t) (hw : Continuous w) (hwpos : ∀ t, 0 < w t)
    {η : ℝ → ℂ} (hη : ContDiff ℝ 1 η) {a b : ℝ} (hab : a ≤ b)
    (hηΩ : ∀ t ∈ Icc a b, η (σ t) ∈ Ω) :
    ∫ t in a..b, ρ ((η ∘ σ) t) * ‖deriv (η ∘ σ) t‖ =
      ∫ s in σ a..σ b, ρ (η s) * ‖deriv η s‖ := by
  set g : ℝ → ℝ := fun s => ρ (η s) * ‖deriv η s‖ with hg
  have hcomp : ∀ t, deriv (η ∘ σ) t = w t • deriv η (σ t) := fun t =>
    (((hη.differentiable one_ne_zero) (σ t)).hasDerivAt.scomp t (hσ t)).deriv
  have hint : ∀ t, ρ ((η ∘ σ) t) * ‖deriv (η ∘ σ) t‖ = (g ∘ σ) t * w t := by
    intro t
    rw [hcomp, norm_smul, Real.norm_eq_abs, abs_of_pos (hwpos t)]
    simp only [hg, Function.comp_apply]
    ring
  simp_rw [hint]
  refine intervalIntegral.integral_comp_mul_deriv' (fun t _ => hσ t) hw.continuousOn ?_
  have hmaps : MapsTo η (σ '' [[a, b]]) Ω := by
    rintro s ⟨t, ht, rfl⟩
    rw [uIcc_of_le hab] at ht
    exact hηΩ t ht
  exact (hρ.comp hη.continuous.continuousOn hmaps).mul
    (hη.continuous_deriv le_rfl).norm.continuousOn

end DifferentialGeometry.Geometry
