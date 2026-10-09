import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Normed.Module.Convex

/-!
# 内蕴距离沿曲线的 Lipschitz 界（O-W-GEO-MIN G1，后缀 `_GM`）

`g_Σ = lam |dz|²` 在开集 `Ω ⊆ ℂ` 上。到 `p` 的内蕴距离以显式函数 `d : ℂ → ℝ` 进入，只要两条性质：
`ContinuousOn d Ω` 与**线段 Lipschitz**
`segment ℝ x y ⊆ Ω → d y ≤ d x + ∫₀¹ √lam(x + t(y − x)) ‖y − x‖ dt`
（多边形内蕴距离——直线段链的 `g_Σ`-长度的下确界——由单段链 + 三角不等式直接满足）。

主定理 `le_add_integral_of_segment_GM`：对 `C¹` 曲线 `η`，`η [a, b] ⊆ Ω`，
`d (η b) ≤ d (η a) + ∫ₐᵇ √lam(η) ‖η′‖`。证明：右 Dini 导数比较
（`image_le_of_liminf_slope_right_le_deriv_boundary`），逐点用线段性质 + `η` 的可微性。
-/

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology

namespace DifferentialGeometry.Geometry

/-- 小正数 `ε` 使 `(A + ε)(B + ε) < r`（`A B < r`）。 -/
theorem exists_pos_add_mul_add_lt_GM {A B r : ℝ} (h : A * B < r) :
    ∃ ε > 0, (A + ε) * (B + ε) < r := by
  have ht : Tendsto (fun e : ℝ => (A + e) * (B + e)) (𝓝[>] 0) (𝓝 (A * B)) := by
    have hc : Continuous (fun e : ℝ => (A + e) * (B + e)) := by fun_prop
    simpa using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  obtain ⟨ε, h1, h2⟩ := ((ht.eventually (gt_mem_nhds h)).and self_mem_nhdsWithin).exists
  exact ⟨ε, h2, h1⟩

/-- 逐点的右 Dini 界：`x` 处 `slope (d ∘ η) x z` 最终 `< r`，只要 `√lam(η x) ‖η′ x‖ < r`。 -/
theorem eventually_slope_lt_GM {Ω : Set ℂ} (hΩ : IsOpen Ω) {lam d : ℂ → ℝ}
    (hlam : ContinuousOn lam Ω)
    (hseg : ∀ x y : ℂ, segment ℝ x y ⊆ Ω →
      d y ≤ d x + ∫ t in (0 : ℝ)..1, Real.sqrt (lam (x + t • (y - x))) * ‖y - x‖)
    {η : ℝ → ℂ} {x : ℝ} {η' : ℂ} (hη : HasDerivAt η η' x) (hx : η x ∈ Ω) {r : ℝ}
    (hr : Real.sqrt (lam (η x)) * ‖η'‖ < r) :
    ∀ᶠ z in 𝓝[>] x, slope (fun t => d (η t)) x z < r := by
  obtain ⟨ε, hε, hεr⟩ := exists_pos_add_mul_add_lt_GM hr
  set A := Real.sqrt (lam (η x)) with hA
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hsl : ContinuousAt (fun w => Real.sqrt (lam w)) (η x) :=
    (hlam.continuousAt (hΩ.mem_nhds hx)).sqrt
  have hev : ∀ᶠ w in 𝓝 (η x), w ∈ Ω ∧ Real.sqrt (lam w) < A + ε :=
    (hΩ.eventually_mem hx).and (hsl.eventually (gt_mem_nhds (by linarith)))
  obtain ⟨δ, hδ, hball⟩ := Metric.eventually_nhds_iff_ball.mp hev
  have hlo := hη.isLittleO.def hε
  have hcont : ∀ᶠ z in 𝓝 x, η z ∈ ball (η x) δ :=
    hη.continuousAt.eventually (ball_mem_nhds _ hδ)
  filter_upwards [nhdsWithin_le_nhds hlo, nhdsWithin_le_nhds hcont, self_mem_nhdsWithin]
    with z hz1 hz2 hz3
  have hzx : 0 < z - x := sub_pos.mpr hz3
  set Δ := η z - η x with hΔ
  have hnorm : ‖Δ‖ ≤ (z - x) * (‖η'‖ + ε) := by
    have h1 : ‖Δ‖ ≤ ‖(z - x) • η'‖ + ‖Δ - (z - x) • η'‖ := by
      have := norm_add_le ((z - x) • η') (Δ - (z - x) • η')
      simpa using this
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hzx] at h1
    have h2 : ‖Δ - (z - x) • η'‖ ≤ ε * (z - x) := by
      have := hz1
      rw [Real.norm_eq_abs, abs_of_pos hzx] at this
      simpa [hΔ] using this
    nlinarith
  have hsegsub : segment ℝ (η x) (η z) ⊆ ball (η x) δ :=
    (convex_ball (η x) δ).segment_subset (mem_ball_self hδ) hz2
  have hint : ∫ t in (0 : ℝ)..1, Real.sqrt (lam (η x + t • Δ)) * ‖Δ‖ ≤ (A + ε) * ‖Δ‖ := by
    have hmem : ∀ t ∈ Icc (0 : ℝ) 1, η x + t • Δ ∈ ball (η x) δ := by
      intro t ht
      apply hsegsub
      rw [segment_eq_image']
      exact ⟨t, ht, rfl⟩
    have hci : ContinuousOn (fun t : ℝ => Real.sqrt (lam (η x + t • Δ)) * ‖Δ‖) (Icc 0 1) := by
      refine ContinuousOn.mul ?_ continuousOn_const
      refine ContinuousOn.sqrt ?_
      refine hlam.comp (by fun_prop) ?_
      intro t ht
      exact (hball _ (hmem t ht)).1
    calc ∫ t in (0 : ℝ)..1, Real.sqrt (lam (η x + t • Δ)) * ‖Δ‖
        ≤ ∫ _t in (0 : ℝ)..1, (A + ε) * ‖Δ‖ := by
          refine intervalIntegral.integral_mono_on zero_le_one
            (hci.intervalIntegrable_of_Icc zero_le_one) intervalIntegrable_const ?_
          intro t ht
          exact mul_le_mul_of_nonneg_right (hball _ (hmem t ht)).2.le (norm_nonneg _)
      _ = (A + ε) * ‖Δ‖ := by simp
  have hd := hseg (η x) (η z) (hsegsub.trans fun w hw => (hball w hw).1)
  rw [slope_def_field]
  rw [div_lt_iff₀ hzx]
  have : d (η z) - d (η x) ≤ (A + ε) * ((z - x) * (‖η'‖ + ε)) :=
    by nlinarith [mul_le_mul_of_nonneg_left hnorm (by linarith : 0 ≤ A + ε)]
  nlinarith

/-- **线段 Lipschitz ⇒ 曲线 Lipschitz**：`d (η b) ≤ d (η a) + ∫ₐᵇ √lam(η) ‖η′‖`。 -/
theorem le_add_integral_of_segment_GM {Ω : Set ℂ} (hΩ : IsOpen Ω) {lam d : ℂ → ℝ}
    (hlam : ContinuousOn lam Ω) (hd : ContinuousOn d Ω)
    (hseg : ∀ x y : ℂ, segment ℝ x y ⊆ Ω →
      d y ≤ d x + ∫ t in (0 : ℝ)..1, Real.sqrt (lam (x + t • (y - x))) * ‖y - x‖)
    {η : ℝ → ℂ} (hη : ContDiff ℝ 1 η) {a b : ℝ} (hab : a ≤ b)
    (hηΩ : ∀ t ∈ Icc a b, η t ∈ Ω) :
    d (η b) ≤ d (η a) + ∫ t in a..b, Real.sqrt (lam (η t)) * ‖deriv η t‖ := by
  set F : ℝ → ℝ := fun t => Real.sqrt (lam (η t)) * ‖deriv η t‖ with hF
  have hFc : ContinuousOn F (Icc a b) := by
    refine ContinuousOn.mul ?_ (hη.continuous_deriv le_rfl).norm.continuousOn
    exact (hlam.comp hη.continuous.continuousOn hηΩ).sqrt
  set P : ℝ → ℝ := fun t => max a (min t b) with hP
  have hPmem : ∀ t, P t ∈ Icc a b := fun t => ⟨le_max_left _ _, max_le hab (min_le_right _ _)⟩
  have hPeq : ∀ t ∈ Icc a b, P t = t := by
    intro t ht
    simp [hP, min_eq_left ht.2, max_eq_right ht.1]
  set Ft : ℝ → ℝ := fun t => F (P t) with hFt
  have hFtc : Continuous Ft :=
    hFc.comp_continuous (continuous_const.max (continuous_id.min continuous_const)) hPmem
  have hder : ∀ t, HasDerivAt (fun u => d (η a) + ∫ s in a..u, Ft s) (Ft t) t :=
    fun t => ((hFtc.integral_hasStrictDerivAt a t).hasDerivAt).const_add _
  have hfc : ContinuousOn (fun t => d (η t)) (Icc a b) :=
    hd.comp hη.continuous.continuousOn hηΩ
  have key := image_le_of_liminf_slope_right_le_deriv_boundary hfc
    (B := fun u => d (η a) + ∫ s in a..u, Ft s) (B' := Ft) (by simp)
    (fun t _ => (hder t).continuousAt.continuousWithinAt)
    (fun t _ => (hder t).hasDerivWithinAt)
    (by
      intro x hx r hr
      have hxI : x ∈ Icc a b := Ico_subset_Icc_self hx
      have hr' : Real.sqrt (lam (η x)) * ‖deriv η x‖ < r := by
        have : Ft x = F x := by simp [hFt, hPeq x hxI]
        rw [this] at hr
        exact hr
      exact (eventually_slope_lt_GM hΩ hlam hseg
        ((hη.differentiable one_ne_zero x).hasDerivAt) (hηΩ x hxI) hr').frequently)
    (right_mem_Icc.mpr hab)
  refine key.trans (le_of_eq ?_)
  congr 1
  refine intervalIntegral.integral_congr fun t ht => ?_
  rw [uIcc_of_le hab] at ht
  simp only [hFt, hPeq t ht, hF]

end DifferentialGeometry.Geometry
