import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.CuspBoundaryBD.BoundaryIntegral

/-!
# IMS04 / G4a（O-W-CURV, suffix `_CV`）：flux 积分界

S-A10-DERIV G6″ 的 flux 项
`f = ∫_{-π}^{π} g(W θ, ν_in(e^{iθ})) · √coef(e^{iθ}) dθ`（`W θ` = transport 在边界点的 `t₀`-速度）。
逐点 `|W θ|_g · |γ'(φ θ)|_g ≤ B` ⇒ `|f| ≤ B`：

`|g(W, ν)| ≤ |W|`（`ν` 单位，Cauchy–Schwarz），`√coef = φ'(θ)·|γ'(φ θ)|`（共形 + 迹），
`∫ B φ' = B (φ π − φ(−π)) = B`（degree one）。与 BOUNDARY G5a 的 `abs_integral_…_le_BD` 同一套换元。
-/

set_option autoImplicit false
noncomputable section
open Set Function Bundle Manifold DifferentialGeometry MeasureTheory
open scoped Topology ContDiff Bundle Manifold Real
namespace GC.LongTime
open DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

omit [FiniteDimensional ℝ E] in
/-- 逐点：`|g(W, ν) √coef| ≤ φ'(θ) · (|W|_g · |γ'(φ θ)|_g)`。 -/
theorem abs_flux_integrand_le_CV (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {U : ℂ → M} {γ : ℝ → M} {φ : ℝ → ℝ} {θ : ℝ}
    (hU : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (circleMap 0 1 θ))
    (hconf : DiskMapConformalAt g U (circleMap 0 1 θ))
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ (φ θ)) (hφ : DifferentiableAt ℝ φ θ)
    (htrace : U ∘ circleMap 0 1 = γ ∘ φ) (W : E) :
    |g.inner (U (circleMap 0 1 θ)) W (diskMapInwardConormal g U (circleMap 0 1 θ)) *
        Real.sqrt (diskMapConformalCoefficient g U (circleMap 0 1 θ))| ≤
      |deriv φ θ| * (Real.sqrt (g.inner (U (circleMap 0 1 θ)) W W) *
        riemannianCurveSpeed g γ (φ θ)) := by
  have hspeed : Real.sqrt (diskMapConformalCoefficient g U (circleMap 0 1 θ)) =
      |deriv φ θ| * riemannianCurveSpeed g γ (φ θ) := by
    rw [← riemannianCurveSpeed_diskMapBoundary g hU hconf, htrace]
    exact riemannianCurveSpeed_reparam g hγ hφ
  have hnn : 0 ≤ |deriv φ θ| * (Real.sqrt (g.inner (U (circleMap 0 1 θ)) W W) *
      riemannianCurveSpeed g γ (φ θ)) :=
    mul_nonneg (abs_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (riemannianCurveSpeed_nonneg _ _ _))
  rcases eq_or_lt_of_le (diskMapConformalCoefficient_nonneg g U (circleMap 0 1 θ)) with h0 | hpos
  · rw [← h0, Real.sqrt_zero, mul_zero, abs_zero]
    exact hnn
  · have hunit := hconf.inwardConormal_unit (by simp) hpos
    have hCS := SmoothRiemannianMetric.metric_inner_cauchy_schwarz_sq g (U (circleMap 0 1 θ))
      W (diskMapInwardConormal g U (circleMap 0 1 θ))
    rw [hunit, mul_one] at hCS
    have hcs := Real.abs_le_sqrt hCS
    rw [abs_mul, hspeed, abs_of_nonneg (mul_nonneg (abs_nonneg _)
      (riemannianCurveSpeed_nonneg _ _ _))]
    calc _ ≤ Real.sqrt (g.inner (U (circleMap 0 1 θ)) W W) *
          (|deriv φ θ| * riemannianCurveSpeed g γ (φ θ)) :=
          mul_le_mul_of_nonneg_right hcs
            (mul_nonneg (abs_nonneg _) (riemannianCurveSpeed_nonneg _ _ _))
      _ = _ := by ring

omit [FiniteDimensional ℝ E] in
/-- **flux 积分界**：逐点 `|W θ|_g · |γ'(φ θ)|_g ≤ B`，`φ` `C¹` monotone degree one，`U ∘ c = γ ∘ φ`
（`U` 在边界圆上可微且共形）⇒ `|∫_{-π}^{π} g(W θ, ν_in) √coef dθ| ≤ B`。 -/
theorem abs_integral_flux_le_CV (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {U : ℂ → M}
    (hU : ∀ θ, MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (circleMap 0 1 θ))
    (hconf : ∀ θ, DiskMapConformalAt g U (circleMap 0 1 θ))
    {γ : ℝ → M} (hγ : ∀ x, MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ x)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ 1 φ) (hmono : Monotone φ) (hdeg : φ π = φ (-π) + 1)
    (htrace : U ∘ circleMap 0 1 = γ ∘ φ) (W : ℝ → E) {B : ℝ}
    (hB : ∀ θ, Real.sqrt (g.inner (U (circleMap 0 1 θ)) (W θ) (W θ)) *
      riemannianCurveSpeed g γ (φ θ) ≤ B) :
    |∫ θ in -π..π, g.inner (U (circleMap 0 1 θ)) (W θ)
        (diskMapInwardConormal g U (circleMap 0 1 θ)) *
        Real.sqrt (diskMapConformalCoefficient g U (circleMap 0 1 θ))| ≤ B := by
  have hφd : Differentiable ℝ φ := hφ.differentiable one_ne_zero
  have hdφc : Continuous (deriv φ) := hφ.continuous_deriv le_rfl
  have hpt : ∀ θ, ‖g.inner (U (circleMap 0 1 θ)) (W θ)
      (diskMapInwardConormal g U (circleMap 0 1 θ)) *
      Real.sqrt (diskMapConformalCoefficient g U (circleMap 0 1 θ))‖ ≤ B * deriv φ θ := by
    intro θ
    rw [Real.norm_eq_abs]
    refine (abs_flux_integrand_le_CV g (hU θ) (hconf θ) (hγ (φ θ)) (hφd θ) htrace (W θ)).trans ?_
    rw [abs_of_nonneg (hmono.deriv_nonneg (x := θ)), mul_comm]
    exact mul_le_mul_of_nonneg_right (hB θ) (hmono.deriv_nonneg (x := θ))
  have hle : -π ≤ π := by linarith [Real.pi_pos]
  have hint : ∫ θ in -π..π, B * deriv φ θ = B := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_deriv_eq_sub (fun x _ => hφd x) (hdφc.intervalIntegrable _ _),
      hdeg]
    ring
  rw [← Real.norm_eq_abs, ← hint]
  exact intervalIntegral.norm_integral_le_of_norm_le hle
    (Filter.Eventually.of_forall fun θ _ => hpt θ)
    ((continuous_const.mul hdφc).intervalIntegrable _ _)

end GC.LongTime
