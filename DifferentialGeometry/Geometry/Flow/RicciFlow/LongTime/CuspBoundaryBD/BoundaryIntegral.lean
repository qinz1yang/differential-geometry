import DifferentialGeometry.Geometry.Curvature.DiskTraceDensity
import DifferentialGeometry.Geometry.Metric.CurveUnitReparametrization
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds

/-!
# IMS04 / G5a（S-A10-BOUNDARY, suffix `_BD`）：`diskMapTraceBoundaryDensity` 的积分 ≤ sup|κ| · 弧长

IMS09 Gauss–Bonnet 的边界项是
`∫_{-π}^{π} diskMapTraceBoundaryDensity g U γ φ θ dθ`，被积函数 = `⟨κ_γ(φθ), ν(z)⟩ · |∂_θ(U∘c)|`
（`ν` 单位 inward conormal，`|∂_θ(U∘c)| = riemannianCurveSpeed g (γ∘φ) θ`）。

* `abs_diskMapTraceBoundaryDensity_le_BD`：逐点 `|density θ| ≤ K · (φ'(θ) · |γ'(φ θ)|_g)`，
  只要 `|κ_γ(φ θ)|_g ≤ K`（Cauchy–Schwarz + `ν` 单位 + `riemannianCurveSpeed_reparam`）；
* `abs_integral_diskMapTraceBoundaryDensity_le_BD`：`|∫ density| ≤ K · ∫_0^1 |γ'|_g`
  （换元 `integral_comp_mul_deriv` + `φ(π) = φ(-π) + 1`（degree-one）+ `γ` 周期 1）。

`φ` monotone、`φ(π) = φ(-π) + 1` 是 weak-Jordan 迹（`IsWeaklyMonotoneOnce`）的性质，不是新几何假设。
-/

set_option autoImplicit false
noncomputable section
open Set Function Bundle Manifold DifferentialGeometry MeasureTheory
open scoped Topology ContDiff Bundle Manifold Real
namespace GC.LongTime
open DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- 逐点：`|density θ| ≤ K · (|φ'(θ)| · speed_γ(φ θ))`。 -/
theorem abs_diskMapTraceBoundaryDensity_le_BD (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {U : ℂ → M} {γ : ℝ → M} {φ : ℝ → ℝ} {θ : ℝ}
    (hU : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (circleMap 0 1 θ))
    (hconf : DiskMapConformalAt g U (circleMap 0 1 θ))
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ (φ θ)) (hφ : DifferentiableAt ℝ φ θ)
    (htrace : U ∘ circleMap 0 1 = γ ∘ φ) {K : ℝ}
    (hK : Real.sqrt (g.inner (γ (φ θ)) (riemannianCurveCurvature g γ (φ θ))
      (riemannianCurveCurvature g γ (φ θ))) ≤ K) :
    |diskMapTraceBoundaryDensity g U γ φ θ| ≤
      K * (|deriv φ θ| * riemannianCurveSpeed g γ (φ θ)) := by
  have hK0 : 0 ≤ K := (Real.sqrt_nonneg _).trans hK
  have hspeed : Real.sqrt (diskMapConformalCoefficient g U (circleMap 0 1 θ)) =
      |deriv φ θ| * riemannianCurveSpeed g γ (φ θ) := by
    rw [← riemannianCurveSpeed_diskMapBoundary g hU hconf, htrace]
    exact riemannianCurveSpeed_reparam g hγ hφ
  have hnonneg : 0 ≤ |deriv φ θ| * riemannianCurveSpeed g γ (φ θ) :=
    mul_nonneg (abs_nonneg _) (riemannianCurveSpeed_nonneg _ _ _)
  rcases eq_or_lt_of_le (diskMapConformalCoefficient_nonneg g U (circleMap 0 1 θ)) with h0 | hpos
  · rw [diskMapTraceBoundaryDensity_eq_zero g U γ φ h0.symm, abs_zero]
    exact mul_nonneg hK0 hnonneg
  · have hunit := hconf.inwardConormal_unit (by simp) hpos
    have hxy : U (circleMap 0 1 θ) = γ (φ θ) := congrFun htrace θ
    have hCS := SmoothRiemannianMetric.metric_inner_cauchy_schwarz_sq g (U (circleMap 0 1 θ))
      (riemannianCurveCurvature g γ (φ θ) : E) (diskMapInwardConormal g U (circleMap 0 1 θ))
    rw [hunit, mul_one] at hCS
    have hcs : |g.inner (U (circleMap 0 1 θ)) (riemannianCurveCurvature g γ (φ θ) : E)
        (diskMapInwardConormal g U (circleMap 0 1 θ))| ≤ K := by
      refine (Real.abs_le_sqrt hCS).trans ?_
      have key : ∀ (x y : M) (h : x = y) (a : E), g.inner x a a = g.inner y a a := by
        intro x y h a
        subst h
        rfl
      exact (congrArg Real.sqrt (key _ _ hxy (riemannianCurveCurvature g γ (φ θ) : E))).trans_le hK
    unfold diskMapTraceBoundaryDensity
    simp only []
    rw [abs_mul, ← hspeed, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_mul_of_nonneg_right hcs (Real.sqrt_nonneg _)

/-- **G5a 主定理**：`|∫_{-π}^{π} diskMapTraceBoundaryDensity| ≤ K · ∫_0^1 |γ'|_g`，
`K ≥ sup |κ_γ|_g`；`φ` 光滑 monotone，`φ π = φ (-π) + 1`，`γ` 周期 1，`U ∘ c = γ ∘ φ`。 -/
theorem abs_integral_diskMapTraceBoundaryDensity_le_BD (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {U : ℂ → M} {s : Set ℂ} (hs : IsOpen s) (hU : ContMDiffOn 𝓘(ℝ, ℂ) 𝓘(ℝ, E) ∞ U s)
    (hDs : Metric.closedBall (0 : ℂ) 1 ⊆ s)
    (hconf : ∀ q ∈ Metric.closedBall (0 : ℂ) 1, DiskMapConformalAt g U q)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hi : ∀ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t (1 : ℝ) ≠ 0) (hγper : ∀ x, γ (x + 1) = γ x)
    {φ : ℝ → ℝ} (hφ : ContDiff ℝ ∞ φ) (hmono : Monotone φ) (hdeg : φ π = φ (-π) + 1)
    (htrace : U ∘ circleMap 0 1 = γ ∘ φ) {K : ℝ}
    (hK : ∀ x, Real.sqrt (g.inner (γ x) (riemannianCurveCurvature g γ x)
      (riemannianCurveCurvature g γ x)) ≤ K) :
    |∫ θ in -π..π, diskMapTraceBoundaryDensity g U γ φ θ| ≤
      K * ∫ x in (0 : ℝ)..1, riemannianCurveSpeed g γ x := by
  have hden : Continuous (diskMapTraceBoundaryDensity g U γ φ) :=
    (contDiff_diskMapTraceBoundaryDensity g hs hU hDs hconf hγ hi hφ htrace).continuous
  have hdφ : ∀ θ, HasDerivAt φ (deriv φ θ) θ := fun θ =>
    ((hφ.differentiable (by simp)) θ).hasDerivAt
  have hdφc : Continuous (deriv φ) := hφ.continuous_deriv (by simp)
  have hsp : Continuous (riemannianCurveSpeed g γ) :=
    (contDiff_riemannianCurveSpeed g hγ hi).continuous
  have hpt : ∀ θ, |diskMapTraceBoundaryDensity g U γ φ θ| ≤
      K * (deriv φ θ * riemannianCurveSpeed g γ (φ θ)) := by
    intro θ
    have hz : circleMap 0 1 θ ∈ Metric.closedBall (0 : ℂ) 1 := by
      simp [Metric.mem_closedBall, dist_zero_right]
    have hUm : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, E) U (circleMap 0 1 θ) :=
      ((hU _ (hDs hz)).contMDiffAt (hs.mem_nhds (hDs hz))).mdifferentiableAt (by simp)
    have := abs_diskMapTraceBoundaryDensity_le_BD g hUm (hconf _ hz)
      ((hγ (φ θ)).mdifferentiableAt (by simp)) (((hφ.differentiable (by simp)) θ)) htrace (hK _)
    rwa [abs_of_nonneg (hmono.deriv_nonneg (x := θ))] at this
  have hbound : Continuous (fun θ => K * (deriv φ θ * riemannianCurveSpeed g γ (φ θ))) :=
    continuous_const.mul (hdφc.mul (hsp.comp hφ.continuous))
  have hle : -π ≤ π := by linarith [Real.pi_pos]
  have hsub : ∫ θ in -π..π, K * (deriv φ θ * riemannianCurveSpeed g γ (φ θ)) =
      K * ∫ x in φ (-π)..φ π, riemannianCurveSpeed g γ x := by
    rw [intervalIntegral.integral_const_mul]
    congr 1
    have hcomp := intervalIntegral.integral_comp_mul_deriv (a := -π) (b := π) (f := φ)
      (f' := deriv φ) (g := riemannianCurveSpeed g γ) (fun x _ => hdφ x) hdφc.continuousOn hsp
    rw [← hcomp]
    refine intervalIntegral.integral_congr (fun x _ => ?_)
    exact mul_comm _ _
  have hperiod : Function.Periodic (riemannianCurveSpeed g γ) 1 := by
    intro x
    have hx := riemannianCurveSpeed_reparam g (γ := γ) (φ := fun y : ℝ => y + 1) (t := x)
      ((hγ (x + 1)).mdifferentiableAt (by simp)) (by fun_prop)
    have hfun : γ ∘ (fun y : ℝ => y + 1) = γ := funext hγper
    rw [hfun] at hx
    simpa using hx.symm
  have hcirc : ∫ x in φ (-π)..φ π, riemannianCurveSpeed g γ x =
      ∫ x in (0 : ℝ)..1, riemannianCurveSpeed g γ x := by
    rw [hdeg]
    have := hperiod.intervalIntegral_add_eq (φ (-π)) 0
    simpa using this
  calc |∫ θ in -π..π, diskMapTraceBoundaryDensity g U γ φ θ|
      ≤ ∫ θ in -π..π, |diskMapTraceBoundaryDensity g U γ φ θ| :=
        intervalIntegral.abs_integral_le_integral_abs hle
    _ ≤ ∫ θ in -π..π, K * (deriv φ θ * riemannianCurveSpeed g γ (φ θ)) :=
        intervalIntegral.integral_mono_on hle (hden.abs.intervalIntegrable _ _)
          (hbound.intervalIntegrable _ _) (fun θ _ => hpt θ)
    _ = K * ∫ x in (0 : ℝ)..1, riemannianCurveSpeed g γ x := by rw [hsub, hcirc]

end GC.LongTime
