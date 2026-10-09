import DifferentialGeometry.Geometry.Curvature.Curve
import DifferentialGeometry.Geometry.Metric.PointwiseInner.Bounds
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.CovariantDerivativeScaling
import DifferentialGeometry.Geometry.Connection.ParallelTransport.Derivative.NormComparison

set_option autoImplicit false
noncomputable section
open DifferentialGeometry DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Geometry.Curvature
open scoped Manifold ContDiff
namespace GC.LongTime

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

theorem sqrt_scaleMetric_inner_BD (c : ℝ) (hc : 0 < c) (g : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    (x : M) (v : TangentSpace 𝓘(ℝ, E) x) :
    Real.sqrt ((scaleMetric c hc g).inner x v v) = Real.sqrt c * Real.sqrt (g.inner x v v) := by
  rw [← Real.sqrt_mul hc.le]
  rfl

theorem riemannianCurveSpeed_scaleMetric_BD (c : ℝ) (hc : 0 < c)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : ℝ → M) (t : ℝ) :
    riemannianCurveSpeed (scaleMetric c hc g) γ t = Real.sqrt c * riemannianCurveSpeed g γ t :=
  sqrt_scaleMetric_inner_BD c hc g _ _

/-- 度量乘常数 `c`：曲率向量乘 `c⁻¹`（弧长缩放 `√c`，曲率缩放 `c^{-1/2}` 的向量版本）。 -/
theorem riemannianCurveCurvature_scaleMetric_BD [FiniteDimensional ℝ E] (c : ℝ) (hc : 0 < c)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : ℝ → M) (t : ℝ) :
    riemannianCurveCurvature (scaleMetric c hc g) γ t = c⁻¹ • riemannianCurveCurvature g γ t := by
  have hT : riemannianCurveUnitTangent (scaleMetric c hc g) γ =
      fun s => (Real.sqrt c)⁻¹ • riemannianCurveUnitTangent g γ s := by
    funext s
    unfold riemannianCurveUnitTangent
    rw [riemannianCurveSpeed_scaleMetric_BD, mul_inv, mul_smul]
  unfold riemannianCurveCurvature
  rw [hT, covDerivAlong_smul, covDerivAlong_scale, riemannianCurveSpeed_scaleMetric_BD,
    smul_smul, smul_smul]
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have h2 : Real.sqrt c * Real.sqrt c = c := Real.mul_self_sqrt hc.le
  have h3 : (Real.sqrt c * riemannianCurveSpeed g γ t)⁻¹ * (Real.sqrt c)⁻¹ =
      c⁻¹ * (riemannianCurveSpeed g γ t)⁻¹ := by
    rw [mul_inv, mul_comm (Real.sqrt c)⁻¹, mul_assoc, ← mul_inv, h2, mul_comm]
  rw [h3]

/-- 曲率向量的 `g`-范数随度量缩放：`|κ_{c g}|_{c g} = c^{-1/2} |κ_g|_g`。 -/
theorem sqrt_curvature_scaleMetric_BD [FiniteDimensional ℝ E] (c : ℝ) (hc : 0 < c)
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) (γ : ℝ → M) (t : ℝ) :
    Real.sqrt ((scaleMetric c hc g).inner (γ t) (riemannianCurveCurvature (scaleMetric c hc g) γ t)
      (riemannianCurveCurvature (scaleMetric c hc g) γ t)) =
      (Real.sqrt c)⁻¹ * Real.sqrt (g.inner (γ t) (riemannianCurveCurvature g γ t)
        (riemannianCurveCurvature g γ t)) := by
  rw [sqrt_scaleMetric_inner_BD, riemannianCurveCurvature_scaleMetric_BD]
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  generalize riemannianCurveCurvature g γ t = κ
  have h1 : g.inner (γ t) (c⁻¹ • κ) (c⁻¹ • κ) = (c⁻¹) ^ 2 * g.inner (γ t) κ κ := by
    simp only [map_smul, smul_apply, smul_eq_mul]
    ring
  rw [h1, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (inv_nonneg.mpr hc.le)]
  have h2 : Real.sqrt c * c⁻¹ = (Real.sqrt c)⁻¹ := by
    have := Real.mul_self_sqrt hc.le
    field_simp
    nlinarith [this]
  rw [← mul_assoc, h2]

/-- **曲率向量范数 ≤ 加速度范数 / 速度²**（`κ ⟂ γ'`，`⟨κ, N⟩ = ⟨Dγ', N⟩/σ²`，取 `N = κ`）。 -/
theorem sqrt_curvature_le_acceleration_BD [FiniteDimensional ℝ E]
    (g : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hi : ∀ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1 ≠ 0) (t : ℝ) :
    Real.sqrt (g.inner (γ t) (riemannianCurveCurvature g γ t)
        (riemannianCurveCurvature g γ t)) ≤
      Real.sqrt (g.inner (γ t)
        (covDerivAlong g γ (fun s => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ s 1) t)
        (covDerivAlong g γ (fun s => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ s 1) t)) /
        riemannianCurveSpeed g γ t ^ 2 := by
  have hs : 0 < riemannianCurveSpeed g γ t := riemannianCurveSpeed_pos g (hi t)
  set κ := riemannianCurveCurvature g γ t with hκ
  set A := covDerivAlong g γ (fun s => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ s 1) t with hA
  have hT : riemannianCurveUnitTangent g γ t =
      (riemannianCurveSpeed g γ t)⁻¹ • mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1 := rfl
  have hort := riemannianCurveCurvature_orthogonal g hγ hi t
  rw [hT] at hort
  have hort' : g.inner (γ t) κ (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1) = 0 := by
    rw [(g.inner (γ t) _).map_smul, smul_eq_mul] at hort
    rcases mul_eq_zero.mp hort with h | h
    · exact absurd (inv_eq_zero.mp h) hs.ne'
    · exact h
  have hnorm := riemannianCurveCurvature_inner_normal g hγ (hi t) κ
    ((g.symm _ _ _).trans hort')
  have hq : 0 ≤ g.inner (γ t) κ κ := metric_inner_self_nonneg _ _ _
  have ha : 0 ≤ g.inner (γ t) A A := metric_inner_self_nonneg _ _ _
  have hCS := SmoothRiemannianMetric.metric_inner_cauchy_schwarz_sq g (γ t) A κ
  rw [eq_div_iff (pow_pos hs 2).ne'] at hnorm
  rw [le_div_iff₀ (pow_pos hs 2)]
  rcases eq_or_lt_of_le hq with h0 | hpos
  · rw [← h0, Real.sqrt_zero, zero_mul]
    exact Real.sqrt_nonneg _
  · have hkey : g.inner (γ t) κ κ * riemannianCurveSpeed g γ t ^ 4 ≤ g.inner (γ t) A A := by
      have hAκ : g.inner (γ t) A κ = g.inner (γ t) κ κ * riemannianCurveSpeed g γ t ^ 2 :=
        hnorm.symm
      have h1 : (g.inner (γ t) A κ) ^ 2 =
          (g.inner (γ t) κ κ * riemannianCurveSpeed g γ t ^ 2) ^ 2 := by rw [hAκ]
      rw [h1] at hCS
      have h2 : g.inner (γ t) κ κ * (g.inner (γ t) κ κ * riemannianCurveSpeed g γ t ^ 4) ≤
          g.inner (γ t) κ κ * g.inner (γ t) A A := by nlinarith [hCS]
      exact le_of_mul_le_mul_left h2 hpos
    have h3 : Real.sqrt (g.inner (γ t) κ κ) * riemannianCurveSpeed g γ t ^ 2 ≤
        Real.sqrt (g.inner (γ t) A A) := by
      rw [← Real.sqrt_sq (sq_nonneg (riemannianCurveSpeed g γ t) |>.trans_eq' rfl |> fun h => h),
        ← Real.sqrt_mul hq]
      exact Real.sqrt_le_sqrt (by nlinarith [hkey])
    exact h3

/-- **曲率扰动 kernel（显式参数形式）**：`g` 为参考度量，`ĝ` 为被估计度量，二者都是 `M` 上的光滑度量。
若 `ĝ ≤ Λ g`（`γ t` 处），`ĝ → g` 的 connection difference 有界 `A`，`|γ'|_g ≤ V`，
`|D^g γ'|_g ≤ W`，则 `|κ_ĝ(γ)|_ĝ ≤ √Λ (W + A V²) / σ̂²`（`σ̂ = ĝ`-speed）。
证明：`sqrt_curvature_le_acceleration_BD` + `covDerivAlong_norm_le_of_connection_bound`。 -/
theorem sqrt_curvature_perturbation_BD [FiniteDimensional ℝ E] [T2Space M]
    [BoundarylessManifold 𝓘(ℝ, E) M] (g ĝ : SmoothRiemannianMetric 𝓘(ℝ, E) M) {γ : ℝ → M}
    (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hi : ∀ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1 ≠ 0) (t : ℝ) {Λ A V W : ℝ} (hΛ : 0 ≤ Λ)
    (hA : 0 ≤ A)
    (hmetric : ∀ z : TangentSpace 𝓘(ℝ, E) (γ t), ĝ.inner (γ t) z z ≤ Λ * g.inner (γ t) z z)
    (hconnection : ∀ u w : TangentSpace 𝓘(ℝ, E) (γ t),
      Real.sqrt (g.inner (γ t)
        (CovariantDerivative.difference (metricCov ĝ) (metricCov g) (γ t) u w)
        (CovariantDerivative.difference (metricCov ĝ) (metricCov g) (γ t) u w)) ≤
        A * Real.sqrt (g.inner (γ t) u u) * Real.sqrt (g.inner (γ t) w w))
    (hvelocity : Real.sqrt (g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1)) ≤ V)
    (hderivative : Real.sqrt (g.inner (γ t)
      (covDerivAlong g γ (fun s => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ s 1) t)
      (covDerivAlong g γ (fun s => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ s 1) t)) ≤ W) :
    Real.sqrt (ĝ.inner (γ t) (riemannianCurveCurvature ĝ γ t) (riemannianCurveCurvature ĝ γ t)) ≤
      Real.sqrt Λ * (W + A * V * V) / riemannianCurveSpeed ĝ γ t ^ 2 := by
  have hγd : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t := (hγ t).mdifferentiableAt (by simp)
  have hacc := covDerivAlong_norm_le_of_connection_bound g ĝ γ
    (fun s => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ s 1) t hγd hΛ hA hmetric hconnection hvelocity
    hvelocity hderivative
  refine (sqrt_curvature_le_acceleration_BD ĝ hγ hi t).trans ?_
  have hs := riemannianCurveSpeed_pos ĝ (hi t)
  exact div_le_div_of_nonneg_right hacc (pow_pos hs 2).le

/-- **consumer（缩放 + 扰动）**：`g(t) = c · ĝ` 的曲率向量范数 `≤ c^{-1/2} · √Λ (W + A V²) / σ̂²`
（`σ̂` 为 `ĝ`-speed）。IMS04 里 `c = t`、`ĝ = t⁻¹ f_t^* g(t)`。 -/
theorem sqrt_curvature_scaled_perturbation_BD [FiniteDimensional ℝ E] [T2Space M]
    [BoundarylessManifold 𝓘(ℝ, E) M] (c : ℝ) (hc : 0 < c) (g ĝ : SmoothRiemannianMetric 𝓘(ℝ, E) M)
    {γ : ℝ → M} (hγ : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, E) ∞ γ)
    (hi : ∀ t, mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1 ≠ 0) (t : ℝ) {Λ A V W : ℝ} (hΛ : 0 ≤ Λ)
    (hA : 0 ≤ A)
    (hmetric : ∀ z : TangentSpace 𝓘(ℝ, E) (γ t), ĝ.inner (γ t) z z ≤ Λ * g.inner (γ t) z z)
    (hconnection : ∀ u w : TangentSpace 𝓘(ℝ, E) (γ t),
      Real.sqrt (g.inner (γ t)
        (CovariantDerivative.difference (metricCov ĝ) (metricCov g) (γ t) u w)
        (CovariantDerivative.difference (metricCov ĝ) (metricCov g) (γ t) u w)) ≤
        A * Real.sqrt (g.inner (γ t) u u) * Real.sqrt (g.inner (γ t) w w))
    (hvelocity : Real.sqrt (g.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1)
      (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ t 1)) ≤ V)
    (hderivative : Real.sqrt (g.inner (γ t)
      (covDerivAlong g γ (fun s => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ s 1) t)
      (covDerivAlong g γ (fun s => mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, E) γ s 1) t)) ≤ W) :
    Real.sqrt ((scaleMetric c hc ĝ).inner (γ t)
      (riemannianCurveCurvature (scaleMetric c hc ĝ) γ t)
      (riemannianCurveCurvature (scaleMetric c hc ĝ) γ t)) ≤
      (Real.sqrt c)⁻¹ * (Real.sqrt Λ * (W + A * V * V) / riemannianCurveSpeed ĝ γ t ^ 2) := by
  rw [sqrt_curvature_scaleMetric_BD]
  exact mul_le_mul_of_nonneg_left
    (sqrt_curvature_perturbation_BD g ĝ hγ hi t hΛ hA hmetric hconnection hvelocity hderivative)
    (inv_nonneg.mpr (Real.sqrt_nonneg _))

end GC.LongTime
