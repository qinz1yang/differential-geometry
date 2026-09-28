import DifferentialGeometry.Geometry.Flow.RicciFlow.Uniqueness.Forward.Measure.DensityRegularity

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow

open DifferentialGeometry.TensorMetric
  (metricDiffAt metricDiffAt_apply metricDiffSq metricDiffSq_def)

open MeasureTheory Set DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Integral.Measure
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M]

theorem metric_eq_of_weighted_energy_zero
    (g₁ g₂ : ℝ → SmoothRiemannianMetric I M) {t : ℝ} (η : M → ℝ)
    (hη : ∀ᵐ x ∂riemannianMeasureFamily (I := I) g₁ t, η x ≠ 0)
    (hden : Integrable (fun x => η x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x)
      (riemannianMeasureFamily (I := I) g₁ t))
    (hE : (∫ x, η x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x
      ∂riemannianMeasureFamily (I := I) g₁ t) = 0) :
    g₁ t = g₂ t := by
  have hprod : (fun x => η x ^ 2 * forwardUniqueDensity (I := I) g₁ g₂ t x)
      =ᵐ[riemannianMeasureFamily (I := I) g₁ t] 0 :=
    (integral_eq_zero_iff_of_nonneg
      (fun x => mul_nonneg (sq_nonneg _) (density_nonneg (I := I) g₁ g₂ t x)) hden).mp hE
  have hz : (fun x => forwardUniqueDensity (I := I) g₁ g₂ t x)
      =ᵐ[riemannianMeasureFamily (I := I) g₁ t] 0 := by
    filter_upwards [hprod, hη] with x hx hnx
    exact (mul_eq_zero.mp hx).resolve_left (pow_ne_zero 2 hnx)
  have hmnn (x : M) : 0 ≤ metricDiffSq (I := I) (g₁ t) (g₂ t) x := by
    rw [metricDiffSq_def]
    exact normSq0S_nonneg (g₁ t) x 2 _
  have hm : (fun x => metricDiffSq (I := I) (g₁ t) (g₂ t) x)
      =ᵐ[riemannianMeasureFamily (I := I) g₁ t] 0 := by
    filter_upwards [hz] with x hx
    exact le_antisymm ((metricDiffSq_le_dens g₁ g₂ t x).trans_eq hx) (hmnn x)
  have hcont : Continuous (fun x => metricDiffSq (I := I) (g₁ t) (g₂ t) x) :=
    normSq0S_continuous (g₁ t) (metricTensorField (g₁ t) - metricTensorField (g₂ t))
  have : (riemannianMeasureFamily (I := I) g₁ t).IsOpenPosMeasure := by
    rw [riemannianMeasureFamily_def]
    exact riemannianVolumeMeasure_isOpenPosMeasure (g₁ t)
  have heq : (fun x => metricDiffSq (I := I) (g₁ t) (g₂ t) x) = 0 :=
    (Continuous.ae_eq_iff_eq (riemannianMeasureFamily (I := I) g₁ t)
      hcont continuous_const).mp hm
  have hmetric_ext : ∀ {g g' : SmoothRiemannianMetric I M},
      (∀ (x : M) (v w : TangentSpace I x), g.inner x v w = g'.inner x v w) → g = g' := by
    intro g g' h
    obtain ⟨i₁, s₁, p₁, b₁, c₁⟩ := g
    obtain ⟨i₂, s₂, p₂, b₂, c₂⟩ := g'
    have hi : i₁ = i₂ :=
      funext fun x => ContinuousLinearMap.ext fun v => ContinuousLinearMap.ext fun w => h x v w
    subst hi
    rfl
  apply hmetric_ext
  intro x X Y
  have hx : normSq0S (I := I) (g₁ t) x 2
      (metricDiffAt (I := I) (g₁ t) (g₂ t) x) = 0 := congrFun heq x
  have h0 := (normSq0S_eq_zero_iff (g₁ t) x 2 _).mp hx
  have hval := congrArg (fun A : Tensor0SSpace 2 I x =>
    A (fun i : Fin 2 => if i = 0 then X else Y)) h0
  simp only [metricDiffAt_apply, Tensor0SSpace.zero_apply] at hval
  norm_num at hval
  linarith [hval]

end DifferentialGeometry.PDE.RicciFlow
