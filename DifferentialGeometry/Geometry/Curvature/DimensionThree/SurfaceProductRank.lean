import DifferentialGeometry.Geometry.Curvature.Product
import DifferentialGeometry.Geometry.Curvature.DimensionOne.Flat
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureNullityRank
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRankNaturality
import DifferentialGeometry.Geometry.Metric.Pullback.Euclidean

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

set_option backward.isDefEq.respectTransparency false in
theorem curvatureOperatorImageAt_finrank_prod_real
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 2)
    (x : M × ℝ) :
    Module.finrank ℝ (curvatureOperatorImageAt (g.prod (euclideanMetric (E := ℝ))) x
      ⟨metricRm04At (g.prod (euclideanMetric (E := ℝ))) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (g.prod (euclideanMetric (E := ℝ))) x⟩) =
      if metricScalarAt g x.1 = 0 then 0 else 1 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  have hdim3 : Module.finrank ℝ (E × ℝ) = 3 := by
    rw [Module.finrank_prod, hdim]
    norm_num
  have hunit : (g.prod (euclideanMetric (E := ℝ))).inner x
      (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) x from (0, 1)) (0, 1) = 1 := by
    rw [SmoothRiemannianMetric.prod_inner_mfderiv]
    simp only [mfderiv_fst, mfderiv_snd]
    change g.inner x.1 0 0 + (1 : ℝ) * 1 = 1
    rw [map_zero]
    norm_num
  rw [curvatureOperatorImageAt_finrank_eq_of_unit_curvature_nullity _ x hdim3
    (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) x from (0, 1))
    (productReal_vertical_mem_curvatureOperatorImageAnnihilatorAt g x 1) hunit]
  have heuc : metricScalarAt (euclideanMetric (E := ℝ)) x.2 = 0 :=
    metricScalarAt_eq_zero_of_finrank_le_one (euclideanMetric (E := ℝ)) (by simp) x.2
  rw [metricScalarAt_productMetric, heuc, add_zero]


theorem curvatureOperatorImageAt_finrank_prod_real_le_one
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 2)
    (x : M × ℝ) :
    Module.finrank ℝ (curvatureOperatorImageAt (g.prod (euclideanMetric (E := ℝ))) x
      ⟨metricRm04At (g.prod (euclideanMetric (E := ℝ))) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (g.prod (euclideanMetric (E := ℝ))) x⟩) ≤ 1 := by
  rw [curvatureOperatorImageAt_finrank_prod_real g hdim x]
  split <;> omega

theorem curvatureOperatorImageAt_finrank_prod_real_eq_one_of_scalar_ne_zero
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 2)
    (x : M × ℝ) (hscalar : metricScalarAt g x.1 ≠ 0) :
    Module.finrank ℝ (curvatureOperatorImageAt (g.prod (euclideanMetric (E := ℝ))) x
      ⟨metricRm04At (g.prod (euclideanMetric (E := ℝ))) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (g.prod (euclideanMetric (E := ℝ))) x⟩) = 1 := by
  rw [curvatureOperatorImageAt_finrank_prod_real g hdim x, ite_eq_right hscalar]

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold J ∞ N] [T2Space N]

theorem curvatureOperatorImageAt_finrank_pullback_prod_real
    (g : SmoothRiemannianMetric J N)
    (Φ : M ≃ₘ⟮I, J.prod 𝓘(ℝ, ℝ)⟯ (N × ℝ))
    (hdim : Module.finrank ℝ F = 2) (x : M) :
    Module.finrank ℝ (curvatureOperatorImageAt
      (Diffeomorph.pullbackMetricCross (g.prod (euclideanMetric (E := ℝ))) Φ) x
      ⟨metricRm04At
          (Diffeomorph.pullbackMetricCross (g.prod (euclideanMetric (E := ℝ))) Φ) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (Diffeomorph.pullbackMetricCross (g.prod (euclideanMetric (E := ℝ))) Φ) x⟩) =
      if metricScalarAt g (Φ x).1 = 0 then 0 else 1 := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : CompleteSpace F := FiniteDimensional.complete ℝ F
  have hdimprod : Module.finrank ℝ (TangentSpace (J.prod 𝓘(ℝ, ℝ)) (Φ x)) = 3 := by
    change Module.finrank ℝ (F × ℝ) = 3
    rw [Module.finrank_prod, hdim]
    norm_num
  have hdimM : Module.finrank ℝ (TangentSpace I x) = 3 :=
    (Φ.mfderivToContinuousLinearEquiv (by simp) x).toLinearEquiv.finrank_eq.trans hdimprod
  rw [← metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank _ x hdimM,
    Diffeomorph.pullbackMetricCross_eq_localPullMetric,
    metricCurvatureOperatorRankAt_localPull
      (g.prod (euclideanMetric (E := ℝ))) Φ Φ.isLocalDiffeomorph x hdimM hdimprod,
    metricCurvatureOperatorRankAt_eq_curvatureOperatorImageAt_finrank]
  exact curvatureOperatorImageAt_finrank_prod_real g hdim (Φ x)


theorem curvatureOperatorImageAt_finrank_pullback_prod_real_le_one
    (g : SmoothRiemannianMetric J N)
    (Φ : M ≃ₘ⟮I, J.prod 𝓘(ℝ, ℝ)⟯ (N × ℝ))
    (hdim : Module.finrank ℝ F = 2) (x : M) :
    Module.finrank ℝ (curvatureOperatorImageAt
      (Diffeomorph.pullbackMetricCross (g.prod (euclideanMetric (E := ℝ))) Φ) x
      ⟨metricRm04At
          (Diffeomorph.pullbackMetricCross (g.prod (euclideanMetric (E := ℝ))) Φ) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (Diffeomorph.pullbackMetricCross (g.prod (euclideanMetric (E := ℝ))) Φ) x⟩) ≤ 1 := by
  rw [curvatureOperatorImageAt_finrank_pullback_prod_real g Φ hdim x]
  split <;> omega

theorem curvatureOperatorImageAt_finrank_pullback_prod_real_eq_one_of_scalar_ne_zero
    (g : SmoothRiemannianMetric J N)
    (Φ : M ≃ₘ⟮I, J.prod 𝓘(ℝ, ℝ)⟯ (N × ℝ))
    (hdim : Module.finrank ℝ F = 2) (x : M)
    (hscalar : metricScalarAt g (Φ x).1 ≠ 0) :
    Module.finrank ℝ (curvatureOperatorImageAt
      (Diffeomorph.pullbackMetricCross (g.prod (euclideanMetric (E := ℝ))) Φ) x
      ⟨metricRm04At
          (Diffeomorph.pullbackMetricCross (g.prod (euclideanMetric (E := ℝ))) Φ) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (Diffeomorph.pullbackMetricCross (g.prod (euclideanMetric (E := ℝ))) Φ) x⟩) = 1 := by
  rw [curvatureOperatorImageAt_finrank_pullback_prod_real g Φ hdim x, ite_eq_right hscalar]

end DifferentialGeometry.Geometry.Curvature.DimensionThree

end

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem curvatureOperatorImageAt_finrank_prod_scaled_real_le_one
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 2)
    {ρ : ℝ} (hρ : 0 < ρ) (x : M × ℝ) :
    Module.finrank ℝ (curvatureOperatorImageAt
      (g.prod (scaleMetric ρ hρ (euclideanMetric (E := ℝ)))) x
      ⟨metricRm04At (g.prod (scaleMetric ρ hρ (euclideanMetric (E := ℝ)))) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (g.prod (scaleMetric ρ hρ (euclideanMetric (E := ℝ)))) x⟩) ≤ 1 := by
  have hsqrt : Real.sqrt ρ ≠ 0 := (Real.sqrt_pos.mpr hρ).ne'
  let ψ : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ ℝ :=
    (LinearEquiv.smulOfNeZero ℝ ℝ (Real.sqrt ρ) hsqrt).toContinuousLinearEquiv.toDiffeomorph
  let Φ : (M × ℝ) ≃ₘ⟮I.prod 𝓘(ℝ, ℝ), I.prod 𝓘(ℝ, ℝ)⟯ (M × ℝ) :=
    (Diffeomorph.refl I M ∞).prodCongr ψ
  have hΦ : Diffeomorph.pullbackMetricCross
      (g.prod (euclideanMetric (E := ℝ))) Φ =
      g.prod (scaleMetric ρ hρ (euclideanMetric (E := ℝ))) := by
    rw [Diffeomorph.pullbackMetricCross_eq_pullbackMetric]
    simpa only [Φ, ψ, Real.sq_sqrt hρ.le] using
      Diffeomorph.pullbackMetric_prod_euclidean_smul (E := ℝ) g (Real.sqrt ρ) hsqrt
  rw [← hΦ]
  exact curvatureOperatorImageAt_finrank_pullback_prod_real_le_one g Φ hdim x

end DifferentialGeometry.Geometry.Curvature.DimensionThree
