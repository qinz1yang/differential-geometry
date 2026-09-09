import DifferentialGeometry.Geometry.Curvature.Product
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureNullityRank
import DifferentialGeometry.Geometry.Curvature.DimensionThree.CurvatureOperatorRankNaturality

noncomputable section

namespace DifferentialGeometry.Geometry.Curvature.DimensionThree

open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M]

theorem curvatureOperatorImageAt_finrank_prod_real_le_one
    [I.Boundaryless]
    (g : SmoothRiemannianMetric I M) (hdim : Module.finrank ℝ E = 2)
    (x : M × ℝ) :
    Module.finrank ℝ (curvatureOperatorImageAt (g.prod (euclideanMetric (E := ℝ))) x
      ⟨metricRm04At (g.prod (euclideanMetric (E := ℝ))) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (g.prod (euclideanMetric (E := ℝ))) x⟩) ≤ 1 := by
  have hdim3 : Module.finrank ℝ (E × ℝ) = 3 := by
    rw [Module.finrank_prod, hdim]
    norm_num
  have hunit : (g.prod (euclideanMetric (E := ℝ))).inner x
      (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) x from (0, 1)) (0, 1) = 1 := by
    have h := prod_inner_verticalAt_verticalAt g (euclideanMetric (E := ℝ))
      (x := x.1) (y := x.2) (1 : ℝ) (1 : ℝ)
    change (g.prod (euclideanMetric (E := ℝ))).inner x (0, 1) (0, 1) = _ at h
    apply h.trans
    change (1 : ℝ) * 1 = 1
    norm_num
  rw [curvatureOperatorImageAt_finrank_eq_of_unit_curvature_nullity _ x hdim3
    (show TangentSpace (I.prod 𝓘(ℝ, ℝ)) x from (0, 1))
    (prod_real_vertical_mem_curvatureOperatorImageAnnihilatorAt g x 1) hunit]
  split <;> omega

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
  [FiniteDimensional ℝ F]
  {G : Type*} [TopologicalSpace G] {J : ModelWithCorners ℝ F G} [J.Boundaryless]
  {N : Type*} [TopologicalSpace N] [ChartedSpace G N]
  [IsManifold J ∞ N] [T2Space N]

theorem curvatureOperatorImageAt_finrank_pullback_prod_real_le_one
    [SigmaCompactSpace M]
    (g : SmoothRiemannianMetric J N)
    (Φ : M ≃ₘ⟮I, J.prod 𝓘(ℝ, ℝ)⟯ (N × ℝ))
    (hdim : Module.finrank ℝ F = 2) (x : M) :
    Module.finrank ℝ (curvatureOperatorImageAt
      (Diffeomorph.pullbackMetricCross (g.prod (euclideanMetric (E := ℝ))) Φ) x
      ⟨metricRm04At
          (Diffeomorph.pullbackMetricCross (g.prod (euclideanMetric (E := ℝ))) Φ) x,
        metricRm04At_mem_algebraicCurvatureTensorSubmodule
          (Diffeomorph.pullbackMetricCross (g.prod (euclideanMetric (E := ℝ))) Φ) x⟩) ≤ 1 := by
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
  exact curvatureOperatorImageAt_finrank_prod_real_le_one g hdim (Φ x)

end DifferentialGeometry.Geometry.Curvature.DimensionThree
