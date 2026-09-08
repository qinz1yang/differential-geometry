import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.CurvatureRankModels
import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.RankOneModelCover
import DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCoverScaling

set_option autoImplicit false
noncomputable section
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry

private instance euclideanFourFinrankFact :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
private instance euclideanThreeFinrankFact :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

section Classification

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

open Curvature Curvature.DimensionThree
theorem gradientRicciSoliton_exists_roundThreeSphere_solitonModelCovering_of_rank_three
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯} {sigma : ℝ}
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    (hsigma : 0 < sigma)
    (hdim : Module.finrank ℝ E = 3)
    {x₀ : M} (hrank : metricCurvatureOperatorRankAt g x₀ hdim = 3) :
    ∃! C : ℝ,
      (∀ x : M, metricScalarAt (I := I) g x +
        Operator.normGradSqFun (I := I) g f x - sigma * f x = C) ∧
      let gnorm := scaleMetric (I := I) sigma hsigma g
      let fnorm := f + ContMDiffMap.const (I := I)
        (I' := modelWithCornersSelf ℝ ℝ) (M := M) (n := ∞) (C / sigma)
      normalizedGradientRicciSoliton (I := I) gnorm fnorm ∧
      ∃ cover : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → M,
      ∃ hcover : solitonModelCovering roundThreeSphereShrinkerMetric roundThreeSphereShrinkerPotential
          gnorm fnorm cover,
    localPullMetric g cover (solitonModelCovering_isLocalDiffeomorph hcover) =
      scaleMetric ((2 / Real.sqrt sigma) ^ 2)
        (sq_pos_of_pos (div_pos (by norm_num) (Real.sqrt_pos.mpr hsigma)))
        (roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3)) := by
  obtain ⟨C, ⟨hC, hn⟩, hunique⟩ := gradientRicciSoliton_existsUnique_normalized hcomplete hsol hsigma
  have hrank' := (metricCurvatureOperatorRankAt_scaleMetric sigma hsigma g x₀ hdim).trans hrank
  obtain ⟨cover, hcover⟩ := exists_roundThreeSphere_solitonModelCovering_of_rank_three hn hdim hrank'
  refine ⟨C, ⟨hC, hn, cover, hcover, ?_⟩, ?_⟩
  · exact solitonModelCovering_roundThreeSphere_unscaled_metric hsigma hcover
  · intro D hD
    exact hunique D ⟨hD.1, hD.2.1⟩

theorem gradientRicciSoliton_exists_roundThreeCylinder_solitonModelCovering_of_rank_one
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯} {sigma : ℝ}
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    (hsigma : 0 < sigma)
    (hdim : Module.finrank ℝ E = 3)
    {x₀ : M} (hrank : metricCurvatureOperatorRankAt g x₀ hdim = 1) :
    ∃! C : ℝ,
      (∀ x : M, metricScalarAt (I := I) g x +
        Operator.normGradSqFun (I := I) g f x - sigma * f x = C) ∧
      let gnorm := scaleMetric (I := I) sigma hsigma g
      let fnorm := f + ContMDiffMap.const (I := I)
        (I' := modelWithCornersSelf ℝ ℝ) (M := M) (n := ∞) (C / sigma)
      normalizedGradientRicciSoliton (I := I) gnorm fnorm ∧
      ∃ cover : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ → M,
      ∃ hcover : solitonModelCovering roundThreeCylinderShrinkerMetric roundThreeCylinderShrinkerPotential
          gnorm fnorm cover,
    localPullMetric g (cover ∘ ((Diffeomorph.refl (𝓡 2) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞).prodCongr
        (LinearEquiv.smulOfNeZero ℝ ℝ (Real.sqrt sigma)
          (Real.sqrt_pos.mpr hsigma).ne').toContinuousLinearEquiv.toDiffeomorph))
      (isLocalDiffeomorph_comp (solitonModelCovering_isLocalDiffeomorph hcover)
        ((Diffeomorph.refl (𝓡 2) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞).prodCongr
        (LinearEquiv.smulOfNeZero ℝ ℝ (Real.sqrt sigma)
          (Real.sqrt_pos.mpr hsigma).ne').toContinuousLinearEquiv.toDiffeomorph).isLocalDiffeomorph) =
      (scaleMetric ((Real.sqrt (2 / sigma)) ^ 2)
        (sq_pos_of_pos (by positivity))
        (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))).prod
        (euclideanMetric (E := ℝ)) ∧
      ∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ,
    f (cover (((Diffeomorph.refl (𝓡 2) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞).prodCongr
        (LinearEquiv.smulOfNeZero ℝ ℝ (Real.sqrt sigma)
          (Real.sqrt_pos.mpr hsigma).ne').toContinuousLinearEquiv.toDiffeomorph) x)) + C / sigma =
      1 + sigma * x.2 ^ 2 / 4 := by
  obtain ⟨C, ⟨hC, hn⟩, hunique⟩ := gradientRicciSoliton_existsUnique_normalized hcomplete hsol hsigma
  have hrank' := (metricCurvatureOperatorRankAt_scaleMetric sigma hsigma g x₀ hdim).trans hrank
  obtain ⟨cover, hcover⟩ := exists_roundThreeCylinder_solitonModelCovering_of_rank_one hn hdim hrank'
  refine ⟨C, ⟨hC, hn, cover, hcover, ?_, ?_⟩, ?_⟩
  · exact solitonModelCovering_roundThreeCylinder_unscaled_metric hsigma hcover
  · exact solitonModelCovering_roundThreeCylinder_unscaled_potential hsigma hcover
  · intro D hD
    exact hunique D ⟨hD.1, hD.2.1⟩

end Classification


end DifferentialGeometry.Geometry
