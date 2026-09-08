import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.RankOneModelCover
import DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCoverCylinderClassification

set_option autoImplicit false

noncomputable section

open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Curvature.DimensionThree

private instance euclideanThreeFinrankFact :
    Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) := ⟨by simp⟩

variable {E : Type} [NormedAddCommGroup E] [NormedSpace Real E] [FiniteDimensional Real E]
  {H : Type} [TopologicalSpace H]
  {I : ModelWithCorners Real E H} [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

theorem normalizedGradientRicciSoliton_isometry_trichotomy_of_rank_one
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 3)
    {x₀ : M} (hrank : metricCurvatureOperatorRankAt g x₀ hdim = 1) :
    (∃ e : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) ≃ₘ⟮
        (𝓡 2).prod 𝓘(Real, Real), I⟯ M,
      Diffeomorph.pullbackMetricCross g e = roundThreeCylinderShrinkerMetric ∧
      ∀ x, f (e x) = 1 + x.2 ^ 2 / 4) ∨
    (∃ e : (RealProjectivePlane × Real) ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), I⟯ M,
      Diffeomorph.pullbackMetricCross g e =
        (scaleMetric 2 (by norm_num)
          (roundProjectiveMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))).prod
            (euclideanMetric (E := Real)) ∧
      ∀ x, f (e x) = 1 + x.2 ^ 2 / 4) ∨
    (∃ e : PuncturedRealProjectiveThreeSpace ≃ₘ⟮𝓡 3, I⟯ M,
      Diffeomorph.pullbackMetricCross g
        (cylinderDiagonalQuotientDiffeomorph.trans e) = cylinderDiagonalQuotientMetric ∧
      ∀ x, f (e (cylinderDiagonalQuotientDiffeomorph x)) =
        cylinderDiagonalQuotientPotential x) := by
  obtain ⟨cover, hcover⟩ := exists_roundThreeCylinder_solitonModelCovering_of_rank_one h hdim hrank
  rcases solitonModelCovering_roundThreeCylinder_target_isometry_trichotomy hcover with
    ⟨_, e, _, hmetric, hpotential⟩ | ⟨_, e, _, hmetric, hpotential⟩ |
      ⟨_, e, _, hmetric, hpotential⟩
  · exact Or.inl ⟨e, hmetric, hpotential⟩
  · exact Or.inr (Or.inl ⟨e, hmetric, hpotential⟩)
  · exact Or.inr (Or.inr ⟨e, hmetric, hpotential⟩)

theorem normalizedGradientRicciSoliton_isometry_dichotomy_of_rank_one_of_exists_nonvanishing_top_form
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 3)
    {x₀ : M} (hrank : metricCurvatureOperatorRankAt g x₀ hdim = 1)
    (hΩ : ∃ Ω : DifferentialForm I M 3, ∀ x, Ω x ≠ 0) :
    (∃ e : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) ≃ₘ⟮
        (𝓡 2).prod 𝓘(Real, Real), I⟯ M,
      Diffeomorph.pullbackMetricCross g e = roundThreeCylinderShrinkerMetric ∧
      ∀ x, f (e x) = 1 + x.2 ^ 2 / 4) ∨
    (∃ e : PuncturedRealProjectiveThreeSpace ≃ₘ⟮𝓡 3, I⟯ M,
      Diffeomorph.pullbackMetricCross g
        (cylinderDiagonalQuotientDiffeomorph.trans e) = cylinderDiagonalQuotientMetric ∧
      ∀ x, f (e (cylinderDiagonalQuotientDiffeomorph x)) =
        cylinderDiagonalQuotientPotential x) := by
  obtain ⟨cover, hcover⟩ := exists_roundThreeCylinder_solitonModelCovering_of_rank_one h hdim hrank
  rcases solitonModelCovering_roundThreeCylinder_target_isometry_dichotomy_of_exists_nonvanishing_top_form
      hcover hΩ with
    ⟨_, e, _, hmetric, hpotential⟩ | ⟨_, e, _, hmetric, hpotential⟩
  · exact Or.inl ⟨e, hmetric, hpotential⟩
  · exact Or.inr ⟨e, hmetric, hpotential⟩

end DifferentialGeometry.Geometry
