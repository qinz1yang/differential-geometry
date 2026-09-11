import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.Classification
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

namespace DifferentialGeometry.Geometry

open Curvature Curvature.DimensionThree

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

theorem gradientRicciSoliton_classification_with_scaling_and_orientation
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯} {sigma : ℝ}
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    (hsigma : 0 < sigma)
    (hdim : Module.finrank ℝ E = 3) :
    ∃! C : ℝ,
      (∀ x : M, Curvature.metricScalarAt g x +
        Operator.normGradSqFun g f x - sigma * f x = C) ∧
      let gnorm := scaleMetric (I := I) sigma hsigma g
      let fnorm := f + ContMDiffMap.const (I := I)
        (I' := modelWithCornersSelf ℝ ℝ) (M := M) (n := ∞) (C / sigma)
      normalizedGradientRicciSoliton (I := I) gnorm fnorm ∧
    let gaussian := ∃ e : M ≃ₘ⟮I, 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))⟯ EuclideanSpace ℝ (Fin 3),
      Diffeomorph.pullbackMetricCross (euclideanMetric (E := EuclideanSpace ℝ (Fin 3))) e = gnorm ∧
      fnorm = gaussianPotential.comp e.toContMDiffMap
    let sphere := ∃ cover : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → M,
      ∃ hcover : solitonModelCovering roundThreeSphereShrinkerMetric roundThreeSphereShrinkerPotential
        gnorm fnorm cover,
      localPullMetric g cover (solitonModelCovering_isLocalDiffeomorph hcover) =
        scaleMetric ((2 / Real.sqrt sigma) ^ 2)
          (sq_pos_of_pos (div_pos (by norm_num) (Real.sqrt_pos.mpr hsigma)))
          (roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3)) ∧
      ∃ G : Subgroup (Equiv.Perm (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)),
      ∃ (_ : Finite G)
        (_ : IsCancelSMul G (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
        (_ : ContinuousConstSMul G (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
        (_ : ContMDiffConstSMul (𝓡 3) ∞ G (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)),
      ∃ hmetric : ∀ gamma : G, Diffeomorph.pullbackMetric roundThreeSphereShrinkerMetric
          (MulAction.smulDiffeomorph (n := ∞) (𝓡 3) gamma) = roundThreeSphereShrinkerMetric,
      ∃ e : MulAction.orbitRel.Quotient G
          (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ≃ₘ⟮𝓡 3, I⟯ M,
        Diffeomorph.pullbackMetricCross gnorm e =
          solitonModelQuotientMetric roundThreeSphereShrinkerMetric hmetric ∧
        (∀ x : M, fnorm x = (3 / 2 : ℝ))
    let cylinder := ∃ cover : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) → M,
      ∃ hcover : solitonModelCovering roundThreeCylinderShrinkerMetric roundThreeCylinderShrinkerPotential
        gnorm fnorm cover,
      ((∃ Ω : DifferentialForm I M 3, ∀ x, Ω x ≠ 0) ↔
        coveringDeckGroup cover ≠ cylinderAntipodalGroup) ∧
      localPullMetric g (cover ∘ ((Diffeomorph.refl (𝓡 2)
          (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞).prodCongr
          (LinearEquiv.smulOfNeZero ℝ ℝ (Real.sqrt sigma)
            (Real.sqrt_pos.mpr hsigma).ne').toContinuousLinearEquiv.toDiffeomorph))
        (isLocalDiffeomorph_comp (solitonModelCovering_isLocalDiffeomorph hcover)
          ((Diffeomorph.refl (𝓡 2) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞).prodCongr
            (LinearEquiv.smulOfNeZero ℝ ℝ (Real.sqrt sigma)
              (Real.sqrt_pos.mpr hsigma).ne').toContinuousLinearEquiv.toDiffeomorph).isLocalDiffeomorph) =
        (scaleMetric ((Real.sqrt (2 / sigma)) ^ 2) (sq_pos_of_pos (by positivity))
          (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2))).prod
          (euclideanMetric (E := ℝ)) ∧
      (∀ x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ,
        f (cover (((Diffeomorph.refl (𝓡 2) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞).prodCongr
          (LinearEquiv.smulOfNeZero ℝ ℝ (Real.sqrt sigma)
            (Real.sqrt_pos.mpr hsigma).ne').toContinuousLinearEquiv.toDiffeomorph) x)) + C / sigma =
          1 + sigma * x.2 ^ 2 / 4) ∧
      ((coveringDeckGroup cover = ⊥ ∧
      ∃ e : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) ≃ₘ⟮
          (𝓡 2).prod 𝓘(Real, Real), I⟯ M,
        (∀ x, e x = cover x) ∧
        Diffeomorph.pullbackMetricCross gnorm e = roundThreeCylinderShrinkerMetric ∧
        ∀ x, fnorm (e x) = 1 + x.2 ^ 2 / 4) ∨
    (coveringDeckGroup cover = cylinderAntipodalGroup ∧
      ∃ e : (RealProjectivePlane × Real) ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), I⟯ M,
        (∀ x, e (realProjectivePlaneQuotientMap x.1, x.2) = cover x) ∧
        Diffeomorph.pullbackMetricCross gnorm e =
          (scaleMetric 2 (by norm_num)
            (roundProjectiveMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))).prod
              (euclideanMetric (E := Real)) ∧
        ∀ x, fnorm (e x) = 1 + x.2 ^ 2 / 4) ∨
    (coveringDeckGroup cover = cylinderDiagonalGroup ∧
      ∃ e : PuncturedRealProjectiveThreeSpace ≃ₘ⟮𝓡 3, I⟯ M,
        (∀ x, e (cylinderDiagonalQuotientDiffeomorph
          (cylinderDiagonalQuotientMap x)) = cover x) ∧
        Diffeomorph.pullbackMetricCross gnorm
          (cylinderDiagonalQuotientDiffeomorph.trans e) = cylinderDiagonalQuotientMetric ∧
        ∀ x, fnorm (e (cylinderDiagonalQuotientDiffeomorph x)) =
          cylinderDiagonalQuotientPotential x))
    (gaussian ∧ ¬ sphere ∧ ¬ cylinder) ∨
      (sphere ∧ ¬ gaussian ∧ ¬ cylinder) ∨
      (cylinder ∧ ¬ gaussian ∧ ¬ sphere) := by
  obtain ⟨C, ⟨hC, hn⟩, hu⟩ := gradientRicciSoliton_existsUnique_normalized hcomplete hsol hsigma
  refine ⟨C, ⟨hC, hn, ?_⟩, ?_⟩
  · let gnorm := scaleMetric (I := I) sigma hsigma g
    let fnorm := f + ContMDiffMap.const (I := I)
      (I' := modelWithCornersSelf ℝ ℝ) (M := M) (n := ∞) (C / sigma)
    intro gaussian sphere cylinder
    have hgiff : (∃ cover : EuclideanSpace ℝ (Fin 3) → M,
        solitonModelCovering (euclideanMetric (E := EuclideanSpace ℝ (Fin 3)))
          (gaussianPotential (E := EuclideanSpace ℝ (Fin 3))) gnorm fnorm cover) ↔ gaussian :=
      exists_solitonModelCovering_gaussian_iff
    have hsiff : (∃ cover : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → M,
        solitonModelCovering roundThreeSphereShrinkerMetric roundThreeSphereShrinkerPotential
          gnorm fnorm cover) ↔ sphere := by
      constructor
      · rintro ⟨cover, hcover⟩
        exact ⟨cover, hcover, solitonModelCovering_roundThreeSphere_unscaled_metric hsigma hcover,
          (exists_solitonModelCovering_roundThreeSphere_iff hn).mp ⟨cover, hcover⟩⟩
      · rintro ⟨cover, hcover, _⟩
        exact ⟨cover, hcover⟩
    have hciff : (∃ cover : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ → M,
        solitonModelCovering roundThreeCylinderShrinkerMetric roundThreeCylinderShrinkerPotential
          gnorm fnorm cover) ↔ cylinder := by
      constructor
      · rintro ⟨cover, hcover⟩
        exact ⟨cover, hcover,
          solitonModelCovering_roundThreeCylinder_exists_nonvanishing_top_form_iff hcover,
          solitonModelCovering_roundThreeCylinder_unscaled_metric hsigma hcover,
          solitonModelCovering_roundThreeCylinder_unscaled_potential hsigma hcover,
          solitonModelCovering_roundThreeCylinder_target_isometry_trichotomy hcover⟩
      · rintro ⟨cover, hcover, _⟩
        exact ⟨cover, hcover⟩
    rcases normalizedGradientRicciSoliton_solitonModelCovering_classification hn hdim with
      ⟨hg, hs, hc⟩ | ⟨hs, hg, hc⟩ | ⟨hc, hg, hs⟩
    · exact Or.inl ⟨hgiff.mp hg, fun hh => hs (hsiff.mpr hh), fun hh => hc (hciff.mpr hh)⟩
    · exact Or.inr (Or.inl ⟨hsiff.mp hs, fun hh => hg (hgiff.mpr hh), fun hh => hc (hciff.mpr hh)⟩)
    · exact Or.inr (Or.inr ⟨hciff.mp hc, fun hh => hg (hgiff.mpr hh), fun hh => hs (hsiff.mpr hh)⟩)
  · intro D hD
    exact hu D ⟨hD.1, hD.2.1⟩


end DifferentialGeometry.Geometry
