import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.CurvatureRankModels
import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.NonnegativeModelCovers
import DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCoverCurvatureRank
import DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCoverGaussian
import DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCoverRoundThreeSphere
import DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCoverCylinderClassification

set_option autoImplicit false

noncomputable section
open Bundle Set
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry
open Curvature Curvature.DimensionThree

private instance euclideanThreeFinrankFact :
    Fact (Module.finrank Real (EuclideanSpace Real (Fin 3)) = 2 + 1) := ⟨by simp⟩

private instance euclideanFourFinrankFact :
    Fact (Module.finrank Real (EuclideanSpace Real (Fin 4)) = 3 + 1) := ⟨by simp⟩

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M]

theorem normalizedGradientRicciSoliton_solitonModelCovering_trichotomy_of_nonnegative
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank ℝ E = 3)
    (hcone : ∀ x : M, metricAlgebraicCurvatureTensorAt g x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    (∃ cover : EuclideanSpace ℝ (Fin 3) → M,
      solitonModelCovering (euclideanMetric (E := EuclideanSpace ℝ (Fin 3)))
        (gaussianPotential (E := EuclideanSpace ℝ (Fin 3))) g f cover) ∨
    (∃ cover : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → M,
      solitonModelCovering roundThreeSphereShrinkerMetric roundThreeSphereShrinkerPotential g f cover) ∨
    (∃ cover : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) → M,
      solitonModelCovering roundThreeCylinderShrinkerMetric roundThreeCylinderShrinkerPotential g f cover) := by
  let x : M := Classical.choice (inferInstance : Nonempty M)
  rcases gradientRicciSoliton_metricCurvatureOperatorRankAt_trichotomy_of_nonnegative g f
    1 h.1 h.2.1 hdim hcone x with hzero | hone | hthree
  · exact Or.inl (exists_gaussian_solitonModelCovering_of_rank_zero h hdim hzero)
  · exact Or.inr (Or.inr (exists_roundThreeCylinder_solitonModelCovering_of_nonnegative_of_rank_one h hdim hcone hone))
  · exact Or.inr (Or.inl (exists_roundThreeSphere_solitonModelCovering_of_rank_three_of_nonnegative h hdim hthree hcone))

theorem normalizedGradientRicciSoliton_solitonModelCovering_classification_of_nonnegative
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank ℝ E = 3)
    (hcone : ∀ x : M, metricAlgebraicCurvatureTensorAt g x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    let gaussian := ∃ cover : EuclideanSpace ℝ (Fin 3) → M,
      solitonModelCovering (euclideanMetric (E := EuclideanSpace ℝ (Fin 3)))
        (gaussianPotential (E := EuclideanSpace ℝ (Fin 3))) g f cover
    let sphere := ∃ cover : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → M,
      solitonModelCovering roundThreeSphereShrinkerMetric roundThreeSphereShrinkerPotential g f cover
    let cylinder := ∃ cover : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) → M,
      solitonModelCovering roundThreeCylinderShrinkerMetric roundThreeCylinderShrinkerPotential g f cover
    (gaussian ∧ ¬ sphere ∧ ¬ cylinder) ∨
      (sphere ∧ ¬ gaussian ∧ ¬ cylinder) ∨
      (cylinder ∧ ¬ gaussian ∧ ¬ sphere) := by
  intro gaussian sphere cylinder
  have hgs : ¬ (gaussian ∧ sphere) := by
    rintro ⟨⟨_, hg⟩, ⟨_, hs⟩⟩
    exact not_solitonModelCovering_gaussian_and_roundThreeSphere hg hs
  have hgc : ¬ (gaussian ∧ cylinder) := by
    rintro ⟨⟨_, hg⟩, ⟨_, hc⟩⟩
    exact not_solitonModelCovering_gaussian_and_roundThreeCylinder hg hc
  have hsc : ¬ (sphere ∧ cylinder) := by
    rintro ⟨⟨_, hs⟩, ⟨_, hc⟩⟩
    exact not_solitonModelCovering_roundThreeSphere_and_roundThreeCylinder hs hc
  rcases normalizedGradientRicciSoliton_solitonModelCovering_trichotomy_of_nonnegative h hdim hcone with hg | hs | hc
  · exact Or.inl ⟨hg, fun hs => hgs ⟨hg, hs⟩, fun hc => hgc ⟨hg, hc⟩⟩
  · exact Or.inr (Or.inl ⟨hs, fun hg => hgs ⟨hg, hs⟩, fun hc => hsc ⟨hs, hc⟩⟩)
  · exact Or.inr (Or.inr ⟨hc, fun hg => hgc ⟨hg, hc⟩, fun hs => hsc ⟨hs, hc⟩⟩)

theorem gradientRicciSoliton_classification_of_nonnegative
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯} {sigma : ℝ}
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    (hsigma : 0 < sigma)
    (hdim : Module.finrank ℝ E = 3)
    (hcone : ∀ x : M, metricAlgebraicCurvatureTensorAt g x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    ∃! C : ℝ,
      (∀ x : M, metricScalarAt g x +
        Operator.normGradSqFun g f x - sigma * f x = C) ∧
      let gnorm := scaleMetric (I := I) sigma hsigma g
      let fnorm := f + ContMDiffMap.const (I := I)
        (I' := modelWithCornersSelf ℝ ℝ) (M := M) (n := ∞) (C / sigma)
      normalizedGradientRicciSoliton (I := I) gnorm fnorm ∧
      let gaussian := ∃ e : M ≃ₘ⟮I, 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))⟯ EuclideanSpace ℝ (Fin 3),
        Diffeomorph.pullbackMetricCross (euclideanMetric (E := EuclideanSpace ℝ (Fin 3))) e = gnorm ∧
        fnorm = gaussianPotential.comp e.toContMDiffMap
      let sphere := ∃ cover : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → M,
        solitonModelCovering roundThreeSphereShrinkerMetric roundThreeSphereShrinkerPotential
          gnorm fnorm cover
      let cylinder := ∃ cover : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) → M,
        solitonModelCovering roundThreeCylinderShrinkerMetric roundThreeCylinderShrinkerPotential
          gnorm fnorm cover
      (gaussian ∧ ¬ sphere ∧ ¬ cylinder) ∨
        (sphere ∧ ¬ gaussian ∧ ¬ cylinder) ∨
        (cylinder ∧ ¬ gaussian ∧ ¬ sphere) := by
  obtain ⟨C, ⟨hC, hn⟩, hu⟩ := gradientRicciSoliton_existsUnique_normalized hcomplete hsol hsigma
  have hcone' : ∀ x : M, metricAlgebraicCurvatureTensorAt (scaleMetric sigma hsigma g) x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M) := by
    let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
    intro x
    rw [metricAlgebraicCurvatureTensorAt_scaleMetric]
    exact algebraicCurvatureOperatorNonnegativeCone.smul_mem (hcone x) hsigma.le
  refine ⟨C, ⟨hC, hn, ?_⟩, ?_⟩
  · intro gaussian sphere cylinder
    have hgaussian : (∃ cover : EuclideanSpace ℝ (Fin 3) → M,
        solitonModelCovering (euclideanMetric (E := EuclideanSpace ℝ (Fin 3)))
          (gaussianPotential (E := EuclideanSpace ℝ (Fin 3)))
          (scaleMetric sigma hsigma g)
          (f + ContMDiffMap.const (I := I) (I' := modelWithCornersSelf ℝ ℝ)
            (M := M) (n := ∞) (C / sigma)) cover) ↔ gaussian :=
      exists_solitonModelCovering_gaussian_iff
    rcases normalizedGradientRicciSoliton_solitonModelCovering_classification_of_nonnegative
      hn hdim hcone' with ⟨hg, hs, hc⟩ | ⟨hs, hg, hc⟩ | ⟨hc, hg, hs⟩
    · exact Or.inl ⟨hgaussian.mp hg, hs, hc⟩
    · exact Or.inr (Or.inl ⟨hs, fun hg' => hg (hgaussian.mpr hg'), hc⟩)
    · exact Or.inr (Or.inr ⟨hc, fun hg' => hg (hgaussian.mpr hg'), hs⟩)
  · intro D hD
    exact hu D ⟨hD.1, hD.2.1⟩

theorem normalizedGradientRicciSoliton_isometry_classification_of_nonnegative
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank ℝ E = 3)
    (hcone : ∀ x : M, metricAlgebraicCurvatureTensorAt g x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M)) :
    let gaussian := ∃ e : M ≃ₘ⟮I, 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))⟯ EuclideanSpace ℝ (Fin 3),
      Diffeomorph.pullbackMetricCross (euclideanMetric (E := EuclideanSpace ℝ (Fin 3))) e = g ∧
      f = gaussianPotential.comp e.toContMDiffMap
    let sphere := ∃ G : Subgroup (Equiv.Perm (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)),
      ∃ (_ : Finite G)
        (_ : IsCancelSMul G (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
        (_ : ContinuousConstSMul G (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
        (_ : ContMDiffConstSMul (𝓡 3) ∞ G (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)),
      ∃ hmetric : ∀ gamma : G, Diffeomorph.pullbackMetric roundThreeSphereShrinkerMetric
          (MulAction.smulDiffeomorph (n := ∞) (𝓡 3) gamma) = roundThreeSphereShrinkerMetric,
      ∃ e : MulAction.orbitRel.Quotient G
          (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ≃ₘ⟮𝓡 3, I⟯ M,
        Diffeomorph.pullbackMetricCross g e =
          solitonModelQuotientMetric roundThreeSphereShrinkerMetric hmetric ∧
        (∀ x : M, f x = (3 / 2 : ℝ))
    let cylinder := ∃ cover : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) → M,
      solitonModelCovering roundThreeCylinderShrinkerMetric roundThreeCylinderShrinkerPotential g f cover ∧
      ((coveringDeckGroup cover = ⊥ ∧
      ∃ e : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) ≃ₘ⟮
          (𝓡 2).prod 𝓘(Real, Real), I⟯ M,
        (∀ x, e x = cover x) ∧
        Diffeomorph.pullbackMetricCross g e = roundThreeCylinderShrinkerMetric ∧
        ∀ x, f (e x) = 1 + x.2 ^ 2 / 4) ∨
    (coveringDeckGroup cover = cylinderAntipodalGroup ∧
      ∃ e : (RealProjectivePlane × Real) ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), I⟯ M,
        (∀ x, e (realProjectivePlaneQuotientMap x.1, x.2) = cover x) ∧
        Diffeomorph.pullbackMetricCross g e =
          (scaleMetric 2 (by norm_num)
            (roundProjectiveMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))).prod
              (euclideanMetric (E := Real)) ∧
        ∀ x, f (e x) = 1 + x.2 ^ 2 / 4) ∨
    (coveringDeckGroup cover = cylinderDiagonalGroup ∧
      ∃ e : PuncturedRealProjectiveThreeSpace ≃ₘ⟮𝓡 3, I⟯ M,
        (∀ x, e (cylinderDiagonalQuotientDiffeomorph
          (cylinderDiagonalQuotientMap x)) = cover x) ∧
        Diffeomorph.pullbackMetricCross g
          (cylinderDiagonalQuotientDiffeomorph.trans e) = cylinderDiagonalQuotientMetric ∧
        ∀ x, f (e (cylinderDiagonalQuotientDiffeomorph x)) =
          cylinderDiagonalQuotientPotential x))
    (gaussian ∧ ¬ sphere ∧ ¬ cylinder) ∨
      (sphere ∧ ¬ gaussian ∧ ¬ cylinder) ∨
      (cylinder ∧ ¬ gaussian ∧ ¬ sphere) := by
  intro gaussian sphere cylinder
  have hgaussian : (∃ cover : EuclideanSpace ℝ (Fin 3) → M,
      solitonModelCovering (euclideanMetric (E := EuclideanSpace ℝ (Fin 3)))
        (gaussianPotential (E := EuclideanSpace ℝ (Fin 3))) g f cover) ↔ gaussian :=
    exists_solitonModelCovering_gaussian_iff
  have hsphere : (∃ cover : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → M,
      solitonModelCovering roundThreeSphereShrinkerMetric roundThreeSphereShrinkerPotential g f cover) ↔
      sphere := exists_solitonModelCovering_roundThreeSphere_iff h
  have hcylinder : (∃ cover : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) → M,
      solitonModelCovering roundThreeCylinderShrinkerMetric roundThreeCylinderShrinkerPotential g f cover) ↔
      cylinder := by
    constructor
    · rintro ⟨cover, hcover⟩
      exact ⟨cover, hcover, solitonModelCovering_roundThreeCylinder_target_isometry_trichotomy hcover⟩
    · rintro ⟨cover, hcover, _⟩
      exact ⟨cover, hcover⟩
  rcases normalizedGradientRicciSoliton_solitonModelCovering_classification_of_nonnegative h hdim hcone with
    ⟨hg, hs, hc⟩ | ⟨hs, hg, hc⟩ | ⟨hc, hg, hs⟩
  · exact Or.inl ⟨hgaussian.mp hg, fun hh => hs (hsphere.mpr hh), fun hh => hc (hcylinder.mpr hh)⟩
  · exact Or.inr (Or.inl
      ⟨hsphere.mp hs, fun hh => hg (hgaussian.mpr hh), fun hh => hc (hcylinder.mpr hh)⟩)
  · exact Or.inr (Or.inr
      ⟨hcylinder.mp hc, fun hh => hg (hgaussian.mpr hh), fun hh => hs (hsphere.mpr hh)⟩)

theorem normalizedGradientRicciSoliton_isometry_classification_of_nonnegative_of_nonflat
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank ℝ E = 3)
    (hcone : ∀ x : M, metricAlgebraicCurvatureTensorAt g x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hnonflat : ∃ x : M, metricRm04At g x ≠ 0) :
    let gaussian := ∃ e : M ≃ₘ⟮I, 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))⟯ EuclideanSpace ℝ (Fin 3),
      Diffeomorph.pullbackMetricCross (euclideanMetric (E := EuclideanSpace ℝ (Fin 3))) e = g ∧
      f = gaussianPotential.comp e.toContMDiffMap
    let sphere := ∃ G : Subgroup (Equiv.Perm (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)),
      ∃ (_ : Finite G)
        (_ : IsCancelSMul G (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
        (_ : ContinuousConstSMul G (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
        (_ : ContMDiffConstSMul (𝓡 3) ∞ G (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)),
      ∃ hmetric : ∀ gamma : G, Diffeomorph.pullbackMetric roundThreeSphereShrinkerMetric
          (MulAction.smulDiffeomorph (n := ∞) (𝓡 3) gamma) = roundThreeSphereShrinkerMetric,
      ∃ e : MulAction.orbitRel.Quotient G
          (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ≃ₘ⟮𝓡 3, I⟯ M,
        Diffeomorph.pullbackMetricCross g e =
          solitonModelQuotientMetric roundThreeSphereShrinkerMetric hmetric ∧
        (∀ x : M, f x = (3 / 2 : ℝ))
    let cylinder := ∃ cover : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) → M,
      solitonModelCovering roundThreeCylinderShrinkerMetric roundThreeCylinderShrinkerPotential g f cover ∧
      ((coveringDeckGroup cover = ⊥ ∧
      ∃ e : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) ≃ₘ⟮
          (𝓡 2).prod 𝓘(Real, Real), I⟯ M,
        (∀ x, e x = cover x) ∧
        Diffeomorph.pullbackMetricCross g e = roundThreeCylinderShrinkerMetric ∧
        ∀ x, f (e x) = 1 + x.2 ^ 2 / 4) ∨
    (coveringDeckGroup cover = cylinderAntipodalGroup ∧
      ∃ e : (RealProjectivePlane × Real) ≃ₘ⟮(𝓡 2).prod 𝓘(Real, Real), I⟯ M,
        (∀ x, e (realProjectivePlaneQuotientMap x.1, x.2) = cover x) ∧
        Diffeomorph.pullbackMetricCross g e =
          (scaleMetric 2 (by norm_num)
            (roundProjectiveMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))).prod
              (euclideanMetric (E := Real)) ∧
        ∀ x, f (e x) = 1 + x.2 ^ 2 / 4) ∨
    (coveringDeckGroup cover = cylinderDiagonalGroup ∧
      ∃ e : PuncturedRealProjectiveThreeSpace ≃ₘ⟮𝓡 3, I⟯ M,
        (∀ x, e (cylinderDiagonalQuotientDiffeomorph
          (cylinderDiagonalQuotientMap x)) = cover x) ∧
        Diffeomorph.pullbackMetricCross g
          (cylinderDiagonalQuotientDiffeomorph.trans e) = cylinderDiagonalQuotientMetric ∧
        ∀ x, f (e (cylinderDiagonalQuotientDiffeomorph x)) =
          cylinderDiagonalQuotientPotential x))
    ¬ gaussian ∧ ((sphere ∧ ¬ cylinder) ∨ (cylinder ∧ ¬ sphere)) := by
  intro gaussian sphere cylinder
  have hnot : ¬ gaussian := by
    rintro ⟨e, hmetric, _⟩
    obtain ⟨x, hx⟩ := hnonflat
    apply hx
    ext v
    have hv : v = vec4 (I := I) (v 0) (v 1) (v 2) (v 3) := by
      ext i
      fin_cases i <;> rfl
    rw [hv]
    change metricRm04StandardAt g x (v 0) (v 1) (v 2) (v 3) = 0
    have hpull := metricRm04Standard_pullbackCross (euclideanMetric (E := EuclideanSpace ℝ (Fin 3)))
      e x (v 0) (v 1) (v 2) (v 3)
    rw [hmetric] at hpull
    simp only [metricRm04StandardAt_apply, euclideanMetric_metricRm04At_eq_zero] at hpull
    exact hpull
  refine ⟨hnot, ?_⟩
  rcases normalizedGradientRicciSoliton_isometry_classification_of_nonnegative h hdim hcone with
    ⟨hg, _, _⟩ | ⟨hs, _, hc⟩ | ⟨hc, _, hs⟩
  · exact (hnot hg).elim
  · exact Or.inl ⟨hs, hc⟩
  · exact Or.inr ⟨hc, hs⟩


theorem normalizedGradientRicciSoliton_isometry_classification_of_nonnegative_of_exists_nonvanishing_top_form
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank ℝ E = 3)
    (hcone : ∀ x : M, metricAlgebraicCurvatureTensorAt g x ∈
      algebraicCurvatureOperatorNonnegativeCone (I := I) (M := M))
    (hΩ : ∃ Ω : DifferentialForm I M 3, ∀ x, Ω x ≠ 0) :
    let gaussian := ∃ e : M ≃ₘ⟮I, 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))⟯ EuclideanSpace ℝ (Fin 3),
      Diffeomorph.pullbackMetricCross (euclideanMetric (E := EuclideanSpace ℝ (Fin 3))) e = g ∧
      f = gaussianPotential.comp e.toContMDiffMap
    let sphere := ∃ G : Subgroup (Equiv.Perm (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)),
      ∃ (_ : Finite G)
        (_ : IsCancelSMul G (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
        (_ : ContinuousConstSMul G (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
        (_ : ContMDiffConstSMul (𝓡 3) ∞ G (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)),
      ∃ hmetric : ∀ gamma : G, Diffeomorph.pullbackMetric roundThreeSphereShrinkerMetric
          (MulAction.smulDiffeomorph (n := ∞) (𝓡 3) gamma) = roundThreeSphereShrinkerMetric,
      ∃ e : MulAction.orbitRel.Quotient G
          (Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ≃ₘ⟮𝓡 3, I⟯ M,
        Diffeomorph.pullbackMetricCross g e =
          solitonModelQuotientMetric roundThreeSphereShrinkerMetric hmetric ∧
        (∀ x : M, f x = (3 / 2 : ℝ))
    let cylinder := ∃ cover : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) → M,
      solitonModelCovering roundThreeCylinderShrinkerMetric roundThreeCylinderShrinkerPotential g f cover ∧
      ((coveringDeckGroup cover = ⊥ ∧
      ∃ e : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) ≃ₘ⟮
          (𝓡 2).prod 𝓘(Real, Real), I⟯ M,
        (∀ x, e x = cover x) ∧
        Diffeomorph.pullbackMetricCross g e = roundThreeCylinderShrinkerMetric ∧
        ∀ x, f (e x) = 1 + x.2 ^ 2 / 4) ∨
    (coveringDeckGroup cover = cylinderDiagonalGroup ∧
      ∃ e : PuncturedRealProjectiveThreeSpace ≃ₘ⟮𝓡 3, I⟯ M,
        (∀ x, e (cylinderDiagonalQuotientDiffeomorph
          (cylinderDiagonalQuotientMap x)) = cover x) ∧
        Diffeomorph.pullbackMetricCross g
          (cylinderDiagonalQuotientDiffeomorph.trans e) = cylinderDiagonalQuotientMetric ∧
        ∀ x, f (e (cylinderDiagonalQuotientDiffeomorph x)) =
          cylinderDiagonalQuotientPotential x))
    (gaussian ∧ ¬ sphere ∧ ¬ cylinder) ∨
      (sphere ∧ ¬ gaussian ∧ ¬ cylinder) ∨
      (cylinder ∧ ¬ gaussian ∧ ¬ sphere) := by
  intro gaussian sphere cylinder
  have hgaussian : (∃ cover : EuclideanSpace ℝ (Fin 3) → M,
      solitonModelCovering (euclideanMetric (E := EuclideanSpace ℝ (Fin 3)))
        (gaussianPotential (E := EuclideanSpace ℝ (Fin 3))) g f cover) ↔ gaussian :=
    exists_solitonModelCovering_gaussian_iff
  have hsphere : (∃ cover : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → M,
      solitonModelCovering roundThreeSphereShrinkerMetric roundThreeSphereShrinkerPotential g f cover) ↔
      sphere := exists_solitonModelCovering_roundThreeSphere_iff h
  have hcylinder : (∃ cover : (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 × Real) → M,
      solitonModelCovering roundThreeCylinderShrinkerMetric roundThreeCylinderShrinkerPotential g f cover) ↔
      cylinder := by
    constructor
    · rintro ⟨cover, hcover⟩
      exact ⟨cover, hcover, solitonModelCovering_roundThreeCylinder_target_isometry_dichotomy_of_exists_nonvanishing_top_form
        hcover hΩ⟩
    · rintro ⟨cover, hcover, _⟩
      exact ⟨cover, hcover⟩
  rcases normalizedGradientRicciSoliton_solitonModelCovering_classification_of_nonnegative h hdim hcone with
    ⟨hg, hs, hc⟩ | ⟨hs, hg, hc⟩ | ⟨hc, hg, hs⟩
  · exact Or.inl ⟨hgaussian.mp hg, fun hh => hs (hsphere.mpr hh), fun hh => hc (hcylinder.mpr hh)⟩
  · exact Or.inr (Or.inl
      ⟨hsphere.mp hs, fun hh => hg (hgaussian.mpr hh), fun hh => hc (hcylinder.mpr hh)⟩)
  · exact Or.inr (Or.inr
      ⟨hcylinder.mp hc, fun hh => hg (hgaussian.mpr hh), fun hh => hs (hsphere.mpr hh)⟩)



end DifferentialGeometry.Geometry
