import DifferentialGeometry.Geometry.Metric.Quotient
import DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCover

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [LocallyCompactSpace M]
variable {G : Type*} [Group G] [MulAction G M]
  [ProperlyDiscontinuousSMul G M] [ContinuousConstSMul G M]
  [IsCancelSMul G M] [ContMDiffConstSMul I ∞ G M]

private noncomputable def solitonModelQuotientPotentialFn
    (Fpot : C^∞⟮I, M; Real⟯)
    (hpotential : ∀ gamma : G, ∀ x : M, Fpot (gamma • x) = Fpot x) :
    MulAction.orbitRel.Quotient G M → Real :=
  Quotient.lift Fpot fun x y hxy => by
    obtain ⟨gamma, rfl⟩ := hxy
    exact hpotential gamma y

noncomputable def solitonModelQuotientMetric
    (h : SmoothRiemannianMetric I M)
    (hmetric : ∀ gamma : G,
      Diffeomorph.pullbackMetric h
        (MulAction.smulDiffeomorph (n := ∞) I gamma) = h) :
    SmoothRiemannianMetric I (MulAction.orbitRel.Quotient G M) :=
  descendedMetric h (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M)
    (MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul
      (n := ∞) I)
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.surjective
    (metricFiberCompatible_quotientMk_of_invariant h hmetric)

noncomputable def solitonModelQuotientPotential
    (Fpot : C^∞⟮I, M; Real⟯)
    (hpotential : ∀ gamma : G, ∀ x : M, Fpot (gamma • x) = Fpot x) :
    C^∞⟮I, MulAction.orbitRel.Quotient G M; Real⟯ :=
  ⟨solitonModelQuotientPotentialFn Fpot hpotential,
    (MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul
      (n := ∞) I).contMDiff_of_comp_of_surjective
        isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.surjective
        (by
          have heq : solitonModelQuotientPotentialFn Fpot hpotential ∘
              (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M) = Fpot := by
            funext x
            rfl
          rw [heq]
          exact Fpot.contMDiff)⟩

omit [I.Boundaryless] [SigmaCompactSpace M] in
theorem localPullMetric_solitonModelQuotientMetric
    (h : SmoothRiemannianMetric I M)
    (hmetric : ∀ gamma : G,
      Diffeomorph.pullbackMetric h
        (MulAction.smulDiffeomorph (n := ∞) I gamma) = h) :
    localPullMetric (solitonModelQuotientMetric h hmetric)
        (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M)
        (MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul
          (n := ∞) I) = h :=
  localPullMetric_descendedMetric h
    (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M)
    (MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul
      (n := ∞) I)
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.surjective
    (metricFiberCompatible_quotientMk_of_invariant h hmetric)

omit [FiniteDimensional Real E] [I.Boundaryless] [SigmaCompactSpace M] in
theorem solitonModelQuotientPotential_apply
    (Fpot : C^∞⟮I, M; Real⟯)
    (hpotential : ∀ gamma : G, ∀ x : M, Fpot (gamma • x) = Fpot x)
    (x : M) :
    solitonModelQuotientPotential Fpot hpotential (Quotient.mk'' x) = Fpot x :=
  rfl

omit [I.Boundaryless] in
theorem solitonModelQuotientMetric_complete
    (h : SmoothRiemannianMetric I M)
    (hcomplete : RiemannianMetricComplete (I := I) h)
    (hmetric : ∀ gamma : G,
      Diffeomorph.pullbackMetric h
        (MulAction.smulDiffeomorph (n := ∞) I gamma) = h) :
    RiemannianMetricComplete (I := I)
      (solitonModelQuotientMetric h hmetric) :=
  RiemannianMetricComplete.of_coveringMap_localPullMetric h
    (solitonModelQuotientMetric h hmetric)
    (MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul
      (n := ∞) I)
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isCoveringMap
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.surjective
    (localPullMetric_solitonModelQuotientMetric h hmetric) hcomplete

theorem normalizedGradientRicciSoliton_solitonModelQuotient
    {h : SmoothRiemannianMetric I M} {Fpot : C^∞⟮I, M; Real⟯}
    (hsol : normalizedGradientRicciSoliton (I := I) h Fpot)
    (hmetric : ∀ gamma : G,
      Diffeomorph.pullbackMetric h
        (MulAction.smulDiffeomorph (n := ∞) I gamma) = h)
    (hpotential : ∀ gamma : G, ∀ x : M, Fpot (gamma • x) = Fpot x) :
    normalizedGradientRicciSoliton (I := I)
      (solitonModelQuotientMetric h hmetric)
      (solitonModelQuotientPotential Fpot hpotential) :=
  normalizedGradientRicciSoliton_of_surjective_localPullMetric hsol
    (solitonModelQuotientMetric_complete h hsol.1 hmetric)
    (MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul
      (n := ∞) I)
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.surjective
    (localPullMetric_solitonModelQuotientMetric h hmetric)
    (fun x => (solitonModelQuotientPotential_apply Fpot hpotential x).symm)

theorem solitonModelCovering_quotient_of_invariant
    {h : SmoothRiemannianMetric I M} {Fpot : C^∞⟮I, M; Real⟯}
    (hsol : normalizedGradientRicciSoliton (I := I) h Fpot)
    (hmetric : ∀ gamma : G,
      Diffeomorph.pullbackMetric h
        (MulAction.smulDiffeomorph (n := ∞) I gamma) = h)
    (hpotential : ∀ gamma : G, ∀ x : M, Fpot (gamma • x) = Fpot x) :
    solitonModelCovering h Fpot
      (solitonModelQuotientMetric h hmetric)
      (solitonModelQuotientPotential Fpot hpotential)
      (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M) := by
  refine ⟨hsol,
    normalizedGradientRicciSoliton_solitonModelQuotient hsol hmetric hpotential,
    MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul I,
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.surjective,
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isCoveringMap,
    ?_, ?_⟩
  · intro x v w
    have hpull := congrArg
      (fun k : SmoothRiemannianMetric I M => k.inner x v w)
      (localPullMetric_solitonModelQuotientMetric h hmetric)
    rw [localPullMetric_inner] at hpull
    exact hpull.symm
  · intro x
    exact (solitonModelQuotientPotential_apply Fpot hpotential x).symm

theorem solitonModelCovering_quotient_target_unique
    {h : SmoothRiemannianMetric I M} {Fpot : C^∞⟮I, M; Real⟯}
    {g : SmoothRiemannianMetric I (MulAction.orbitRel.Quotient G M)}
    {f : C^∞⟮I, MulAction.orbitRel.Quotient G M; Real⟯}
    (hpi : solitonModelCovering h Fpot g f
      (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M))
    (hmetric : ∀ gamma : G,
      Diffeomorph.pullbackMetric h
        (MulAction.smulDiffeomorph (n := ∞) I gamma) = h)
    (hpotential : ∀ gamma : G, ∀ x : M, Fpot (gamma • x) = Fpot x) :
    g = solitonModelQuotientMetric h hmetric ∧
      f = solitonModelQuotientPotential Fpot hpotential := by
  constructor
  · apply localPullMetric_injective_of_surjective
      (Quotient.mk'' : M → MulAction.orbitRel.Quotient G M)
      (MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul I)
      isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.surjective
    exact (solitonModelCovering_metric_eq_localPull hpi).symm.trans
      (localPullMetric_solitonModelQuotientMetric h hmetric).symm
  · apply ContMDiffMap.ext
    intro y
    obtain ⟨x, rfl⟩ :=
      isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.surjective y
    exact (solitonModelCovering_potential hpi x).symm.trans
      (solitonModelQuotientPotential_apply Fpot hpotential x).symm

end DifferentialGeometry.Geometry
