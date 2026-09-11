import DifferentialGeometry.Geometry.Metric.Sphere.DeckGroup
import DifferentialGeometry.Topology.Covering.FiniteDeckGroup
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models
import DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCoverQuotient

set_option autoImplicit false
noncomputable section
open Bundle Manifold Metric Module
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] {H : Type*} [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]

private instance euclideanFourFinrankFact :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩

theorem solitonModelCovering_roundThreeSphere_isQuotientCoveringMap
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    {p : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → M}
    (hπ : solitonModelCovering roundThreeSphereShrinkerMetric
      roundThreeSphereShrinkerPotential g f p) :
    IsQuotientCoveringMap p (coveringDeckGroup p) := by
  apply isQuotientCoveringMap_coveringDeckGroup_of_roundMetric (n := 3) (by decide)
    (scaleMetric (1 / 4) (by norm_num) g)
    (solitonModelCovering_isLocalDiffeomorph hπ) (solitonModelCovering_surjective hπ)
  intro x v w
  have hmetric := solitonModelCovering_metric hπ x v w
  simp only [roundThreeSphereShrinkerMetric, roundSphereShrinkerMetric,
    scaleMetric_inner, roundSphereShrinkerRadius_three] at hmetric ⊢
  linarith

theorem solitonModelCovering_roundThreeSphere_potential
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    {p : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → M}
    (hπ : solitonModelCovering roundThreeSphereShrinkerMetric
      roundThreeSphereShrinkerPotential g f p) :
    ∀ x : M, f x = (3 / 2 : ℝ) := by
  intro x
  obtain ⟨y, rfl⟩ := solitonModelCovering_surjective hπ x
  rw [← solitonModelCovering_potential hπ]
  exact roundThreeSphereShrinkerPotential_apply y


theorem solitonModelCovering_roundThreeSphere_finite_deckGroup
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    {p : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → M}
    (hπ : solitonModelCovering roundThreeSphereShrinkerMetric
      roundThreeSphereShrinkerPotential g f p) :
    Finite (coveringDeckGroup p) := by
  let _ : PreconnectedSpace (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
    Subtype.preconnectedSpace (isPreconnected_sphere
      (Module.one_lt_rank_of_one_lt_finrank (by norm_num)) 0 1)
  exact finite_coveringDeckGroup_of_compactSpace (solitonModelCovering_isCoveringMap hπ)


theorem solitonModelCovering_roundThreeSphere_quotient
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    {p : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → M}
    (hπ : solitonModelCovering roundThreeSphereShrinkerMetric
      roundThreeSphereShrinkerPotential g f p) :
    let hp := solitonModelCovering_roundThreeSphere_isQuotientCoveringMap hπ
    let _ := hp.isCancelSMul
    let _ := solitonModelCovering_roundThreeSphere_finite_deckGroup hπ
    let _ : ContMDiffConstSMul (𝓡 3) ∞ (coveringDeckGroup p)
        (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
      ⟨coveringDeckGroup_contMDiff (solitonModelCovering_isLocalDiffeomorph hπ)⟩
    ∃ e : MulAction.orbitRel.Quotient (coveringDeckGroup p)
        (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ≃ₘ⟮𝓡 3, I⟯ M,
      (∀ x, e (Quotient.mk'' x) = p x) ∧
      (∀ x, e.symm (p x) = Quotient.mk'' x) ∧
      Diffeomorph.pullbackMetricCross g e =
        solitonModelQuotientMetric roundThreeSphereShrinkerMetric
          (solitonModelCovering_smul_metric hπ hp) ∧
      f.comp e.toContMDiffMap =
        solitonModelQuotientPotential roundThreeSphereShrinkerPotential
          (solitonModelCovering_smul_potential hπ hp) ∧
      (∀ x : M, f x = (3 / 2 : ℝ)) := by
  dsimp only
  let hp := solitonModelCovering_roundThreeSphere_isQuotientCoveringMap hπ
  let _ := hp.isCancelSMul
  let _ := solitonModelCovering_roundThreeSphere_finite_deckGroup hπ
  let _ : ContMDiffConstSMul (𝓡 3) ∞ (coveringDeckGroup p)
      (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
    ⟨coveringDeckGroup_contMDiff (solitonModelCovering_isLocalDiffeomorph hπ)⟩
  exact ⟨hp.orbitRelQuotientDiffeomorph (solitonModelCovering_isLocalDiffeomorph hπ),
    hp.orbitRelQuotientDiffeomorph_apply _, hp.orbitRelQuotientDiffeomorph_symm_apply _,
    solitonModelCovering_quotient_metric hπ hp, solitonModelCovering_quotient_potential hπ hp,
    solitonModelCovering_roundThreeSphere_potential hπ⟩


theorem solitonModelCovering_roundThreeSphere_of_quotient_isometry
    {G : Type*} [Group G] [Finite G]
    [MulAction G (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)]
    [IsCancelSMul G (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)]
    [ContinuousConstSMul G (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)]
    [ContMDiffConstSMul (𝓡 3) ∞ G (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (hsol : normalizedGradientRicciSoliton g f)
    (hmetric : ∀ gamma : G, Diffeomorph.pullbackMetric roundThreeSphereShrinkerMetric
      (MulAction.smulDiffeomorph (n := ∞) (𝓡 3) gamma) = roundThreeSphereShrinkerMetric)
    (e : MulAction.orbitRel.Quotient G
      (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ≃ₘ⟮𝓡 3, I⟯ M)
    (he : Diffeomorph.pullbackMetricCross g e =
      solitonModelQuotientMetric roundThreeSphereShrinkerMetric hmetric)
    (hf : ∀ x : M, f x = (3 / 2 : ℝ)) :
    solitonModelCovering roundThreeSphereShrinkerMetric
      roundThreeSphereShrinkerPotential g f
      (e ∘ (Quotient.mk'' : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 →
        MulAction.orbitRel.Quotient G (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))) := by
  let q : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 →
      MulAction.orbitRel.Quotient G (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) := Quotient.mk''
  let hq := MulAction.isLocalDiffeomorph_quotientMk_of_properlyDiscontinuousSMul
    (n := ∞) (G := G) (M := sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) (𝓡 3)
  refine ⟨normalizedGradientRicciSoliton_roundThreeSphere, hsol,
    isLocalDiffeomorph_comp e.isLocalDiffeomorph hq,
    e.surjective.comp Quotient.mk_surjective,
    isQuotientCoveringMap_quotientMk_of_properlyDiscontinuousSMul.isCoveringMap.homeomorph_comp
      e.toHomeomorph, ?_, ?_⟩
  · intro x v w
    have hid := congrArg (fun k : SmoothRiemannianMetric (𝓡 3)
        (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) => k.inner x v w)
      (localPullMetric_solitonModelQuotientMetric roundThreeSphereShrinkerMetric hmetric)
    rw [← he, localPullMetric_inner, Diffeomorph.pullbackMetricCross_inner] at hid
    rw [mfderiv_comp_apply x (e.contMDiff.mdifferentiableAt (by simp))
      (hq.contMDiff.mdifferentiableAt (by simp)),
      mfderiv_comp_apply x (e.contMDiff.mdifferentiableAt (by simp))
      (hq.contMDiff.mdifferentiableAt (by simp))]
    exact hid.symm
  · intro x
    rw [hf]
    exact roundThreeSphereShrinkerPotential_apply x


theorem exists_solitonModelCovering_roundThreeSphere_iff
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (hsol : normalizedGradientRicciSoliton g f) :
    (∃ p : sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → M,
      solitonModelCovering roundThreeSphereShrinkerMetric
        roundThreeSphereShrinkerPotential g f p) ↔
    ∃ G : Subgroup (Equiv.Perm (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)),
      ∃ (_ : Finite G)
        (_ : IsCancelSMul G (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
        (_ : ContinuousConstSMul G (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1))
        (_ : ContMDiffConstSMul (𝓡 3) ∞ G (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1)),
      ∃ hmetric : ∀ gamma : G, Diffeomorph.pullbackMetric roundThreeSphereShrinkerMetric
          (MulAction.smulDiffeomorph (n := ∞) (𝓡 3) gamma) = roundThreeSphereShrinkerMetric,
      ∃ e : MulAction.orbitRel.Quotient G
          (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) ≃ₘ⟮𝓡 3, I⟯ M,
        Diffeomorph.pullbackMetricCross g e =
          solitonModelQuotientMetric roundThreeSphereShrinkerMetric hmetric ∧
        (∀ x : M, f x = (3 / 2 : ℝ)) := by
  constructor
  · rintro ⟨p, hp⟩
    let hquot := solitonModelCovering_roundThreeSphere_isQuotientCoveringMap hp
    let _ := hquot.isCancelSMul
    let _ := solitonModelCovering_roundThreeSphere_finite_deckGroup hp
    let _ : ContMDiffConstSMul (𝓡 3) ∞ (coveringDeckGroup p)
        (sphere (0 : EuclideanSpace ℝ (Fin 4)) 1) :=
      ⟨coveringDeckGroup_contMDiff (solitonModelCovering_isLocalDiffeomorph hp)⟩
    exact ⟨coveringDeckGroup p, inferInstance, inferInstance, inferInstance, inferInstance,
      solitonModelCovering_smul_metric hp hquot,
      hquot.orbitRelQuotientDiffeomorph (solitonModelCovering_isLocalDiffeomorph hp),
      solitonModelCovering_quotient_metric hp hquot,
      solitonModelCovering_roundThreeSphere_potential hp⟩
  · rintro ⟨G, hfinite, hfree, hcont, hsmooth, hmetric, e, he, hf⟩
    let _ := hfinite
    let _ := hfree
    let _ := hcont
    let _ := hsmooth
    exact ⟨_, solitonModelCovering_roundThreeSphere_of_quotient_isometry hsol hmetric e he hf⟩

end DifferentialGeometry.Geometry
