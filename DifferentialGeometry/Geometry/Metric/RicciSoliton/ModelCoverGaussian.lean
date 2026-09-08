import DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCover
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models
import DifferentialGeometry.Geometry.Metric.PullbackCompleteness

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

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace Real V]
  [FiniteDimensional Real V]

theorem solitonModelCovering_gaussian_deckGroup_eq_bot
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {cover : V → M}
    (hπ : solitonModelCovering (euclideanMetric (E := V))
      (gaussianPotential (E := V)) g f cover) :
    coveringDeckGroup cover = ⊥ := by
  apply le_antisymm
  · intro gamma hgamma
    simp only [Subgroup.mem_bot]
    let deck : coveringDeckGroup cover := ⟨gamma, hgamma⟩
    have hpotential := solitonModelCovering_deckGroup_potential hπ deck 0
    change gaussianPotential (gamma 0) = gaussianPotential 0 at hpotential
    simp only [gaussianPotential_apply, norm_zero] at hpotential
    have hfix : gamma 0 = 0 := by
      apply norm_eq_zero.mp
      nlinarith [sq_nonneg ‖gamma 0‖]
    have hdeck : deck = 1 := coveringDeckGroup_eq_one_of_apply_eq
      (solitonModelCovering_isCoveringMap hπ) deck 0 hfix
    exact congrArg Subtype.val hdeck
  · exact bot_le

theorem solitonModelCovering_gaussian_injective
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {cover : V → M}
    (hπ : solitonModelCovering (euclideanMetric (E := V))
      (gaussianPotential (E := V)) g f cover) :
    Function.Injective cover := by
  intro x y hxy
  obtain ⟨gamma, hgamma⟩ :=
    (coveringDeckGroup_apply_eq_iff
      (solitonModelCovering_isCoveringMap hπ)).mp hxy
  have hmem : gamma.1 ∈ (⊥ : Subgroup (Equiv.Perm V)) := by
    rw [← solitonModelCovering_gaussian_deckGroup_eq_bot hπ]
    exact gamma.property
  have hone : gamma = 1 := by
    apply Subtype.ext
    simpa using hmem
  rw [hone] at hgamma
  simpa using hgamma.symm

noncomputable def gaussianSolitonModelCoveringDiffeomorph
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {cover : V → M}
    (hπ : solitonModelCovering (euclideanMetric (E := V))
      (gaussianPotential (E := V)) g f cover) :
    V ≃ₘ⟮𝓘(Real, V), I⟯ M :=
  (solitonModelCovering_isLocalDiffeomorph hπ).diffeomorphOfBijective
    ⟨solitonModelCovering_gaussian_injective hπ,
      solitonModelCovering_surjective hπ⟩

@[simp] theorem gaussianSolitonModelCoveringDiffeomorph_apply
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {cover : V → M}
    (hπ : solitonModelCovering (euclideanMetric (E := V))
      (gaussianPotential (E := V)) g f cover) (x : V) :
    gaussianSolitonModelCoveringDiffeomorph hπ x = cover x :=
  rfl

theorem gaussianSolitonModelCoveringDiffeomorph_pullbackMetric
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {cover : V → M}
    (hπ : solitonModelCovering (euclideanMetric (E := V))
      (gaussianPotential (E := V)) g f cover) :
    Diffeomorph.pullbackMetricCross g
        (gaussianSolitonModelCoveringDiffeomorph hπ) =
      euclideanMetric := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [Diffeomorph.pullbackMetricCross_inner]
  exact (solitonModelCovering_metric hπ x v w).symm

theorem gaussianSolitonModelCoveringDiffeomorph_symm_pullbackMetric
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {cover : V → M}
    (hπ : solitonModelCovering (euclideanMetric (E := V))
      (gaussianPotential (E := V)) g f cover) :
    Diffeomorph.pullbackMetricCross (euclideanMetric (E := V))
      (gaussianSolitonModelCoveringDiffeomorph hπ).symm = g :=
  Diffeomorph.pullbackMetricCross_symm_eq_iff.mp
    (gaussianSolitonModelCoveringDiffeomorph_pullbackMetric hπ)

theorem gaussianSolitonModelCoveringDiffeomorph_potential
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {cover : V → M}
    (hπ : solitonModelCovering (euclideanMetric (E := V))
      (gaussianPotential (E := V)) g f cover) :
    gaussianPotential (E := V) =
      f.comp (gaussianSolitonModelCoveringDiffeomorph hπ).toContMDiffMap := by
  apply ContMDiffMap.ext
  intro x
  exact solitonModelCovering_potential hπ x

theorem gaussianSolitonModelCoveringDiffeomorph_symm_potential
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {cover : V → M}
    (hπ : solitonModelCovering (euclideanMetric (E := V))
      (gaussianPotential (E := V)) g f cover) :
    f = gaussianPotential.comp
      (gaussianSolitonModelCoveringDiffeomorph hπ).symm.toContMDiffMap := by
  apply ContMDiffMap.ext
  intro y
  have hpotential := solitonModelCovering_potential hπ
    ((gaussianSolitonModelCoveringDiffeomorph hπ).symm y)
  change gaussianPotential ((gaussianSolitonModelCoveringDiffeomorph hπ).symm y) =
    f ((gaussianSolitonModelCoveringDiffeomorph hπ)
      ((gaussianSolitonModelCoveringDiffeomorph hπ).symm y)) at hpotential
  rw [(gaussianSolitonModelCoveringDiffeomorph hπ).apply_symm_apply] at hpotential
  exact hpotential.symm

theorem solitonModelCovering_gaussian_of_isometry
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    (e : M ≃ₘ⟮I, 𝓘(ℝ, V)⟯ V)
    (hg : Diffeomorph.pullbackMetricCross (euclideanMetric (E := V)) e = g)
    (hf : f = gaussianPotential.comp e.toContMDiffMap) :
    solitonModelCovering (euclideanMetric (E := V))
      (gaussianPotential (E := V)) g f e.symm := by
  have hcomplete : RiemannianMetricComplete (I := I)
      (localPullMetric (euclideanMetric (E := V)) e e.isLocalDiffeomorph) := by
    rw [← Diffeomorph.pullbackMetricCross_eq_localPullMetric]
    exact RiemannianMetricComplete.pullbackCross _ e normalizedGradientRicciSoliton_gaussian.1
  have hsol := normalizedGradientRicciSoliton_localPullMetric
    (normalizedGradientRicciSoliton_gaussian (E := V)) e.isLocalDiffeomorph hcomplete
  rw [← Diffeomorph.pullbackMetricCross_eq_localPullMetric, hg] at hsol
  change normalizedGradientRicciSoliton g (gaussianPotential.comp e.toContMDiffMap) at hsol
  rw [← hf] at hsol
  refine ⟨normalizedGradientRicciSoliton_gaussian, hsol, e.symm.isLocalDiffeomorph,
    e.symm.surjective, ?_, ?_, ?_⟩
  · exact (solitonModelCovering_isCoveringMap (solitonModelCovering_refl hsol)).comp_homeomorph
      e.symm.toHomeomorph
  · intro x v w
    have h := congrArg (fun k : SmoothRiemannianMetric 𝓘(ℝ, V) V => k.inner x v w)
      (Diffeomorph.pullbackMetricCross_symm_eq_iff.mp hg)
    rw [Diffeomorph.pullbackMetricCross_inner] at h
    exact h.symm
  · intro x
    rw [hf]
    change gaussianPotential x = gaussianPotential (e (e.symm x))
    rw [e.apply_symm_apply]

theorem exists_solitonModelCovering_gaussian_iff
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯} :
    (∃ cover : V → M, solitonModelCovering (euclideanMetric (E := V))
      (gaussianPotential (E := V)) g f cover) ↔
    ∃ e : M ≃ₘ⟮I, 𝓘(ℝ, V)⟯ V,
      Diffeomorph.pullbackMetricCross (euclideanMetric (E := V)) e = g ∧
      f = gaussianPotential.comp e.toContMDiffMap := by
  constructor
  · rintro ⟨cover, hcover⟩
    exact ⟨(gaussianSolitonModelCoveringDiffeomorph hcover).symm,
      gaussianSolitonModelCoveringDiffeomorph_symm_pullbackMetric hcover,
      gaussianSolitonModelCoveringDiffeomorph_symm_potential hcover⟩
  · rintro ⟨e, hg, hf⟩
    exact ⟨e.symm, solitonModelCovering_gaussian_of_isometry e hg hf⟩

variable {L : Type*} [TopologicalSpace L]
variable {K : ModelWithCorners Real V L} [K.Boundaryless]
variable {P : Type*} [TopologicalSpace P] [ChartedSpace L P]
  [IsManifold K ∞ P] [SigmaCompactSpace P] [T2Space P]

theorem isGaussianGradientRicciSoliton_of_solitonModelCovering
    {g : SmoothRiemannianMetric K P} {f : C^∞⟮K, P; Real⟯}
    {cover : V → P}
    (hπ : solitonModelCovering (euclideanMetric (E := V))
      (gaussianPotential (E := V)) g f cover) :
    isGaussianGradientRicciSoliton (E := V) g f 1 := by
  let Phi : V ≃ₘ⟮𝓘(Real, V), K⟯ P :=
    gaussianSolitonModelCoveringDiffeomorph hπ
  refine ⟨zero_lt_one, Phi.symm, 0, ?_, ?_⟩
  · calc
      Diffeomorph.pullbackMetricCross euclideanMetric Phi.symm = g :=
        gaussianSolitonModelCoveringDiffeomorph_symm_pullbackMetric hπ
      _ = scaleMetric (I := K) 1 zero_lt_one g := by
        apply SmoothRiemannianMetric.ext_inner
        intro y v w
        simp only [scaleMetric_inner, one_mul]
  · apply ContMDiffMap.ext
    intro y
    have hpotential := congrArg (fun q : C^∞⟮K, P; Real⟯ => q y)
      (gaussianSolitonModelCoveringDiffeomorph_symm_potential hπ)
    change f y + 0 = gaussianPotential (Phi.symm y)
    simpa using hpotential

end DifferentialGeometry.Geometry
