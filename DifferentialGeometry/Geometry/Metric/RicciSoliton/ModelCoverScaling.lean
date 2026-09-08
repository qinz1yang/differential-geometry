import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models
import DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCover
import DifferentialGeometry.Geometry.Metric.PullbackScaling
import DifferentialGeometry.Geometry.Metric.Pullback.Product

set_option autoImplicit false
noncomputable section
open Bundle Manifold
open scoped Manifold ContDiff
namespace DifferentialGeometry.Geometry

variable {A : Type*} [NormedAddCommGroup A] [InnerProductSpace ℝ A]
  [FiniteDimensional ℝ A]
variable {n : ℕ} [Fact (Module.finrank ℝ A = n + 1)]

omit [FiniteDimensional ℝ A] in
theorem scaleMetric_inv_roundSphereShrinkerMetric
    (hn : 2 ≤ n) {sigma : ℝ} (hsigma : 0 < sigma) :
    scaleMetric sigma⁻¹ (inv_pos.mpr hsigma) (roundSphereShrinkerMetric (A := A) hn) =
      scaleMetric ((roundSphereShrinkerRadius n / Real.sqrt sigma) ^ 2)
        (sq_pos_of_pos (div_pos (roundSphereShrinkerRadius_pos hn) (Real.sqrt_pos.mpr hsigma)))
        (roundMetric (E := A) (n := n)) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  simp only [scaleMetric_inner, roundSphereShrinkerMetric]
  rw [div_pow, Real.sq_sqrt hsigma.le]
  ring

theorem roundSphereShrinkerRadius_three_div_sqrt {sigma : ℝ} :
    roundSphereShrinkerRadius 3 / Real.sqrt sigma = 2 / Real.sqrt sigma := by
  rw [roundSphereShrinkerRadius_three]

theorem roundSphereShrinkerRadius_two_div_sqrt {sigma : ℝ} :
    roundSphereShrinkerRadius 2 / Real.sqrt sigma = Real.sqrt (2 / sigma) := by
  rw [roundSphereShrinkerRadius_two, Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 2)]

theorem roundThreeCylinderShrinkerPotential_dilation
    {sigma : ℝ} (hsigma : 0 < sigma)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) :
    roundThreeCylinderShrinkerPotential (x.1, Real.sqrt sigma * x.2) =
      1 + sigma * x.2 ^ 2 / 4 := by
  rw [roundThreeCylinderShrinkerPotential_apply, mul_pow, Real.sq_sqrt hsigma.le]

private noncomputable def cylinderDilation {sigma : ℝ} (hsigma : 0 < sigma) :
    (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) ≃ₘ⟮
      (𝓡 2).prod 𝓘(ℝ, ℝ), (𝓡 2).prod 𝓘(ℝ, ℝ)⟯
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) :=
  (Diffeomorph.refl (𝓡 2) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞).prodCongr
    (LinearEquiv.smulOfNeZero ℝ ℝ (Real.sqrt sigma) (Real.sqrt_pos.mpr hsigma).ne').toContinuousLinearEquiv.toDiffeomorph

private theorem cylinderDilation_apply {sigma : ℝ} (hsigma : 0 < sigma)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) :
    cylinderDilation hsigma x = (x.1, Real.sqrt sigma * x.2) := rfl

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem cylinderDilation_pullbackMetric {sigma : ℝ} (hsigma : 0 < sigma) :
    Diffeomorph.pullbackMetricCross
      (scaleMetric sigma⁻¹ (inv_pos.mpr hsigma) roundThreeCylinderShrinkerMetric)
      (cylinderDilation hsigma) =
    (scaleMetric sigma⁻¹ (inv_pos.mpr hsigma) roundTwoSphereShrinkerMetric).prod
      (euclideanMetric (E := ℝ)) := by
  let T := (LinearEquiv.smulOfNeZero ℝ ℝ (Real.sqrt sigma)
    (Real.sqrt_pos.mpr hsigma).ne').toContinuousLinearEquiv
  have hT (x : ℝ) : T x = Real.sqrt sigma * x := rfl
  have hderiv (x : ℝ) : mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) T.toDiffeomorph x =
      T.toContinuousLinearMap := by
    rw [mfderiv_eq_fderiv]
    change fderiv ℝ (T.toContinuousLinearMap : ℝ → ℝ) x = _
    exact T.toContinuousLinearMap.fderiv
  have hline : Diffeomorph.pullbackMetric (euclideanMetric (E := ℝ)) T.toDiffeomorph =
      scaleMetric sigma hsigma (euclideanMetric (E := ℝ)) := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [Diffeomorph.pullbackMetric_inner, hderiv, scaleMetric_inner,
      euclideanMetric_inner, euclideanMetric_inner]
    change inner ℝ (Real.sqrt sigma • v) (Real.sqrt sigma • w) = sigma * inner ℝ v w
    rw [real_inner_smul_left, real_inner_smul_right]
    rw [← mul_assoc, ← sq, Real.sq_sqrt hsigma.le]
  rw [Diffeomorph.pullbackMetricCross_scaleMetric,
    Diffeomorph.pullbackMetricCross_eq_pullbackMetric,
    roundThreeCylinderShrinkerMetric, cylinderDilation,
    Diffeomorph.pullbackMetric_prodCongr, Diffeomorph.pullbackMetric_refl]
  change scaleMetric sigma⁻¹ (inv_pos.mpr hsigma)
      (roundTwoSphereShrinkerMetric.prod (Diffeomorph.pullbackMetric euclideanMetric T.toDiffeomorph)) = _
  rw [hline]
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  simp only [scaleMetric_inner, SmoothRiemannianMetric.prod_inner]
  have hs := ne_of_gt hsigma
  field_simp

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [SigmaCompactSpace M] [T2Space M]

private instance euclideanFourFinrankFact : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 4)) = 3 + 1) := ⟨by simp⟩
private instance euclideanThreeFinrankFact : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

theorem solitonModelCovering_roundThreeSphere_unscaled_metric
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    {sigma C : ℝ} (hsigma : 0 < sigma)
    {cover : Metric.sphere (0 : EuclideanSpace ℝ (Fin 4)) 1 → M}
    (hcover : solitonModelCovering roundThreeSphereShrinkerMetric roundThreeSphereShrinkerPotential
      (scaleMetric sigma hsigma g) (f + ContMDiffMap.const (C / sigma)) cover) :
    localPullMetric g cover (solitonModelCovering_isLocalDiffeomorph hcover) =
      scaleMetric ((2 / Real.sqrt sigma) ^ 2)
        (sq_pos_of_pos (div_pos (by norm_num) (Real.sqrt_pos.mpr hsigma)))
        (roundMetric (E := EuclideanSpace ℝ (Fin 4)) (n := 3)) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have hm := solitonModelCovering_metric hcover x v w
  simp only [roundThreeSphereShrinkerMetric, roundSphereShrinkerMetric,
    scaleMetric_inner, roundSphereShrinkerRadius_three] at hm
  rw [localPullMetric_inner, scaleMetric_inner, div_pow, Real.sq_sqrt hsigma.le]
  field_simp
  nlinarith [hm]

theorem solitonModelCovering_roundThreeCylinder_unscaled_metric
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    {sigma C : ℝ} (hsigma : 0 < sigma)
    {cover : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ → M}
    (hcover : solitonModelCovering roundThreeCylinderShrinkerMetric roundThreeCylinderShrinkerPotential
      (scaleMetric sigma hsigma g) (f + ContMDiffMap.const (C / sigma)) cover) :
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
        (euclideanMetric (E := ℝ)) := by
  have hscale : localPullMetric g cover (solitonModelCovering_isLocalDiffeomorph hcover) =
      scaleMetric sigma⁻¹ (inv_pos.mpr hsigma) roundThreeCylinderShrinkerMetric := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    have hm := solitonModelCovering_metric hcover x v w
    rw [scaleMetric_inner] at hm
    rw [localPullMetric_inner, scaleMetric_inner, hm]
    field_simp
  have hcomp : localPullMetric g (cover ∘ cylinderDilation hsigma)
      (isLocalDiffeomorph_comp (solitonModelCovering_isLocalDiffeomorph hcover)
        (cylinderDilation hsigma).isLocalDiffeomorph) =
      Diffeomorph.pullbackMetricCross
        (localPullMetric g cover (solitonModelCovering_isLocalDiffeomorph hcover))
        (cylinderDilation hsigma) := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [localPullMetric_inner, Diffeomorph.pullbackMetricCross_inner, localPullMetric_inner,
      mfderiv_comp x
        ((solitonModelCovering_contMDiff hcover).mdifferentiableAt (by simp))
        ((cylinderDilation hsigma).contMDiff.mdifferentiableAt (by simp))]
    rfl
  change localPullMetric g (cover ∘ cylinderDilation hsigma)
      (isLocalDiffeomorph_comp (solitonModelCovering_isLocalDiffeomorph hcover)
        (cylinderDilation hsigma).isLocalDiffeomorph) = _
  rw [hcomp, hscale, cylinderDilation_pullbackMetric]
  congr 1
  change scaleMetric sigma⁻¹ (inv_pos.mpr hsigma)
      (roundSphereShrinkerMetric (A := EuclideanSpace ℝ (Fin 3)) (n := 2) (by decide)) = _
  rw [scaleMetric_inv_roundSphereShrinkerMetric (by decide) hsigma]
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  simp only [scaleMetric_inner, roundSphereShrinkerRadius_two_div_sqrt]

theorem solitonModelCovering_roundThreeCylinder_unscaled_potential
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    {sigma C : ℝ} (hsigma : 0 < sigma)
    {cover : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ → M}
    (hcover : solitonModelCovering roundThreeCylinderShrinkerMetric roundThreeCylinderShrinkerPotential
      (scaleMetric sigma hsigma g) (f + ContMDiffMap.const (C / sigma)) cover)
    (x : Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 × ℝ) :
    f (cover (((Diffeomorph.refl (𝓡 2) (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1) ∞).prodCongr
        (LinearEquiv.smulOfNeZero ℝ ℝ (Real.sqrt sigma)
          (Real.sqrt_pos.mpr hsigma).ne').toContinuousLinearEquiv.toDiffeomorph) x)) + C / sigma =
      1 + sigma * x.2 ^ 2 / 4 := by
  have hp := solitonModelCovering_potential hcover (cylinderDilation hsigma x)
  change roundThreeCylinderShrinkerPotential (cylinderDilation hsigma x) =
    f (cover (cylinderDilation hsigma x)) + C / sigma at hp
  rw [cylinderDilation_apply, roundThreeCylinderShrinkerPotential_dilation hsigma] at hp
  exact hp.symm

end DifferentialGeometry.Geometry
