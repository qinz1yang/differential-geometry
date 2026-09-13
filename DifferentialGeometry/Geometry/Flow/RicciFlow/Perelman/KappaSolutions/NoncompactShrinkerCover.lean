import DifferentialGeometry.Geometry.Metric.RicciSoliton.Defs
import DifferentialGeometry.Geometry.Metric.Completeness
import DifferentialGeometry.Geometry.Metric.UniversalCover.Metric
import DifferentialGeometry.Geometry.Metric.Sphere.Round.Metric
import DifferentialGeometry.Geometry.Curvature.Metric.Defs
import DifferentialGeometry.Geometry.Metric.UniversalCover.Completeness
import DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCoverCylinderClassification
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Models
import DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCoverGaussian
import DifferentialGeometry.Geometry.Metric.PullbackScaling
import DifferentialGeometry.Topology.Covering.SmoothLift
import DifferentialGeometry.Topology.Covering.Smooth.LocalDiffeomorph
import DifferentialGeometry.Topology.Covering.CylindricalModel
import DifferentialGeometry.Topology.ProjectiveSpace.SphereHalfTurnFrame
import DifferentialGeometry.Topology.Manifold.LocallyPathConnected
import DifferentialGeometry.Geometry.Flow.RicciFlow.Soliton.Classification

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Topology
open scoped Manifold ContDiff

local notation "SphereTwo" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1

private local instance upstreamNoncompactShrinkerSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [NoncompactSpace M]
  [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M] [Inhabited M]

private local instance upstreamNoncompactShrinkerC1 : IsManifold I 1 M :=
  IsManifold.of_le (n := ∞) (by decide)

local notation "Cylinder" => SphereTwo × ℝ
local notation "CylinderI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
private noncomputable def lineMul (c : ℝ) (hc : c ≠ 0) : ℝ ≃ₘ⟮𝓘(ℝ, ℝ), 𝓘(ℝ, ℝ)⟯ ℝ :=
  (LinearEquiv.smulOfNeZero ℝ ℝ c hc).toContinuousLinearEquiv.toDiffeomorph

private noncomputable def lineScale (c : ℝ) (hc : c ≠ 0) :
    Cylinder ≃ₘ⟮CylinderI, CylinderI⟯ Cylinder :=
  (Diffeomorph.refl (𝓡 2) SphereTwo ∞).prodCongr (lineMul c hc)

@[simp] private theorem lineMul_apply (c : ℝ) (hc : c ≠ 0) (s : ℝ) :
    lineMul c hc s = c * s := rfl

@[simp] private theorem lineScale_apply (c : ℝ) (hc : c ≠ 0) (x : Cylinder) :
    lineScale c hc x = (x.1, c * x.2) := rfl

private theorem lineMul_mfderiv (c : ℝ) (hc : c ≠ 0) (s : ℝ) :
    mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (lineMul c hc : ℝ → ℝ) s =
      (LinearEquiv.smulOfNeZero ℝ ℝ c hc).toContinuousLinearEquiv.toContinuousLinearMap := by
  rw [mfderiv_eq_fderiv]
  change fderiv ℝ
    (((LinearEquiv.smulOfNeZero ℝ ℝ c hc).toContinuousLinearEquiv.toContinuousLinearMap :
      ℝ →L[ℝ] ℝ) : ℝ → ℝ) s = _
  exact ((LinearEquiv.smulOfNeZero ℝ ℝ c hc).toContinuousLinearEquiv.toContinuousLinearMap).fderiv

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem lineMul_pullback_euclidean (c : ℝ) (hc : c ≠ 0) :
    Diffeomorph.pullbackMetric (euclideanMetric (E := ℝ)) (lineMul c hc) =
      scaleMetric (c ^ 2) (sq_pos_of_ne_zero hc) (euclideanMetric (E := ℝ)) := by
  apply SmoothRiemannianMetric.ext_inner
  intro s v w
  rw [Diffeomorph.pullbackMetric_inner, lineMul_mfderiv, scaleMetric_inner,
    euclideanMetric_inner, euclideanMetric_inner]
  change inner ℝ (c • v) (c • w) = c ^ 2 * inner ℝ v w
  rw [real_inner_smul_left, real_inner_smul_right]
  ring

private theorem roundTwoSphereShrinkerMetric_eq_scaleMetric :
    roundTwoSphereShrinkerMetric =
      scaleMetric 2 (by norm_num)
        (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  simp only [roundTwoSphereShrinkerMetric, roundSphereShrinkerMetric, scaleMetric_inner,
    roundSphereShrinkerRadius_sq (by decide : 2 ≤ 2)]
  norm_num


private theorem mem_orbit_bot_iff {X : Type*} [MulAction (Equiv.Perm X) X] (a b : X) :
    a ∈ MulAction.orbit (⊥ : Subgroup (Equiv.Perm X)) b ↔ a = b := by
  constructor
  · rintro ⟨g, rfl⟩
    have hg : g = 1 := Subtype.ext (Subgroup.mem_bot.mp g.property)
    simp [hg]
  · intro h
    rw [h]
    exact MulAction.mem_orbit_self b

private theorem mem_orbit_cylinderAntipodalGroup_iff {a b : Cylinder} :
    a ∈ MulAction.orbit cylinderAntipodalGroup b ↔
      a = b ∨ a = DifferentialGeometry.Geometry.cylinderAntipodalDiffeomorph b := by
  constructor
  · rintro ⟨g, rfl⟩
    rcases cylinderAntipodalGroup_eq_one_or_generator g with h | h
    · left
      change g.1 b = b
      rw [h]
      rfl
    · right
      change g.1 b = DifferentialGeometry.Geometry.cylinderAntipodalDiffeomorph b
      rw [h]
      rfl
  · rintro (ha | h)
    · rw [ha]
      exact MulAction.mem_orbit_self b
    · rw [h]
      exact ⟨cylinderAntipodalGroupGenerator, cylinderAntipodalGroupGenerator_smul b⟩

private theorem mem_orbit_cylinderDiagonalGroup_iff {a b : Cylinder} :
    a ∈ MulAction.orbit cylinderDiagonalGroup b ↔
      a = b ∨ a = DifferentialGeometry.Geometry.cylinderDiagonalDiffeomorph b := by
  constructor
  · rintro ⟨g, rfl⟩
    rcases cylinderDiagonalGroup_eq_one_or_generator g with h | h
    · left
      change g.1 b = b
      rw [h]
      rfl
    · right
      change g.1 b = DifferentialGeometry.Geometry.cylinderDiagonalDiffeomorph b
      rw [h]
      rfl
  · rintro (ha | h)
    · rw [ha]
      exact MulAction.mem_orbit_self b
    · rw [h]
      exact ⟨cylinderDiagonalGroupGenerator, cylinderDiagonalGroupGenerator_smul b⟩

section Glue

omit [CompleteSpace E] [NoncompactSpace M] in
theorem exists_universalCover_cylinder_isometry_of_solitonModelCovering
    {sigma : ℝ} (hsigma : 0 < sigma)
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; ℝ⟯}
    {cover : Cylinder → M}
    (hcover : solitonModelCovering roundThreeCylinderShrinkerMetric
      roundThreeCylinderShrinkerPotential (scaleMetric sigma hsigma g) f cover) :
    ∃ Psi : Cylinder ≃ₘ⟮CylinderI, I⟯ UniversalCover M,
      (∀ (x : SphereTwo) (s : ℝ) (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
        (UniversalCover.liftedMetric (I := I) g).inner (Psi (x, s))
            (mfderiv CylinderI I Psi (x, s) (v, a))
            (mfderiv CylinderI I Psi (x, s) (w, b)) =
          (2 / sigma) * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner
            x v w + a * b) ∧
      ((∀ p q : Cylinder,
          UniversalCover.proj (Psi p) = UniversalCover.proj (Psi q) ↔ q = p) ∨
        (∀ p q : Cylinder,
          UniversalCover.proj (Psi p) = UniversalCover.proj (Psi q) ↔
            q = p ∨ q = (-p.1, p.2)) ∨
        (∀ p q : Cylinder,
          UniversalCover.proj (Psi p) = UniversalCover.proj (Psi q) ↔
            q = p ∨ q = (-p.1, -p.2))) := by
  let _ : SimplyConnectedSpace Cylinder :=
    DifferentialGeometry.Topology.simplyConnectedSpace_sphereTwo_prod_real
  let _ : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace Cylinder :=
    DifferentialGeometry.Topology.Manifold.locallyPathConnectedSpace_of_modelWithCorners CylinderI
  have hcovercov : IsCoveringMap cover := solitonModelCovering_isCoveringMap hcover
  have hcoverloc : IsLocalDiffeomorph CylinderI I ∞ cover :=
    solitonModelCovering_isLocalDiffeomorph hcover
  have hcoversmooth : ContMDiff CylinderI I ∞ cover := solitonModelCovering_contMDiff hcover
  let p₀ : Cylinder := (sphereEquator 0, 0)
  let n₀ : UniversalCover M :=
    ⟨cover p₀, Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath (default : M) (cover p₀))⟩
  have hn₀ : UniversalCover.proj n₀ = cover p₀ := rfl
  obtain ⟨F, hF0, hFproj, hFsmooth⟩ :=
    DifferentialGeometry.Topology.exists_smooth_lift_of_simplyConnected
      (UniversalCover.proj_isCoveringMap (X := M))
      (UniversalCover.proj_localDiffeo (I := I))
      cover hcoversmooth p₀ n₀ hn₀
  obtain ⟨G, hG0, hGproj, hGsmooth⟩ :=
    DifferentialGeometry.Topology.exists_smooth_lift_of_simplyConnected
      hcovercov hcoverloc
      (UniversalCover.proj (X := M)) (UniversalCover.proj_contMDiff (I := I))
      n₀ p₀ hn₀.symm
  have hfunF : (fun x : Cylinder => UniversalCover.proj (F x)) = cover :=
    funext fun x => hFproj x
  have hGF : (fun x : Cylinder => G (F x)) = id :=
    hcovercov.eq_of_comp_eq
      (G.continuous.comp F.continuous) continuous_id
      (funext fun x => by
        change cover (G (F x)) = cover x
        rw [hGproj (F x), hFproj x])
      p₀ (by change G (F p₀) = p₀; rw [hF0, hG0])
  have hFG : (fun y : UniversalCover M => F (G y)) = id :=
    (UniversalCover.proj_isCoveringMap (X := M)).eq_of_comp_eq
      (F.continuous.comp G.continuous) continuous_id
      (funext fun y => by
        change UniversalCover.proj (F (G y)) = UniversalCover.proj y
        rw [hFproj (G y), hGproj y])
      n₀ (by change F (G n₀) = n₀; rw [hG0, hF0])
  have hGF' : ∀ x : Cylinder, G (F x) = x := fun x => congrFun hGF x
  have hFG' : ∀ y : UniversalCover M, F (G y) = y := fun y => congrFun hFG y
  let Lift : Cylinder ≃ₘ⟮CylinderI, I⟯ UniversalCover M :=
    { toFun := F
      invFun := G
      left_inv := hGF'
      right_inv := hFG'
      contMDiff_toFun := hFsmooth
      contMDiff_invFun := hGsmooth }
  have hLift_proj : ∀ x : Cylinder, UniversalCover.proj (Lift x) = cover x := fun x => hFproj x
  let c : ℝ := Real.sqrt sigma
  have hc : c ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hsigma)
  let up : Cylinder ≃ₘ⟮CylinderI, CylinderI⟯ Cylinder := lineScale c hc
  let Psi : Cylinder ≃ₘ⟮CylinderI, I⟯ UniversalCover M := up.trans Lift
  have hcover_up : ∀ y : Cylinder, cover (up y) = UniversalCover.proj (Psi y) := by
    intro y
    simp only [Psi, Diffeomorph.coe_trans, Function.comp_apply]
    rw [hLift_proj]
  have hLift_pull : Diffeomorph.pullbackMetricCross (UniversalCover.liftedMetric (I := I) g)
      Lift = scaleMetric (1 / sigma) (by positivity) roundThreeCylinderShrinkerMetric := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [Diffeomorph.pullbackMetricCross_inner, scaleMetric_inner]
    change g.inner (UniversalCover.proj (Lift x)) (mfderiv CylinderI I Lift x v)
        (mfderiv CylinderI I Lift x w) = 1 / sigma * (roundThreeCylinderShrinkerMetric.inner x) v w
    rw [hLift_proj x]
    have hfff : UniversalCover.proj ∘ (Lift : Cylinder → UniversalCover M) = cover :=
      funext hLift_proj
    have hd : mfderiv CylinderI I Lift x = mfderiv CylinderI I cover x := by
      ext v
      have hcomp := mfderiv_comp_apply x
        (UniversalCover.hasMFDerivAt_proj (I := I) (Lift x)).mdifferentiableAt
        (Lift.mdifferentiable (by decide) x) v
      rw [(UniversalCover.hasMFDerivAt_proj (I := I) (Lift x)).mfderiv, hfff] at hcomp
      exact hcomp.symm
    rw [hd]
    have hm := solitonModelCovering_metric hcover x v w
    rw [scaleMetric_inner] at hm
    rw [hm, one_div, inv_mul_cancel_left₀ (ne_of_gt hsigma)]
    rfl
  have hup_pull : Diffeomorph.pullbackMetricCross roundThreeCylinderShrinkerMetric up =
      roundTwoSphereShrinkerMetric.prod (scaleMetric sigma hsigma (euclideanMetric (E := ℝ))) := by
    rw [Diffeomorph.pullbackMetricCross_eq_pullbackMetric]
    dsimp only [up, lineScale, c]
    rw [roundThreeCylinderShrinkerMetric, Diffeomorph.pullbackMetric_prodCongr,
      Diffeomorph.pullbackMetric_refl, lineMul_pullback_euclidean]
    simp only [Real.sq_sqrt hsigma.le]
  have key : ∀ (p : Cylinder) (V W : TangentSpace CylinderI p),
      (Diffeomorph.pullbackMetricCross (UniversalCover.liftedMetric (I := I) g) Psi).inner p V W =
        (1 / sigma) * (2 * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner
          p.1 V.1 W.1 + sigma * (V.2 * W.2)) := by
    intro p V W
    simp only [Psi]
    rw [← Diffeomorph.pullbackMetricCross_trans (UniversalCover.liftedMetric (I := I) g) up Lift,
      hLift_pull, DifferentialGeometry.Diffeomorph.pullbackMetricCross_scaleMetric, hup_pull]
    rw [scaleMetric_inner, SmoothRiemannianMetric.prod_inner]
    have h1 : (roundTwoSphereShrinkerMetric.inner p.1) V.1 W.1 =
        2 * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner p.1 V.1 W.1 := by
      rw [roundTwoSphereShrinkerMetric_eq_scaleMetric]
      rfl
    have h2 : ((scaleMetric sigma hsigma (euclideanMetric (E := ℝ))).inner p.2) V.2 W.2 =
        sigma * (V.2 * W.2) := by
      change sigma * inner ℝ V.2 W.2 = sigma * (V.2 * W.2)
      rw [Real.inner_apply]
    rw [h1, h2]
  have hmetric : ∀ (x : SphereTwo) (s : ℝ) (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
      (UniversalCover.liftedMetric (I := I) g).inner (Psi (x, s))
          (mfderiv CylinderI I Psi (x, s) (v, a))
          (mfderiv CylinderI I Psi (x, s) (w, b)) =
        (2 / sigma) * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner
          x v w + a * b := by
    intro x s v w a b
    rw [← Diffeomorph.pullbackMetricCross_inner (UniversalCover.liftedMetric (I := I) g)
      Psi (x, s) (v, a) (w, b)]
    rw [key (x, s) (v, a) (w, b)]
    field_simp
  rcases solitonModelCovering_roundThreeCylinder_target_isometry_trichotomy hcover with
    ⟨hgrp, -⟩ | ⟨hgrp, -⟩ | ⟨hgrp, -⟩
  · refine ⟨Psi, hmetric, Or.inl ?_⟩
    intro p q
    rw [← hcover_up p, ← hcover_up q,
      coveringDeckGroup_apply_eq_iff hcovercov, hgrp, mem_orbit_bot_iff]
    exact ⟨fun h => (up.injective h).symm, fun h => by rw [h]⟩
  · refine ⟨Psi, hmetric, Or.inr (Or.inl ?_)⟩
    intro p q
    rw [← hcover_up p, ← hcover_up q,
      coveringDeckGroup_apply_eq_iff hcovercov, hgrp, mem_orbit_cylinderAntipodalGroup_iff]
    constructor
    · rintro (h | h)
      · left
        exact (up.injective h).symm
      · right
        have hup : up p = (p.1, c * p.2) := by simp [up]
        have huq : up q = (q.1, c * q.2) := by simp [up]
        rw [hup, huq, cylinderAntipodalDiffeomorph_apply, cylinderAntipodal_apply] at h
        have hf := congrArg Prod.fst h
        have hs := congrArg Prod.snd h
        apply Prod.ext
        · have hneg := congrArg Neg.neg hf
          simpa using hneg.symm
        · exact mul_left_cancel₀ hc hs.symm
    · rintro (h | h)
      · left
        rw [h]
      · right
        rw [h]
        apply Prod.ext
        · simp only [up, lineScale_apply, cylinderAntipodalDiffeomorph_apply,
            cylinderAntipodal_apply, neg_neg]
        · simp only [up, lineScale_apply, cylinderAntipodalDiffeomorph_apply,
            cylinderAntipodal_apply]
  · refine ⟨Psi, hmetric, Or.inr (Or.inr ?_)⟩
    intro p q
    rw [← hcover_up p, ← hcover_up q,
      coveringDeckGroup_apply_eq_iff hcovercov, hgrp, mem_orbit_cylinderDiagonalGroup_iff]
    constructor
    · rintro (h | h)
      · left
        exact (up.injective h).symm
      · right
        have hup : up p = (p.1, c * p.2) := by simp [up]
        have huq : up q = (q.1, c * q.2) := by simp [up]
        rw [hup, huq, DifferentialGeometry.Geometry.cylinderDiagonalDiffeomorph_apply,
          DifferentialGeometry.Geometry.cylinderDiagonal_apply] at h
        have hf := congrArg Prod.fst h
        have hs := congrArg Prod.snd h
        apply Prod.ext
        · have hneg := congrArg Neg.neg hf
          simpa using hneg.symm
        · have hneg : c * q.2 = c * (-p.2) := by
            have h' := congrArg Neg.neg hs
            rw [neg_neg, ← mul_neg] at h'
            exact h'.symm
          exact mul_left_cancel₀ hc hneg
    · rintro (h | h)
      · left
        rw [h]
      · right
        rw [h]
        apply Prod.ext
        · simp only [up, lineScale_apply, DifferentialGeometry.Geometry.cylinderDiagonalDiffeomorph_apply,
            DifferentialGeometry.Geometry.cylinderDiagonal_apply, neg_neg]
        · simp only [up, lineScale_apply, DifferentialGeometry.Geometry.cylinderDiagonalDiffeomorph_apply,
            DifferentialGeometry.Geometry.cylinderDiagonal_apply]
          ring

end Glue

theorem complete_noncompact_three_shrinker_universal_cover_fibres
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯)
    {sigma : ℝ} (hsigma : 0 < sigma) (hdim : Module.finrank ℝ E = 3)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsoliton : gradientRicciSoliton (I := I) g f sigma)
    (hnonflat : ∃ x : M, metricScalarAt (I := I) g x ≠ 0) :
    ∃ Psi : (SphereTwo × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover M,
      (∀ (x : SphereTwo) (s : ℝ) (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
        (UniversalCover.liftedMetric (I := I) g).inner (Psi (x, s))
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (x, s) (v, a))
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (x, s) (w, b)) =
          (2 / sigma) * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner
            x v w + a * b) ∧
      ((∀ p q : SphereTwo × ℝ,
          UniversalCover.proj (Psi p) = UniversalCover.proj (Psi q) ↔ q = p) ∨
        (∀ p q : SphereTwo × ℝ,
          UniversalCover.proj (Psi p) = UniversalCover.proj (Psi q) ↔
            q = p ∨ q = (-p.1, p.2)) ∨
        (∀ p q : SphereTwo × ℝ,
          UniversalCover.proj (Psi p) = UniversalCover.proj (Psi q) ↔
            q = p ∨ q = (-p.1, -p.2))) := by
  obtain ⟨C, ⟨hC, hnorm⟩, -⟩ :=
    gradientRicciSoliton_existsUnique_normalized (I := I) hcomplete hsoliton hsigma
  rcases normalizedGradientRicciSoliton_solitonModelCovering_classification (I := I)
    hnorm hdim with ⟨hg, -, -⟩ | ⟨hs, -, -⟩ | ⟨hc, -, -⟩
  · obtain ⟨cover, hcover⟩ := hg
    exfalso
    obtain ⟨e, he, -⟩ :=
      (exists_solitonModelCovering_gaussian_iff (I := I)
        (V := EuclideanSpace ℝ (Fin 3))).mp ⟨cover, hcover⟩
    obtain ⟨x, hx⟩ := hnonflat
    have hRic : ∀ v w : TangentSpace I x,
        ricciTensor (I := I) (scaleMetric (I := I) sigma hsigma g) x v w = 0 := by
      intro v w
      rw [← he, ricciTensor_pullbackCross]
      exact euclideanMetric_ricciTensor (e x) _ _
    have hzero : metricScalarAt (I := I) (scaleMetric (I := I) sigma hsigma g) x = 0 :=
      metricScalarAt_eq_zero_of_ricciTensor_eq_zero _ x hRic
    rw [metricScalarAt_scaleMetric] at hzero
    exact hx ((mul_eq_zero.mp hzero).resolve_left (inv_ne_zero hsigma.ne'))
  · obtain ⟨cover, hcover⟩ := hs
    exact absurd (compactSpace_of_solitonModelCovering (I := I) hcover)
      (not_compactSpace_iff.mpr inferInstance)
  · obtain ⟨cover, hcover⟩ := hc
    exact exists_universalCover_cylinder_isometry_of_solitonModelCovering (I := I) hsigma hcover

theorem complete_noncompact_three_shrinker_universal_cover_cylinder
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯)
    {sigma : ℝ} (hsigma : 0 < sigma) (hdim : Module.finrank ℝ E = 3)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsoliton : gradientRicciSoliton (I := I) g f sigma)
    (hnonflat : ∃ x : M, metricScalarAt (I := I) g x ≠ 0) :
    ∃ Psi : (SphereTwo × ℝ) ≃ₘ⟮(𝓡 2).prod 𝓘(ℝ, ℝ), I⟯ UniversalCover M,
      ∀ (x : SphereTwo) (s : ℝ) (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
        (UniversalCover.liftedMetric (I := I) g).inner (Psi (x, s))
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (x, s) (v, a))
            (mfderiv ((𝓡 2).prod 𝓘(ℝ, ℝ)) I Psi (x, s) (w, b)) =
          (2 / sigma) * (roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)).inner
            x v w + a * b := by
  obtain ⟨Psi, hmetric, _⟩ := complete_noncompact_three_shrinker_universal_cover_fibres
    g f hsigma hdim hcomplete hsoliton hnonflat
  exact ⟨Psi, hmetric⟩

end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
