import DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCoverScaling
import DifferentialGeometry.Geometry.Metric.RicciSoliton.ModelCoverCylinderClassification
import DifferentialGeometry.Geometry.Metric.RicciSoliton.UniversalCover
import DifferentialGeometry.Geometry.Metric.UniversalCover.Metric
import DifferentialGeometry.Topology.Covering.CylinderQuotientModels
import DifferentialGeometry.Topology.Covering.CylindricalModel
import DifferentialGeometry.Topology.Manifold.LocallyPathConnected

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

open Bundle
open DifferentialGeometry
open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Riemannian.Topology
open scoped Manifold ContDiff

local notation "SphereTwo" => Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1
local notation "Cylinder" => SphereTwo × ℝ
local notation "CylinderI" => ModelWithCorners.prod (𝓡 2) 𝓘(ℝ, ℝ)
local notation "gS" => roundMetric (E := EuclideanSpace ℝ (Fin 3)) (n := 2)

private local instance w5cSphereDimension :
    Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin 3)) = 2 + 1) := ⟨by simp⟩

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

private theorem lineScale_pullback_prod (c : ℝ) (hc : c ≠ 0)
    (g : SmoothRiemannianMetric (𝓡 2) SphereTwo) :
    Diffeomorph.pullbackMetric (g.prod (euclideanMetric (E := ℝ))) (lineScale c hc) =
      g.prod (scaleMetric (c ^ 2) (sq_pos_of_ne_zero hc) (euclideanMetric (E := ℝ))) := by
  rw [lineScale, Diffeomorph.pullbackMetric_prodCongr, Diffeomorph.pullbackMetric_refl,
    lineMul_pullback_euclidean]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
set_option backward.isDefEq.respectTransparency false in
private theorem scaleMetric_prod {E₂ : Type*} [NormedAddCommGroup E₂] [NormedSpace ℝ E₂]
    [FiniteDimensional ℝ E₂] {H₂ : Type*} [TopologicalSpace H₂]
    {J : ModelWithCorners ℝ E₂ H₂} [J.Boundaryless]
    {N : Type*} [TopologicalSpace N] [ChartedSpace H₂ N] [IsManifold J ∞ N] [T2Space N]
    (c : ℝ) (hc : 0 < c) (g : SmoothRiemannianMetric (𝓡 2) SphereTwo)
    (h : SmoothRiemannianMetric J N) :
    scaleMetric c hc (g.prod h) = (scaleMetric c hc g).prod (scaleMetric c hc h) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  simp only [scaleMetric_inner, SmoothRiemannianMetric.prod_inner]
  ring

set_option backward.isDefEq.respectTransparency false in
private theorem scaleMetric_scaleMetric {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] {H' : Type*} [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M'] [T2Space M']
    (c d : ℝ) (hc : 0 < c) (hd : 0 < d) (g : SmoothRiemannianMetric I' M') :
    scaleMetric c hc (scaleMetric d hd g) = scaleMetric (c * d) (mul_pos hc hd) g := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [scaleMetric_inner, scaleMetric_inner, scaleMetric_inner]
  ring

set_option backward.isDefEq.respectTransparency false in
private theorem scaleMetric_one {E' : Type*} [NormedAddCommGroup E']
    [NormedSpace ℝ E'] [FiniteDimensional ℝ E'] {H' : Type*} [TopologicalSpace H']
    {I' : ModelWithCorners ℝ E' H'} [I'.Boundaryless]
    {M' : Type*} [TopologicalSpace M'] [ChartedSpace H' M'] [IsManifold I' ∞ M'] [T2Space M']
    (g : SmoothRiemannianMetric I' M') :
    scaleMetric 1 (by norm_num) g = g := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [scaleMetric_inner, one_mul]

private theorem roundTwoSphereShrinkerMetric_eq (h2 : 0 < (2 : ℝ)) :
    roundTwoSphereShrinkerMetric = scaleMetric (2 : ℝ) h2 (gS) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  simp only [roundTwoSphereShrinkerMetric, roundSphereShrinkerMetric, scaleMetric_inner,
    roundSphereShrinkerRadius_two, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]


variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [NoncompactSpace M]
  [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M] [Inhabited M]

private local instance w5dManifoldOne : IsManifold I 1 M := IsManifold.of_le (n := ∞) (by decide)


def NoncompactShrinkerCylinderClassification
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) (sigma : ℝ) : Prop :=
  ∃ (C : ℝ) (Psi : Cylinder ≃ₘ⟮CylinderI, I⟯ UniversalCover M),
    (∀ (x : SphereTwo) (s : ℝ) (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
      (UniversalCover.liftedMetric (I := I) g).inner (Psi (x, s))
          (mfderiv CylinderI I Psi (x, s) (v, a))
          (mfderiv CylinderI I Psi (x, s) (w, b)) =
        (2 / sigma) * (gS).inner x v w + a * b) ∧
    (∀ (x : SphereTwo) (s : ℝ),
      f (UniversalCover.proj (Psi (x, s))) + C / sigma = 1 + sigma * s ^ 2 / 4)

def NoncompactShrinkerCylinderClassificationTheorem.{uE, uH, uM} : Prop :=
  ∀ {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type uM} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SigmaCompactSpace M] [ConnectedSpace M] [NoncompactSpace M]
    [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M] [Inhabited M]
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯) {sigma : ℝ},
    0 < sigma → Module.finrank ℝ E = 3 →
      RiemannianMetricComplete (I := I) g → gradientRicciSoliton (I := I) g f sigma →
        (∃ x : M, metricScalarAt (I := I) g x ≠ 0) →
          NoncompactShrinkerCylinderClassification (I := I) (M := M) g f sigma

omit [FiniteDimensional ℝ E] [CompleteSpace E] [I.Boundaryless] [T2Space M]
  [SigmaCompactSpace M] [ConnectedSpace M]
  [NoncompactSpace M] [LocallyPathConnectedSpace M] [SemilocallySimplyConnectedSpace M]
  [Inhabited M] in
set_option backward.isDefEq.respectTransparency false in
private theorem localPullMetric_comp_diffeomorph
    {E₁ : Type*} [NormedAddCommGroup E₁] [NormedSpace ℝ E₁] [FiniteDimensional ℝ E₁]
    {H₁ : Type*} [TopologicalSpace H₁] {I₁ : ModelWithCorners ℝ E₁ H₁} [I₁.Boundaryless]
    {N₁ : Type*} [TopologicalSpace N₁] [ChartedSpace H₁ N₁] [IsManifold I₁ ∞ N₁] [T2Space N₁]
    (g : SmoothRiemannianMetric I M) (Phi : N₁ → M) (hPhi : IsLocalDiffeomorph I₁ I ∞ Phi)
    (e : Cylinder ≃ₘ⟮CylinderI, I₁⟯ N₁) :
    localPullMetric g (Phi ∘ e) (isLocalDiffeomorph_comp hPhi e.isLocalDiffeomorph) =
      Diffeomorph.pullbackMetricCross (localPullMetric g Phi hPhi) e := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [localPullMetric_inner, Diffeomorph.pullbackMetricCross_inner, localPullMetric_inner,
    mfderiv_comp x (hPhi.contMDiff.mdifferentiableAt (by simp))
      (e.contMDiff.mdifferentiableAt (by simp))]
  rfl

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


omit [NoncompactSpace M] in
set_option backward.isDefEq.respectTransparency false in
theorem complete_noncompact_three_shrinker_universal_cover_fibres_of_classification
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯)
    {sigma : ℝ} (hsigma : 0 < sigma) (_hdim : Module.finrank ℝ E = 3)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (_hsoliton : gradientRicciSoliton (I := I) g f sigma)
    (_hnonflat : ∃ x : M, metricScalarAt (I := I) g x ≠ 0)
    (hclass : NoncompactShrinkerCylinderClassification (I := I) (M := M) g f sigma) :
    ∃ Psi : Cylinder ≃ₘ⟮CylinderI, I⟯ UniversalCover M,
      (∀ (x : SphereTwo) (s : ℝ) (v w : TangentSpace (𝓡 2) x) (a b : ℝ),
        (UniversalCover.liftedMetric (I := I) g).inner (Psi (x, s))
            (mfderiv CylinderI I Psi (x, s) (v, a))
            (mfderiv CylinderI I Psi (x, s) (w, b)) =
          (2 / sigma) * (gS).inner x v w + a * b) ∧
      ((∀ p q : Cylinder,
          UniversalCover.proj (Psi p) = UniversalCover.proj (Psi q) ↔ q = p) ∨
        (∀ p q : Cylinder,
          UniversalCover.proj (Psi p) = UniversalCover.proj (Psi q) ↔
            q = p ∨ q = (-p.1, p.2)) ∨
        (∀ p q : Cylinder,
          UniversalCover.proj (Psi p) = UniversalCover.proj (Psi q) ↔
            q = p ∨ q = (-p.1, -p.2))) := by
  obtain ⟨C, Psi, hmetric, hpotential⟩ := hclass
  have hspos : 0 < Real.sqrt sigma := Real.sqrt_pos.mpr hsigma
  have hsne : Real.sqrt sigma ≠ 0 := ne_of_gt hspos
  have hsneinv : (Real.sqrt sigma)⁻¹ ≠ 0 := inv_ne_zero hsne
  let up : Cylinder ≃ₘ⟮CylinderI, CylinderI⟯ Cylinder := lineScale (Real.sqrt sigma) hsne
  let down : Cylinder ≃ₘ⟮CylinderI, CylinderI⟯ Cylinder := lineScale ((Real.sqrt sigma)⁻¹) hsneinv
  let PsiM : Cylinder → M := fun y => UniversalCover.proj (Psi y)
  let cover : Cylinder → M := PsiM ∘ down
  have hPsiM : IsLocalDiffeomorph CylinderI I ∞ PsiM :=
    isLocalDiffeomorph_comp (UniversalCover.proj_localDiffeo (I := I)) Psi.isLocalDiffeomorph
  have hcoverld : IsLocalDiffeomorph CylinderI I ∞ cover :=
    isLocalDiffeomorph_comp hPsiM down.isLocalDiffeomorph
  have hprojSurj : Function.Surjective (UniversalCover.proj (X := M)) := by
    let _ : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
    intro x
    exact ⟨⟨x, Path.Homotopic.Quotient.mk
      (PathConnectedSpace.somePath (default : M) x)⟩, rfl⟩
  have hcoverSurj : Function.Surjective cover :=
    (hprojSurj.comp Psi.surjective).comp down.surjective
  have hcoverCov : IsCoveringMap cover :=
    ((UniversalCover.proj_isCoveringMap (X := M)).comp_homeomorph
      Psi.toHomeomorph).comp_homeomorph down.toHomeomorph
  have hPsi_pull : Diffeomorph.pullbackMetricCross (UniversalCover.liftedMetric (I := I) g) Psi =
      (scaleMetric (2 / sigma) (by positivity) (gS)).prod (euclideanMetric (E := ℝ)) := by
    apply SmoothRiemannianMetric.ext_inner
    rintro ⟨a, s⟩ ⟨v₁, v₂⟩ ⟨w₁, w₂⟩
    have hline : inner ℝ v₂ w₂ = v₂ * w₂ := by
      simp [RCLike.inner_apply, mul_comm]
    rw [Diffeomorph.pullbackMetricCross_inner, hmetric a s v₁ w₁ v₂ w₂,
      SmoothRiemannianMetric.prod_inner, scaleMetric_inner, euclideanMetric_inner, hline]
  have hproj_pull : localPullMetric (scaleMetric sigma hsigma g)
      (UniversalCover.proj (X := M))
      (UniversalCover.proj_localDiffeo (I := I)) =
      scaleMetric sigma hsigma (UniversalCover.liftedMetric (I := I) g) := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [localPullMetric_inner, scaleMetric_inner, scaleMetric_inner,
      (UniversalCover.hasMFDerivAt_proj (I := I) x).mfderiv]
    exact congrArg (fun t => sigma * t)
      (UniversalCover.liftedMetric_inner_eq (I := I) g x v w)
  have hPsiM_pull : localPullMetric (scaleMetric sigma hsigma g) PsiM hPsiM =
      scaleMetric sigma hsigma
        (Diffeomorph.pullbackMetricCross (UniversalCover.liftedMetric (I := I) g) Psi) := by
    have h := localPullMetric_comp_diffeomorph (I := I) (M := M) (g := scaleMetric sigma hsigma g)
      (Phi := (UniversalCover.proj (X := M))) (UniversalCover.proj_localDiffeo (I := I)) Psi
    rw [hproj_pull, Diffeomorph.pullbackMetricCross_scaleMetric] at h
    exact h
  have hcover_pull : localPullMetric (scaleMetric sigma hsigma g) cover hcoverld =
      roundThreeCylinderShrinkerMetric := by
    have h := localPullMetric_comp_diffeomorph (I := I) (M := M) (g := scaleMetric sigma hsigma g)
      (Phi := PsiM) hPsiM down
    rw [hPsiM_pull, hPsi_pull] at h
    rw [Diffeomorph.pullbackMetricCross_scaleMetric] at h
    have hcoef : sigma * (2 / sigma) = 2 := by field_simp
    have hcoef2 : sigma * (Real.sqrt sigma)⁻¹ ^ 2 = 1 := by
      rw [inv_pow, Real.sq_sqrt hsigma.le]
      field_simp
    dsimp only [down, lineScale] at h
    rw [Diffeomorph.pullbackMetricCross_eq_pullbackMetric,
      Diffeomorph.pullbackMetric_prodCongr, Diffeomorph.pullbackMetric_refl,
      lineMul_pullback_euclidean, scaleMetric_prod, scaleMetric_scaleMetric,
      scaleMetric_scaleMetric] at h
    simp only [hcoef, hcoef2] at h
    rw [scaleMetric_one,
      ← roundTwoSphereShrinkerMetric_eq (by norm_num : (0 : ℝ) < 2)] at h
    rw [roundThreeCylinderShrinkerMetric]
    exact h
  let fhat : C^∞⟮I, M; ℝ⟯ := f + ContMDiffMap.const (I := I)
    (I' := modelWithCornersSelf ℝ ℝ) (M := M) (n := ∞) (C / sigma)
  have hcover_potential : ∀ x : Cylinder, roundThreeCylinderShrinkerPotential x =
      fhat (cover x) := by
    intro x
    have hscale : sigma * ((Real.sqrt sigma)⁻¹ * x.2) ^ 2 / 4 = x.2 ^ 2 / 4 := by
      rw [mul_pow, inv_pow, Real.sq_sqrt hsigma.le]
      field_simp
    have h := hpotential x.1 ((Real.sqrt sigma)⁻¹ * x.2)
    rw [roundThreeCylinderShrinkerPotential_apply]
    change 1 + x.2 ^ 2 / 4 = (f : M → ℝ) (cover x) + C / sigma
    dsimp only [cover, PsiM, Function.comp_apply, down, lineScale_apply]
    rw [h, hscale]
  have hmodel : solitonModelCovering roundThreeCylinderShrinkerMetric
      roundThreeCylinderShrinkerPotential (scaleMetric sigma hsigma g)
      fhat cover := by
    refine ⟨normalizedGradientRicciSoliton_roundThreeCylinder, ?_, hcoverld, hcoverSurj,
      hcoverCov, ?_, hcover_potential⟩
    · exact normalizedGradientRicciSoliton_of_surjective_localPullMetric
        (hsol := normalizedGradientRicciSoliton_roundThreeCylinder)
        (hcomplete := RiemannianMetricComplete.scaleMetric hcomplete sigma hsigma)
        (hPhi := hcoverld) (hsurj := hcoverSurj) (hpull := hcover_pull)
        (hpotential := hcover_potential)
    · intro x v w
      rw [← hcover_pull, localPullMetric_inner]
  have hSC : SimplyConnectedSpace Cylinder :=
    DifferentialGeometry.Topology.simplyConnectedSpace_sphereTwo_prod_real
  have hLPC : LocallyPathConnectedSpace Cylinder :=
    DifferentialGeometry.Topology.Manifold.locallyPathConnectedSpace_of_modelWithCorners CylinderI
  have hdown_up : ∀ y : Cylinder, down (up y) = y := by
    intro y
    dsimp only [up, down]
    rw [lineScale_apply, lineScale_apply]
    exact Prod.ext rfl (inv_mul_cancel_left₀ hsne y.2)
  have hcover_up : ∀ y : Cylinder, cover (up y) = UniversalCover.proj (Psi y) := by
    intro y
    dsimp only [cover, PsiM, Function.comp_apply]
    rw [hdown_up y]
  rcases solitonModelCovering_roundThreeCylinder_target_isometry_trichotomy hmodel with
    ⟨hgrp, _⟩ | ⟨hgrp, _⟩ | ⟨hgrp, _⟩
  · refine ⟨Psi, hmetric, Or.inl ?_⟩
    intro p q
    rw [← hcover_up p, ← hcover_up q,
      coveringDeckGroup_apply_eq_iff (solitonModelCovering_isCoveringMap hmodel), hgrp,
      mem_orbit_bot_iff]
    exact ⟨fun h => (up.injective h).symm, fun h => by rw [h]⟩
  · refine ⟨Psi, hmetric, Or.inr (Or.inl ?_)⟩
    intro p q
    rw [← hcover_up p, ← hcover_up q,
      coveringDeckGroup_apply_eq_iff (solitonModelCovering_isCoveringMap hmodel), hgrp,
      mem_orbit_cylinderAntipodalGroup_iff]
    constructor
    · rintro (h | h)
      · left
        exact (up.injective h).symm
      · right
        have hup : up p = (p.1, Real.sqrt sigma * p.2) := rfl
        have huq : up q = (q.1, Real.sqrt sigma * q.2) := rfl
        rw [hup, huq, cylinderAntipodalDiffeomorph_apply, cylinderAntipodal_apply] at h
        have hf := congrArg Prod.fst h
        have hs := congrArg Prod.snd h
        apply Prod.ext
        · have hneg := congrArg Neg.neg hf
          simpa using hneg.symm
        · exact mul_left_cancel₀ hsne hs.symm
    · rintro (h | h)
      · left
        rw [h]
      · right
        rw [h]
        apply Prod.ext
        · dsimp only [up]
          simp only [lineScale_apply, cylinderAntipodalDiffeomorph_apply,
            cylinderAntipodal_apply, neg_neg]
        · dsimp only [up]
          simp only [lineScale_apply, cylinderAntipodalDiffeomorph_apply,
            cylinderAntipodal_apply]
  · refine ⟨Psi, hmetric, Or.inr (Or.inr ?_)⟩
    intro p q
    rw [← hcover_up p, ← hcover_up q,
      coveringDeckGroup_apply_eq_iff (solitonModelCovering_isCoveringMap hmodel), hgrp,
      mem_orbit_cylinderDiagonalGroup_iff]
    constructor
    · rintro (h | h)
      · left
        exact (up.injective h).symm
      · right
        have hup : up p = (p.1, Real.sqrt sigma * p.2) := rfl
        have huq : up q = (q.1, Real.sqrt sigma * q.2) := rfl
        rw [hup, huq, DifferentialGeometry.Geometry.cylinderDiagonalDiffeomorph_apply,
          DifferentialGeometry.Geometry.cylinderDiagonal_apply] at h
        have hf := congrArg Prod.fst h
        have hs := congrArg Prod.snd h
        apply Prod.ext
        · have hneg := congrArg Neg.neg hf
          simpa using hneg.symm
        · have hneg := congrArg Neg.neg hs
          simp only [neg_neg] at hneg
          have hq : Real.sqrt sigma * q.2 = Real.sqrt sigma * (-p.2) := by
            rw [mul_neg]
            exact hneg.symm
          exact mul_left_cancel₀ hsne hq
    · rintro (h | h)
      · left
        rw [h]
      · right
        rw [h]
        apply Prod.ext
        · dsimp only [up]
          simp only [lineScale_apply, DifferentialGeometry.Geometry.cylinderDiagonalDiffeomorph_apply,
            DifferentialGeometry.Geometry.cylinderDiagonal_apply, neg_neg]
        · dsimp only [up]
          simp only [lineScale_apply, DifferentialGeometry.Geometry.cylinderDiagonalDiffeomorph_apply,
            DifferentialGeometry.Geometry.cylinderDiagonal_apply]
          ring


omit [NoncompactSpace M] in
theorem cylinderQuotientModels_of_classification
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; ℝ⟯)
    {sigma : ℝ} (hsigma : 0 < sigma) (hdim : Module.finrank ℝ E = 3)
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsoliton : gradientRicciSoliton (I := I) g f sigma)
    (hnonflat : ∃ x : M, metricScalarAt (I := I) g x ≠ 0)
    (hclass : NoncompactShrinkerCylinderClassification (I := I) (M := M) g f sigma) :
    ∃ Psi : Cylinder ≃ₘ⟮CylinderI, I⟯ UniversalCover M,
      CylinderQuotientModels (I := I) (fun p : Cylinder => UniversalCover.proj (Psi p)) := by
  obtain ⟨Psi, _hmetric, hfibres⟩ :=
    complete_noncompact_three_shrinker_universal_cover_fibres_of_classification
      g f hsigma hdim hcomplete hsoliton hnonflat hclass
  have hlocal : IsLocalDiffeomorph CylinderI I ∞
      (fun p : Cylinder => UniversalCover.proj (Psi p)) :=
    isLocalDiffeomorph_comp (UniversalCover.proj_localDiffeo (I := I)) Psi.isLocalDiffeomorph
  have hcover : IsCoveringMap (fun p : Cylinder => UniversalCover.proj (Psi p)) :=
    (UniversalCover.proj_isCoveringMap (X := M)).comp_homeomorph Psi.toHomeomorph
  have hsurj : Function.Surjective (fun p : Cylinder => UniversalCover.proj (Psi p)) := by
    let _ : PathConnectedSpace M := PathConnectedSpace.of_locallyPathConnectedSpace
    intro x
    exact ⟨Psi.symm ⟨x, Path.Homotopic.Quotient.mk
      (PathConnectedSpace.somePath (default : M) x)⟩,
      congrArg (UniversalCover.proj (X := M))
        (Psi.apply_symm_apply _)⟩
  exact ⟨Psi, cylinderQuotientModels_of_fibres _ hlocal hcover hsurj hfibres⟩


end DifferentialGeometry.PDE.RicciFlow.Perelman.KappaSolutions

end
