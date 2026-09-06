import DifferentialGeometry.Geometry.Metric.RicciSoliton.SurfaceClassification
import DifferentialGeometry.Geometry.Metric.ProjectiveSpace
import DifferentialGeometry.Geometry.Metric.PullbackScaling
import DifferentialGeometry.Geometry.Metric.Sphere.IsometryRepresentation

set_option autoImplicit false

noncomputable section

open Bundle Manifold
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

local instance : IsManifold (𝓡 2) ∞
    (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) := inferInstance

local instance : IsManifold (𝓡 2) ∞ RealProjectivePlane := inferInstance

private theorem roundTwoSphereShrinkerMetric_eq_scaleMetric :
    roundTwoSphereShrinkerMetric =
      scaleMetric 2 (by norm_num)
        (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  simp only [roundTwoSphereShrinkerMetric, roundSphereShrinkerMetric, scaleMetric_inner,
    roundSphereShrinkerRadius_sq (by decide : 2 ≤ 2)]
  norm_num

section Exclusivity

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] [FiniteDimensional Real F]
variable {H : Type*} [TopologicalSpace H] {I : ModelWithCorners Real F H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

theorem euclidean_round_projective_isometries_pairwise_exclusive
    (g : SmoothRiemannianMetric I M) {sigma : Real} (hsigma : 0 < sigma) :
    List.Pairwise (fun P Q : Prop => ¬ (P ∧ Q))
      [∃ e : M ≃ₘ⟮I, 𝓡 2⟯ EuclideanSpace Real (Fin 2),
        Diffeomorph.pullbackMetricCross euclideanMetric e = g,
      ∃ e : M ≃ₘ⟮I, 𝓡 2⟯ Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1,
        Diffeomorph.pullbackMetricCross
          (scaleMetric (2 / sigma) (div_pos (by norm_num) hsigma)
            (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) e = g,
      ∃ e : M ≃ₘ⟮I, 𝓡 2⟯ RealProjectivePlane,
        Diffeomorph.pullbackMetricCross
          (scaleMetric (2 / sigma) (div_pos (by norm_num) hsigma)
            (roundProjectiveMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) e = g] := by
  apply List.Pairwise.cons
  · intro P hP
    rcases List.mem_cons.mp hP with rfl | hP
    · rintro ⟨⟨e, _⟩, ⟨d, _⟩⟩
      let : CompactSpace M := d.symm.toHomeomorph.compactSpace
      exact (not_compactSpace_iff.mpr
        (inferInstance : NoncompactSpace (EuclideanSpace Real (Fin 2))))
        e.toHomeomorph.compactSpace
    · obtain rfl := List.mem_singleton.mp hP
      rintro ⟨⟨e, _⟩, ⟨d, _⟩⟩
      let : CompactSpace M := d.symm.toHomeomorph.compactSpace
      exact (not_compactSpace_iff.mpr
        (inferInstance : NoncompactSpace (EuclideanSpace Real (Fin 2))))
        e.toHomeomorph.compactSpace
  apply List.Pairwise.cons
  · intro P hP
    obtain rfl := List.mem_singleton.mp hP
    rintro ⟨⟨e, he⟩, ⟨d, hd⟩⟩
    let c := 2 / sigma
    have hc : 0 < c := div_pos (by norm_num) hsigma
    let Phi : RealProjectivePlane ≃ₘ⟮𝓡 2, 𝓡 2⟯
        Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 := d.symm.trans e
    have hscale : Diffeomorph.pullbackMetricCross
        (scaleMetric c hc (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) Phi =
      scaleMetric c hc (roundProjectiveMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) := by
      rw [show Phi = d.symm.trans e from rfl, ← Diffeomorph.pullbackMetricCross_trans, he]
      exact Diffeomorph.pullbackMetricCross_symm_eq_iff.mp hd
    rw [Diffeomorph.pullbackMetricCross_scaleMetric] at hscale
    apply not_exists_diffeomorph_pullbackMetric_roundProjectiveMetric
      (E := EuclideanSpace Real (Fin 3)) (n := 2) (by decide)
    refine ⟨Phi, ?_⟩
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    have hm := congrArg (fun k : SmoothRiemannianMetric (𝓡 2) RealProjectivePlane =>
      k.inner x v w) hscale
    simp only [scaleMetric_inner] at hm
    exact mul_left_cancel₀ hc.ne' hm
  apply List.Pairwise.cons
  · intro P hP
    exact False.elim (List.not_mem_nil hP)
  exact List.Pairwise.nil

end Exclusivity

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M] [ConnectedSpace M]

omit [ConnectedSpace M] in
private theorem pullbackMetric_roundProjective_of_solitonModelCovering
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {cover : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 → M}
    (hcover : solitonModelCovering roundTwoSphereShrinkerMetric
      roundTwoSphereShrinkerPotential g f cover)
    (Phi : RealProjectivePlane ≃ₘ⟮𝓡 2, I⟯ M)
    (hPhi : ∀ x, Phi (realProjectivePlaneQuotientMap x) = cover x) :
    Diffeomorph.pullbackMetricCross g Phi =
      scaleMetric 2 (by norm_num)
        (roundProjectiveMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) := by
  let q := realProjectivePlaneQuotientMap
  have hq : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ q :=
    realProjectiveSpaceQuotientMap_isLocalDiffeomorph
  have hqsurj : Function.Surjective q := realProjectivePlaneQuotientMap_surjective
  apply localPullMetric_injective_of_surjective q hq hqsurj
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  have hpi := solitonModelCovering_metric hcover x v w
  have hcovereq : cover = (Phi : RealProjectivePlane → M) ∘ q := (funext hPhi).symm
  rw [hcovereq] at hpi
  have hchain : mfderiv (𝓡 2) I ((Phi : RealProjectivePlane → M) ∘ q) x =
      (mfderiv (𝓡 2) I Phi (q x)).comp (mfderiv (𝓡 2) (𝓡 2) q x) :=
    mfderiv_comp x (Phi.contMDiff.mdifferentiableAt (by simp))
      (hq.contMDiff.mdifferentiableAt (by simp))
  rw [hchain, roundTwoSphereShrinkerMetric_eq_scaleMetric, scaleMetric_inner] at hpi
  simp only [ContinuousLinearMap.comp_apply] at hpi
  have hproj := congrArg
    (fun k : SmoothRiemannianMetric (𝓡 2)
      (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) => k.inner x v w)
    (localPullMetric_roundProjectiveMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))
  rw [localPullMetric_inner] at hproj
  rw [localPullMetric_inner, Diffeomorph.pullbackMetricCross_inner,
    localPullMetric_inner, scaleMetric_inner]
  exact hpi.symm.trans (congrArg (fun r : Real => 2 * r) hproj.symm)

private theorem normalizedGradientRicciSoliton_model_isometries_of_finrank_eq_two
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2) :
    (∃ e : E ≃ₘ⟮𝓘(Real, E), I⟯ M,
      Diffeomorph.pullbackMetricCross g e = euclideanMetric ∧
        ∀ x, f (e x) = gaussianPotential x) ∨
      (∃ e : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 ≃ₘ⟮𝓡 2, I⟯ M,
        Diffeomorph.pullbackMetricCross g e =
          scaleMetric 2 (by norm_num)
            (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) ∧
          ∀ x, f (e x) = 1) ∨
      (∃ e : RealProjectivePlane ≃ₘ⟮𝓡 2, I⟯ M,
        Diffeomorph.pullbackMetricCross g e =
          scaleMetric 2 (by norm_num)
            (roundProjectiveMetric (E := EuclideanSpace Real (Fin 3)) (n := 2)) ∧
          ∀ x, f (e x) = 1) := by
  obtain hGaussian | ⟨cover, hcover, _, hmodels⟩ :=
    exists_gaussian_or_roundTwoSphere_solitonModelQuotientCovering_with_target_homeomorphism_of_finrank_eq_two
      h hdim
  · obtain ⟨cover, hcover⟩ := hGaussian
    refine Or.inl ⟨gaussianSolitonModelCoveringDiffeomorph hcover,
      gaussianSolitonModelCoveringDiffeomorph_pullbackMetric hcover, ?_⟩
    intro x
    exact (solitonModelCovering_potential hcover x).symm
  rcases hmodels with ⟨e, he⟩ | ⟨e, he⟩
  · have hinj : Function.Injective cover := by
      intro x y hxy
      apply e.injective
      simpa only [he] using hxy
    let Phi : Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1 ≃ₘ⟮𝓡 2, I⟯ M :=
      (solitonModelCovering_isLocalDiffeomorph hcover).diffeomorphOfBijective
        ⟨hinj, solitonModelCovering_surjective hcover⟩
    refine Or.inr (Or.inl ⟨Phi, ?_, ?_⟩)
    · rw [← roundTwoSphereShrinkerMetric_eq_scaleMetric]
      apply SmoothRiemannianMetric.ext_inner
      intro x v w
      rw [Diffeomorph.pullbackMetricCross_inner]
      exact (solitonModelCovering_metric hcover x v w).symm
    · intro x
      exact (solitonModelCovering_potential hcover x).symm
  · let q := realProjectivePlaneQuotientMap
    have hq : IsLocalDiffeomorph (𝓡 2) (𝓡 2) ∞ q :=
      realProjectiveSpaceQuotientMap_isLocalDiffeomorph
    have hqsurj : Function.Surjective q := realProjectivePlaneQuotientMap_surjective
    have hcomp : (e : RealProjectivePlane → M) ∘ q = cover := funext he
    have heSmooth : ContMDiff (𝓡 2) I ∞ (e : RealProjectivePlane → M) :=
      hq.contMDiff_of_comp_of_surjective hqsurj
        (by rw [hcomp]; exact solitonModelCovering_contMDiff hcover)
    have hcompInv : (e.symm : M → RealProjectivePlane) ∘ cover = q := by
      funext x
      simp only [Function.comp_apply, ← he x, e.symm_apply_apply, q]
    have heInvSmooth : ContMDiff I (𝓡 2) ∞ (e.symm : M → RealProjectivePlane) :=
      (solitonModelCovering_isLocalDiffeomorph hcover).contMDiff_of_comp_of_surjective
        (solitonModelCovering_surjective hcover) (by rw [hcompInv]; exact hq.contMDiff)
    let Phi : RealProjectivePlane ≃ₘ⟮𝓡 2, I⟯ M :=
      { toEquiv := e.toEquiv
        contMDiff_toFun := heSmooth
        contMDiff_invFun := heInvSmooth }
    refine Or.inr (Or.inr ⟨Phi, ?_, ?_⟩)
    · exact pullbackMetric_roundProjective_of_solitonModelCovering hcover Phi he
    · intro y
      obtain ⟨x, rfl⟩ := hqsurj y
      have hp := solitonModelCovering_potential hcover x
      change 1 = f (cover x) at hp
      exact (hp.trans (congrArg f (he x).symm)).symm

omit [I.Boundaryless] [SigmaCompactSpace M] [ConnectedSpace M] in
private theorem exists_gaussian_isometry_of_scaled_pullbackMetric
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    {sigma a : Real} (hsigma : 0 < sigma) (hdim : Module.finrank Real E = 2)
    (e : E ≃ₘ⟮𝓘(Real, E), I⟯ M)
    (hmetric : Diffeomorph.pullbackMetricCross (scaleMetric sigma hsigma g) e =
      euclideanMetric)
    (hpotential : ∀ x, f (e x) + a = gaussianPotential x) :
    ∃ Phi : M ≃ₘ⟮I, 𝓡 2⟯ EuclideanSpace Real (Fin 2),
      Diffeomorph.pullbackMetricCross euclideanMetric Phi = g ∧
        ∀ x, f x + a = sigma * ‖Phi x‖ ^ 2 / 4 := by
  let L : E ≃ₗᵢ[Real] EuclideanSpace Real (Fin 2) :=
    ((stdOrthonormalBasis Real E).reindex (finCongr hdim)).repr
  let r := Real.sqrt sigma
  have hr : 0 < r := Real.sqrt_pos.2 hsigma
  have hrSq : r ^ 2 = sigma := Real.sq_sqrt hsigma.le
  let T : EuclideanSpace Real (Fin 2) ≃L[Real] E :=
    L.symm.toContinuousLinearEquiv.trans
      ((LinearEquiv.smulOfNeZero Real E r hr.ne').toContinuousLinearEquiv)
  have hT (x : EuclideanSpace Real (Fin 2)) : T x = r • L.symm x := rfl
  have hTinner (v w : EuclideanSpace Real (Fin 2)) :
      inner Real (T v) (T w) = sigma * inner Real v w := by
    rw [hT, hT, real_inner_smul_left, real_inner_smul_right, L.symm.inner_map_map]
    rw [← mul_assoc, ← sq, hrSq]
  have hTnorm (x : EuclideanSpace Real (Fin 2)) : ‖T x‖ ^ 2 = sigma * ‖x‖ ^ 2 := by
    rw [hT, norm_smul, Real.norm_eq_abs, abs_of_pos hr, L.symm.norm_map, mul_pow, hrSq]
  have hderiv (x : EuclideanSpace Real (Fin 2)) :
      mfderiv (𝓡 2) 𝓘(Real, E) T.toDiffeomorph x = T.toContinuousLinearMap := by
    rw [mfderiv_eq_fderiv]
    change fderiv Real (T.toContinuousLinearMap : EuclideanSpace Real (Fin 2) → E) x = _
    exact T.toContinuousLinearMap.fderiv
  let Psi : EuclideanSpace Real (Fin 2) ≃ₘ⟮𝓡 2, I⟯ M := T.toDiffeomorph.trans e
  have hPsi : Diffeomorph.pullbackMetricCross g Psi = euclideanMetric := by
    rw [show Psi = T.toDiffeomorph.trans e from rfl,
      ← Diffeomorph.pullbackMetricCross_trans]
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rw [Diffeomorph.pullbackMetricCross_inner, hderiv, euclideanMetric_inner,
      Diffeomorph.pullbackMetricCross_inner]
    rw [Diffeomorph.pullbackMetricCross_scaleMetric] at hmetric
    have hm := congrArg (fun k : SmoothRiemannianMetric 𝓘(Real, E) E =>
      k.inner (T x) (T v) (T w)) hmetric
    change sigma * (Diffeomorph.pullbackMetricCross g e).inner
      (T x) (T v) (T w) = inner Real (T v) (T w) at hm
    have hpt := Diffeomorph.pullbackMetricCross_inner g e (T x) (T v) (T w)
    exact mul_left_cancel₀ hsigma.ne'
      ((congrArg (fun z : Real => sigma * z) hpt).symm.trans
        (hm.trans (hTinner v w)))
  refine ⟨Psi.symm, Diffeomorph.pullbackMetricCross_symm_eq_iff.mp hPsi, ?_⟩
  intro x
  have hp := hpotential (T (Psi.symm x))
  have hx : e (T (Psi.symm x)) = x := Psi.apply_symm_apply x
  rw [hx, gaussianPotential_apply, hTnorm] at hp
  exact hp

theorem gradientRicciSoliton_classification_of_finrank_eq_two
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {sigma : Real}
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    (hsigma : 0 < sigma) (hdim : Module.finrank Real E = 2) :
    (∃ e : M ≃ₘ⟮I, 𝓡 2⟯ EuclideanSpace Real (Fin 2), ∃ b : Real,
      Diffeomorph.pullbackMetricCross euclideanMetric e = g ∧
        ∀ x, f x + b = sigma * ‖e x‖ ^ 2 / 4) ∨
      (∃ e : M ≃ₘ⟮I, 𝓡 2⟯ Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1,
        ∃ b : Real,
          Diffeomorph.pullbackMetricCross
            (scaleMetric (2 / sigma) (div_pos (by norm_num) hsigma)
              (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) e = g ∧
            ∀ x, f x = b) ∨
      (∃ e : M ≃ₘ⟮I, 𝓡 2⟯ RealProjectivePlane, ∃ b : Real,
        Diffeomorph.pullbackMetricCross
          (scaleMetric (2 / sigma) (div_pos (by norm_num) hsigma)
            (roundProjectiveMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) e = g ∧
          ∀ x, f x = b) := by
  obtain ⟨C, hnormalized⟩ := gradientRicciSoliton_exists_normalized hcomplete hsol hsigma
  rcases normalizedGradientRicciSoliton_model_isometries_of_finrank_eq_two hnormalized hdim
    with ⟨e, hmetric, hpotential⟩ | ⟨e, hmetric, hpotential⟩ | ⟨e, hmetric, hpotential⟩
  · obtain ⟨Phi, hPhi, hp⟩ :=
      exists_gaussian_isometry_of_scaled_pullbackMetric hsigma hdim e hmetric hpotential
    exact Or.inl ⟨Phi, C / sigma, hPhi, hp⟩
  · refine Or.inr (Or.inl ⟨e.symm, 1 - C / sigma, ?_, ?_⟩)
    · apply Diffeomorph.pullbackMetricCross_symm_eq_iff.mp
      apply SmoothRiemannianMetric.ext_inner
      intro x v w
      have hm := congrArg (fun k : SmoothRiemannianMetric (𝓡 2)
        (Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1) => k.inner x v w) hmetric
      simp only [Diffeomorph.pullbackMetricCross_inner, scaleMetric_inner] at hm ⊢
      rw [div_mul_eq_mul_div]
      apply (eq_div_iff hsigma.ne').mpr
      simpa only [mul_comm] using hm
    · intro x
      have hp := hpotential (e.symm x)
      change f (e (e.symm x)) + C / sigma = 1 at hp
      rw [e.apply_symm_apply] at hp
      linarith
  · refine Or.inr (Or.inr ⟨e.symm, 1 - C / sigma, ?_, ?_⟩)
    · apply Diffeomorph.pullbackMetricCross_symm_eq_iff.mp
      apply SmoothRiemannianMetric.ext_inner
      intro x v w
      have hm := congrArg (fun k : SmoothRiemannianMetric (𝓡 2) RealProjectivePlane =>
        k.inner x v w) hmetric
      simp only [Diffeomorph.pullbackMetricCross_inner, scaleMetric_inner] at hm ⊢
      rw [div_mul_eq_mul_div]
      apply (eq_div_iff hsigma.ne').mpr
      simpa only [mul_comm] using hm
    · intro x
      have hp := hpotential (e.symm x)
      change f (e (e.symm x)) + C / sigma = 1 at hp
      rw [e.apply_symm_apply] at hp
      linarith

theorem gradientRicciSoliton_exists_gaussian_isometry_of_finrank_eq_two_of_noncompact
    [NoncompactSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {sigma : Real}
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    (hsigma : 0 < sigma) (hdim : Module.finrank Real E = 2) :
    ∃ e : M ≃ₘ⟮I, 𝓡 2⟯ EuclideanSpace Real (Fin 2), ∃ b : Real,
      Diffeomorph.pullbackMetricCross euclideanMetric e = g ∧
        ∀ x, f x + b = sigma * ‖e x‖ ^ 2 / 4 := by
  rcases gradientRicciSoliton_classification_of_finrank_eq_two hcomplete hsol hsigma hdim
    with h | ⟨e, _, _, _⟩ | ⟨e, _, _, _⟩
  · exact h
  · exact False.elim ((not_compactSpace_iff.mpr (inferInstance : NoncompactSpace M))
      e.symm.toHomeomorph.compactSpace)
  · exact False.elim ((not_compactSpace_iff.mpr (inferInstance : NoncompactSpace M))
      e.symm.toHomeomorph.compactSpace)

omit [ConnectedSpace M] in
theorem gradientRicciSoliton_exists_round_sphere_isometry_of_finrank_eq_two_of_simply_connected_of_nonflat
    [SimplyConnectedSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯} {sigma : Real}
    (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    (hsigma : 0 < sigma) (hdim : Module.finrank Real E = 2)
    (hnonflat : ∃ x : M, Curvature.metricRm04At (I := I) g x ≠ 0) :
    ∃ e : M ≃ₘ⟮I, 𝓡 2⟯ Metric.sphere (0 : EuclideanSpace Real (Fin 3)) 1,
      ∃ b : Real,
        Diffeomorph.pullbackMetricCross
          (scaleMetric (2 / sigma) (div_pos (by norm_num) hsigma)
            (roundMetric (E := EuclideanSpace Real (Fin 3)) (n := 2))) e = g ∧
          ∀ x, f x = b := by
  let : CompleteSpace E := FiniteDimensional.complete Real E
  rcases gradientRicciSoliton_classification_of_finrank_eq_two hcomplete hsol hsigma hdim
    with ⟨e, _, hmetric, _⟩ | h | ⟨e, _, _, _⟩
  · obtain ⟨x, hx⟩ := hnonflat
    exfalso
    apply hx
    have hscalar : Curvature.metricScalarAt (I := I) g x = 0 := by
      apply metricScalarAt_eq_zero_of_ricciTensor_eq_zero
      intro v w
      rw [← hmetric, Curvature.ricciTensor_pullbackCross, euclideanMetric_ricciTensor]
    apply ContinuousMultilinearMap.ext
    intro v
    change Curvature.metricRm04At (I := I) g x v = 0
    have hvec : Curvature.vec4 (v 0) (v 1) (v 2) (v 3) = v := by
      funext i
      fin_cases i <;> rfl
    have hv := Curvature.metricRm04StdAt_eq_scalar_div_two_of_finrank_eq_two
      g hdim x (v 0) (v 1) (v 2) (v 3)
    simpa only [Curvature.metricRm04StdAt, Curvature.tensor04StdAt, hvec, hscalar,
      zero_div, zero_mul] using hv
  · exact h
  · exact False.elim (not_simplyConnectedSpace_realProjectivePlane
      e.symm.toHomeomorph.toHomotopyEquiv.simplyConnectedSpace)

end DifferentialGeometry.Geometry
