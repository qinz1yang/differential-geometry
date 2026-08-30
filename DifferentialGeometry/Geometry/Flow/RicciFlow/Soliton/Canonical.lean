import DifferentialGeometry.Analysis.ODE.CompactSupportFlow
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Operations
import DifferentialGeometry.Geometry.Metric.RicciSoliton.PotentialCompleteness
import DifferentialGeometry.Geometry.Metric.Scaling
import DifferentialGeometry.Geometry.Metric.Pullback
import DifferentialGeometry.Geometry.Metric.Pullback.Completeness
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivativePullback
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciNaturality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Pullback

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.PDE.RicciFlow.Soliton

open DifferentialGeometry.Geometry
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Analysis.ODE

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] [ConnectedSpace M]

def canonicalTimeDomain (sigma : Real) : Set Real :=
  {t : Real | 1 - sigma * t > 0}

theorem zero_mem_canonicalTimeDomain (sigma : Real) :
    0 ∈ canonicalTimeDomain sigma := by
  simp [canonicalTimeDomain]

theorem mem_canonicalTimeDomain_iff {sigma t : Real} :
    t ∈ canonicalTimeDomain sigma ↔ 1 - sigma * t > 0 := by
  rfl

noncomputable def canonicalFlowParameter (sigma t : Real) : Real :=
  if sigma = 0 then t else -Real.log (1 - sigma * t) / sigma

theorem canonicalFlowParameter_zero (sigma : Real) :
    canonicalFlowParameter sigma 0 = 0 := by
  by_cases hσ : sigma = 0
  · simp [canonicalFlowParameter, hσ]
  · simp [canonicalFlowParameter, hσ]

theorem canonicalFlowParameter_of_zero {t : Real} :
    canonicalFlowParameter 0 t = t := by
  simp [canonicalFlowParameter]

theorem canonicalFlowParameter_deriv {sigma t : Real}
    (ht : t ∈ canonicalTimeDomain sigma) :
    HasDerivAt (canonicalFlowParameter sigma) (1 / (1 - sigma * t)) t := by
  by_cases hσ : sigma = 0
  · subst hσ
    have hp : canonicalFlowParameter 0 = id := by
      funext s
      simp [canonicalFlowParameter]
    rw [hp]
    norm_num only [zero_mul, sub_zero, div_one]
    exact hasDerivAt_id t
  · have hpos : 0 < 1 - sigma * t := ht
    have hinner : HasDerivAt (fun s : Real => 1 - sigma * s) (-sigma) t := by
      have hraw := (hasDerivAt_const t (1 : Real)).sub
        ((hasDerivAt_const t sigma).mul (hasDerivAt_id t))
      have hfun : ((fun x : Real => 1) - (fun x : Real => sigma) * id) =
          (fun s : Real => 1 - sigma * s) := by
        funext s
        simp [sub_eq_add_neg]
      have hder : (0 - (0 * id t + sigma * 1) : Real) = -sigma := by ring
      rw [hfun, hder] at hraw
      exact hraw
    have hlog : HasDerivAt (fun s : Real => Real.log (1 - sigma * s))
        (-(sigma * (1 - sigma * t)⁻¹)) t := by
      have hcomp := (Real.hasDerivAt_log hpos.ne').comp t hinner
      simpa [Function.comp_def, mul_comm, mul_left_comm, mul_assoc] using hcomp
    rw [show canonicalFlowParameter sigma =
      fun s : Real => (-1 / sigma) * Real.log (1 - sigma * s) by
        funext s
        simp [canonicalFlowParameter, hσ, div_eq_mul_inv]
        ring]
    have hfinal := hlog.const_mul (-1 / sigma)
    simpa [Function.comp_def, div_eq_mul_inv, hσ, mul_comm, mul_left_comm, mul_assoc] using hfinal

private theorem potentialIntegralCurves
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma) :
    ∀ x : M, ∃ gamma : Real → M,
      gamma 0 = x ∧ IsMIntegralCurve gamma (fun y => gradFun (I := I) g f y) :=
  gradientRicciSoliton_exists_globalIntegralCurve_potential
    (I := I) g f sigma hcomplete hsol

noncomputable def canonicalFlowMap
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    (t : Real) : M → M :=
  fun x : M => curveAt (fun y => gradFun (I := I) g f y)
    (potentialIntegralCurves (I := I) g f sigma hcomplete hsol) x t

theorem canonicalFlowMap_zero
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma) :
    canonicalFlowMap (I := I) g f sigma hcomplete hsol 0 = id := by
  funext x
  exact curveAt_zero _ _ x

theorem canonicalFlowMap_diffeomorph
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    (s : Real) :
    ∃ d : Diffeomorph I I M M ∞,
      (∀ x, d x = canonicalFlowMap (I := I) g f sigma hcomplete hsol s x) ∧
      (∀ x, d.symm x = canonicalFlowMap (I := I) g f sigma hcomplete hsol (-s) x) := by
  let hcurves := potentialIntegralCurves (I := I) g f sigma hcomplete hsol
  let v : (x : M) → TangentSpace I x := fun y => gradFun (I := I) g f y
  have hv : ContMDiff I (I.prod 𝓘(Real, E)) ∞
      (fun x : M => (⟨x, v x⟩ : TangentBundle I M)) := by
    exact gradFun_contMDiff_total_section (I := I) g f.contMDiff
  have hd := globalFlow_diffeomorph_of_complete (I := I) v hv hcurves s
  obtain ⟨d, hd, hdsym⟩ := hd
  refine ⟨d, ?_, ?_⟩
  · intro x
    exact hd x
  · intro x
    exact hdsym x

noncomputable def canonicalFlowDiffeomorph
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    (s : Real) : Diffeomorph I I M M ∞ :=
  Classical.choose (canonicalFlowMap_diffeomorph (I := I) g f sigma hcomplete hsol s)

theorem canonicalFlowDiffeomorph_apply
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    (s : Real) (x : M) :
    canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol s x =
      canonicalFlowMap (I := I) g f sigma hcomplete hsol s x := by
  exact (Classical.choose_spec
    (canonicalFlowMap_diffeomorph (I := I) g f sigma hcomplete hsol s)).1 x

theorem canonicalFlowDiffeomorph_symm_apply
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    (s : Real) (x : M) :
    (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol s).symm x =
      canonicalFlowMap (I := I) g f sigma hcomplete hsol (-s) x := by
  exact (Classical.choose_spec
    (canonicalFlowMap_diffeomorph (I := I) g f sigma hcomplete hsol s)).2 x

theorem canonicalFlowDiffeomorph_zero
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma) :
    canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol 0 =
      _root_.Diffeomorph.refl I M ∞ := by
  apply Diffeomorph.ext
  intro x
  rw [canonicalFlowDiffeomorph_apply]
  exact congrFun (canonicalFlowMap_zero (I := I) g f sigma hcomplete hsol) x

theorem canonicalFlowParameter_contDiffAt {sigma t : Real}
    (ht : t ∈ canonicalTimeDomain sigma) :
    ContDiffAt Real ∞ (canonicalFlowParameter sigma) t := by
  by_cases hσ : sigma = 0
  · subst hσ
    have hp : canonicalFlowParameter 0 = id := by
      funext s
      simp [canonicalFlowParameter]
    rw [hp]
    exact contDiffAt_id
  · have hpos : 0 < 1 - sigma * t := ht
    have hlin : ContDiffAt Real ∞ (fun s : Real => 1 - sigma * s) t := by
      have hconst : ContDiffAt Real ∞ (fun _ : Real => (1 : Real)) t :=
        contDiffAt_const
      have hsig : ContDiffAt Real ∞ (fun _ : Real => sigma) t :=
        contDiffAt_const
      have hid : ContDiffAt Real ∞ (id : Real → Real) t := contDiffAt_id
      simpa [Function.comp_def] using hconst.sub (hsig.mul hid)
    have hlog : ContDiffAt Real ∞
        (fun s : Real => Real.log (1 - sigma * s)) t := by
      have hlog0 : ContDiffAt Real ∞ Real.log (1 - sigma * t) :=
        Real.contDiffAt_log.2 hpos.ne'
      change ContDiffAt Real ∞
        (Real.log ∘ (fun s : Real => 1 - sigma * s)) t
      exact hlog0.comp t hlin
    have hscaled : ContDiffAt Real ∞
        (fun s : Real => (-1 / sigma) * Real.log (1 - sigma * s)) t :=
      hlog.const_smul (-1 / sigma)
    have hfun : canonicalFlowParameter sigma =
        (fun s : Real => (-1 / sigma) * Real.log (1 - sigma * s)) := by
      funext s
      simp [canonicalFlowParameter, hσ, div_eq_mul_inv]
      ring
    rw [hfun]
    exact hscaled

theorem canonicalFlowMap_contMDiffAt
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {t : Real} (ht : t ∈ canonicalTimeDomain sigma) (x : M) :
    ContMDiffAt (𝓘(Real, Real).prod I) I ∞
      (fun p : Real × M => canonicalFlowMap (I := I) g f sigma hcomplete hsol
        (canonicalFlowParameter sigma p.1) p.2) (t, x) := by
  let hcurves := potentialIntegralCurves (I := I) g f sigma hcomplete hsol
  let v : (y : M) → TangentSpace I y := fun y => gradFun (I := I) g f y
  have hv : ContMDiff I (I.prod 𝓘(Real, E)) ∞
      (fun y : M => (⟨y, v y⟩ : TangentBundle I M)) := by
    exact gradFun_contMDiff_total_section (I := I) g f.contMDiff
  have hflow := contMDiffAt_globalFlow_joint_of_complete
    (I := I) v hv hcurves (canonicalFlowParameter sigma t) x
  have hparam := canonicalFlowParameter_contDiffAt ht
  have hparamAt : ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
      (fun p : Real × M => canonicalFlowParameter sigma p.1) (t, x) := by
    exact hparam.contMDiffAt.comp (t, x)
      (contMDiffAt_fst (I := 𝓘(Real, Real)) (J := I) (p := (t, x)))
  have hsnd : ContMDiffAt (𝓘(Real, Real).prod I) I ∞
      (fun p : Real × M => p.2) (t, x) := contMDiffAt_snd
  have hpair : ContMDiffAt (𝓘(Real, Real).prod I)
      (𝓘(Real, Real).prod I) ∞
      (fun p : Real × M => (canonicalFlowParameter sigma p.1, p.2)) (t, x) := by
    exact hparamAt.prodMk hsnd
  have hcomp := hflow.comp (t, x) hpair
  simpa [canonicalFlowMap, v, Function.comp_def] using hcomp

theorem canonicalFlowMap_hasMFDerivAt
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {t : Real} (ht : t ∈ canonicalTimeDomain sigma) (x : M) :
    HasMFDerivAt 𝓘(Real, Real) I
      (fun s : Real => canonicalFlowMap (I := I) g f sigma hcomplete hsol
        (canonicalFlowParameter sigma s) x) t
      ((1 : Real →L[Real] Real).smulRight
        ((1 / (1 - sigma * t)) •
          gradFun (I := I) g f
            (canonicalFlowMap (I := I) g f sigma hcomplete hsol
              (canonicalFlowParameter sigma t) x))) := by
  let hcurves := potentialIntegralCurves (I := I) g f sigma hcomplete hsol
  let gamma : Real → M := curveAt (fun y : M => gradFun (I := I) g f y) hcurves x
  have hgamma := curveAt_integralCurve
    (fun y : M => gradFun (I := I) g f y) hcurves x
    (canonicalFlowParameter sigma t)
  have hparam := canonicalFlowParameter_deriv (sigma := sigma) ht
  have hcomp := HasMFDerivAt.comp t hgamma hparam.hasFDerivAt.hasMFDerivAt
  have heq : (fun s : Real => canonicalFlowMap (I := I) g f sigma hcomplete hsol
      (canonicalFlowParameter sigma s) x) =
      gamma ∘ canonicalFlowParameter sigma := by
    funext s
    simp [gamma, canonicalFlowMap]
  rw [heq]
  have hclm :
      (ContinuousLinearMap.smulRight (1 : Real →L[Real] Real)
          ((1 / (1 - sigma * t)) •
            gradFun (I := I) g f
              (canonicalFlowMap (I := I) g f sigma hcomplete hsol
                (canonicalFlowParameter sigma t) x))) =
        (ContinuousLinearMap.smulRight (1 : Real →L[Real] Real)
            (gradFun (I := I) g f
              (canonicalFlowMap (I := I) g f sigma hcomplete hsol
                (canonicalFlowParameter sigma t) x))) ∘SL
          ContinuousLinearMap.toSpanSingleton ℝ (1 / (1 - sigma * t)) := by
    apply ContinuousLinearMap.ext
    intro r
    change r • ((1 / (1 - sigma * t)) •
      gradFun (I := I) g f
        (canonicalFlowMap (I := I) g f sigma hcomplete hsol
          (canonicalFlowParameter sigma t) x)) =
      (r * (1 / (1 - sigma * t))) •
        gradFun (I := I) g f
          (canonicalFlowMap (I := I) g f sigma hcomplete hsol
            (canonicalFlowParameter sigma t) x)
    rw [smul_smul]
  rw [hclm]
  exact hcomp

noncomputable def canonicalMetric
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {t : Real} (ht : t ∈ canonicalTimeDomain sigma) : SmoothRiemannianMetric I M :=
  Diffeomorph.pullbackMetric
    (scaleMetric (I := I) (1 - sigma * t) (mem_canonicalTimeDomain_iff.mp ht) g)
    (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
      (canonicalFlowParameter sigma t))

noncomputable def canonicalPotential
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    (t : Real) : C^∞⟮I, M; Real⟯ :=
  f.comp (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
    (canonicalFlowParameter sigma t)).toContMDiffMap

theorem canonicalPotential_hasDerivAt
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {t : Real} (ht : t ∈ canonicalTimeDomain sigma) (x : M) :
    HasDerivAt
      (fun s : Real => canonicalPotential (I := I) g f sigma hcomplete hsol s x)
      ((1 / (1 - sigma * t)) *
        g.inner
          (canonicalFlowMap (I := I) g f sigma hcomplete hsol
            (canonicalFlowParameter sigma t) x)
          (gradFun (I := I) g f
            (canonicalFlowMap (I := I) g f sigma hcomplete hsol
              (canonicalFlowParameter sigma t) x))
          (gradFun (I := I) g f
            (canonicalFlowMap (I := I) g f sigma hcomplete hsol
              (canonicalFlowParameter sigma t) x))) t := by
  let hcurves := potentialIntegralCurves (I := I) g f sigma hcomplete hsol
  let gamma : Real → M := curveAt (fun y : M => gradFun (I := I) g f y) hcurves x
  have hgamma := hasDerivAt_df_comp_integralCurve (I := I) (f := (f : M → Real))
    f.contMDiff (fun y : M => gradFun (I := I) g f y)
    (curveAt_integralCurve (fun y : M => gradFun (I := I) g f y) hcurves x)
    (canonicalFlowParameter sigma t)
  have hparam := canonicalFlowParameter_deriv (sigma := sigma) ht
  have hcomp := hgamma.comp t hparam
  have heq : (fun s : Real => canonicalPotential (I := I) g f sigma hcomplete hsol s x) =
      (fun s : Real => f (gamma (canonicalFlowParameter sigma s))) := by
    funext s
    change f ((canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
      (canonicalFlowParameter sigma s)) x) = _
    rw [canonicalFlowDiffeomorph_apply]
    rfl
  have hinner := inner_gradFun (I := I) g (f : M → Real)
    (gamma (canonicalFlowParameter sigma t))
    (gradFun (I := I) g f (gamma (canonicalFlowParameter sigma t)))
  have hder := hcomp.congr_deriv (by rw [← hinner])
  have hder' := hder.congr_deriv (mul_comm _ _)
  have hmap :
      canonicalFlowMap (I := I) g f sigma hcomplete hsol
          (canonicalFlowParameter sigma t) x =
        gamma (canonicalFlowParameter sigma t) := by
    rfl
  rw [hmap]
  have hpoint : ∀ s : Real,
      canonicalPotential (I := I) g f sigma hcomplete hsol s x =
        ((f : M → Real) ∘ curveAt (fun y : M => gradFun (I := I) g f y)
          hcurves x) (canonicalFlowParameter sigma s) := by
    intro s
    rw [congrFun heq s]
    rfl
  have hresult := hder'.congr_of_eventuallyEq
    (Filter.Eventually.of_forall hpoint)
  change HasDerivAt
    (fun s : Real => (canonicalPotential (I := I) g f sigma hcomplete hsol s) x) _ t
  exact hresult

theorem canonicalPotential_evolution
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {t : Real} (ht : t ∈ canonicalTimeDomain sigma) (x : M) :
    HasDerivAt
      (fun s : Real => canonicalPotential (I := I) g f sigma hcomplete hsol s x)
      ((1 / (1 - sigma * t)) *
        normGradSqFun (I := I) g (f : M → Real)
          (canonicalFlowMap (I := I) g f sigma hcomplete hsol
            (canonicalFlowParameter sigma t) x)) t := by
  simpa only [normGradSqFun_def] using
    canonicalPotential_hasDerivAt (I := I) g f sigma hcomplete hsol ht x

theorem canonicalPotential_zero
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma) :
    canonicalPotential (I := I) g f sigma hcomplete hsol 0 = f := by
  apply ContMDiffMap.ext
  intro x
  change f ((canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
    (canonicalFlowParameter sigma 0)) x) = f x
  rw [canonicalFlowParameter_zero, canonicalFlowDiffeomorph_apply]
  exact congrFun (canonicalFlowMap_zero (I := I) g f sigma hcomplete hsol) x ▸ rfl

theorem canonicalFlowDiffeomorph_hasMFDerivAt
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {t : Real} (ht : t ∈ canonicalTimeDomain sigma) (x : M) :
    HasMFDerivAt 𝓘(Real, Real) I
      (fun s : Real => canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
        (canonicalFlowParameter sigma s) x) t
      ((1 : Real →L[Real] Real).smulRight
        ((1 / (1 - sigma * t)) •
          gradFun (I := I) g f
            (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
              (canonicalFlowParameter sigma t) x))) := by
  have h := canonicalFlowMap_hasMFDerivAt
    (I := I) g f sigma hcomplete hsol ht x
  have hfun : (fun s : Real =>
      (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
        (canonicalFlowParameter sigma s)) x) =
      (fun s : Real => canonicalFlowMap (I := I) g f sigma hcomplete hsol
        (canonicalFlowParameter sigma s) x) := by
    funext s
    rw [canonicalFlowDiffeomorph_apply]
  rw [hfun]
  rw [canonicalFlowDiffeomorph_apply]
  exact h

theorem canonicalMetric_ricciTensor
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {t : Real} (ht : t ∈ canonicalTimeDomain sigma) (x : M)
    (v w : TangentSpace I x) :
    ricciTensor (I := I)
        (canonicalMetric (I := I) g f sigma hcomplete hsol ht) x v w =
      ricciTensor (I := I) g
        (canonicalFlowMap (I := I) g f sigma hcomplete hsol
          (canonicalFlowParameter sigma t) x)
        (mfderiv I I
          (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
            (canonicalFlowParameter sigma t) : M → M) x v)
        (mfderiv I I
          (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
            (canonicalFlowParameter sigma t) : M → M) x w) := by
  rw [canonicalMetric,
    DifferentialGeometry.Geometry.Curvature.ricciTensor_pullback,
    DifferentialGeometry.Geometry.Curvature.ricciTensor_scaleMetric,
    canonicalFlowDiffeomorph_apply]

theorem canonicalMetric_gradientRicciSoliton
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {t : Real} (ht : t ∈ canonicalTimeDomain sigma) :
    gradientRicciSoliton (I := I)
      (canonicalMetric (I := I) g f sigma hcomplete hsol ht)
      (canonicalPotential (I := I) g f sigma hcomplete hsol t)
      (sigma / (1 - sigma * t)) := by
  have hscale := gradientRicciSoliton_scaleMetric (I := I) hsol
    (1 - sigma * t) (mem_canonicalTimeDomain_iff.mp ht)
  have hpb := gradientRicciSoliton_pullbackCross (I := I) hscale
    (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
      (canonicalFlowParameter sigma t))
  exact hpb

theorem canonicalMetric_hamilton_constant
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {t : Real} (ht : t ∈ canonicalTimeDomain sigma) :
    ∃ C : Real, ∀ x : M,
      metricScalarAt (I := I) (canonicalMetric (I := I) g f sigma hcomplete hsol ht) x +
          (canonicalMetric (I := I) g f sigma hcomplete hsol ht).inner x
            (gradFun (I := I) (canonicalMetric (I := I) g f sigma hcomplete hsol ht)
              (canonicalPotential (I := I) g f sigma hcomplete hsol t) x)
            (gradFun (I := I) (canonicalMetric (I := I) g f sigma hcomplete hsol ht)
              (canonicalPotential (I := I) g f sigma hcomplete hsol t) x) -
          (sigma / (1 - sigma * t)) *
            canonicalPotential (I := I) g f sigma hcomplete hsol t x = C := by
  exact gradientRicciSoliton_hamilton_constant
    (canonicalMetric_gradientRicciSoliton (I := I) g f sigma hcomplete hsol ht)

theorem canonicalMetric_weightedLaplacian_potential
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {t : Real} (ht : t ∈ canonicalTimeDomain sigma) (x : M) :
    ∃ C : Real,
      weightedLaplacian (I := I)
          (canonicalMetric (I := I) g f sigma hcomplete hsol ht)
          (canonicalPotential (I := I) g f sigma hcomplete hsol t)
          (canonicalPotential (I := I) g f sigma hcomplete hsol t) x =
        (Module.finrank Real E : Real) * (sigma / (1 - sigma * t)) / 2 -
          (sigma / (1 - sigma * t)) *
            canonicalPotential (I := I) g f sigma hcomplete hsol t x - C := by
  obtain ⟨C, hC⟩ := canonicalMetric_hamilton_constant
    (I := I) g f sigma hcomplete hsol ht
  refine ⟨C, ?_⟩
  apply gradientRicciSoliton_weightedLaplacian_potential
    (canonicalMetric_gradientRicciSoliton (I := I) g f sigma hcomplete hsol ht) _ x
  intro y
  simpa only [normGradSqFun_def] using hC y

theorem canonicalTimeDomain_zero_eq_univ :
    canonicalTimeDomain 0 = (Set.univ : Set Real) := by
  ext t
  simp [canonicalTimeDomain]

theorem canonicalMetric_inner
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {t : Real} (ht : t ∈ canonicalTimeDomain sigma) (x : M)
    (v w : TangentSpace I x) :
    (canonicalMetric (I := I) g f sigma hcomplete hsol ht).inner x v w =
      (1 - sigma * t) * g.inner
        (canonicalFlowMap (I := I) g f sigma hcomplete hsol
          (canonicalFlowParameter sigma t) x)
        (mfderiv I I
          (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
            (canonicalFlowParameter sigma t) : M → M) x v)
        (mfderiv I I
          (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
            (canonicalFlowParameter sigma t) : M → M) x w) := by
  rw [canonicalMetric, Diffeomorph.pullbackMetric_inner, scaleMetric_inner]
  rw [canonicalFlowDiffeomorph_apply]

theorem canonicalMetric_scalar
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {t : Real} (ht : t ∈ canonicalTimeDomain sigma) (x : M) :
    metricScalarAt (I := I)
        (canonicalMetric (I := I) g f sigma hcomplete hsol ht) x =
      (1 - sigma * t)⁻¹ * metricScalarAt (I := I) g
        (canonicalFlowMap (I := I) g f sigma hcomplete hsol
          (canonicalFlowParameter sigma t) x) := by
  rw [canonicalMetric, DifferentialGeometry.HCGCompactness.metricScalarAt_pullback,
    metricScalarAt_scaleMetric,
    canonicalFlowDiffeomorph_apply]

theorem canonicalMetric_metricRm04
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {t : Real} (ht : t ∈ canonicalTimeDomain sigma) (x : M)
    (slots : Fin 4 → TangentSpace I x) :
    metricRm04 (I := I)
        (canonicalMetric (I := I) g f sigma hcomplete hsol ht) x slots =
      (1 - sigma * t) • metricRm04 (I := I) g
        (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
          (canonicalFlowParameter sigma t) x)
        (fun i => mfderiv I I
          (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
            (canonicalFlowParameter sigma t) : M → M) x (slots i)) := by
  let _ : IsManifold I 1 M :=
    IsManifold.of_le (I := I) (M := M) (n := ∞)
      (by decide : (1 : WithTop ℕ∞) ≤ ∞)
  rw [canonicalMetric, DifferentialGeometry.PDE.RicciFlow.metricRm04_pullback_eval]
  rw [metricRm_scale]
  rfl

theorem canonicalMetric_zero
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma) :
    canonicalMetric (I := I) g f sigma hcomplete hsol
      (zero_mem_canonicalTimeDomain sigma) = g := by
  apply SmoothRiemannianMetric.ext_inner
  intro x v w
  rw [canonicalMetric_inner]
  have hflow : canonicalFlowParameter sigma 0 = 0 := canonicalFlowParameter_zero sigma
  rw [hflow, canonicalFlowDiffeomorph_apply]
  have hmapx : canonicalFlowMap (I := I) g f sigma hcomplete hsol 0 x = x :=
    congrFun (canonicalFlowMap_zero (I := I) g f sigma hcomplete hsol) x
  have hfun :
      (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol 0 : M → M) = id := by
    funext y
    rw [canonicalFlowDiffeomorph_apply]
    exact congrFun (canonicalFlowMap_zero (I := I) g f sigma hcomplete hsol) y
  have hmfd : mfderiv I I
      (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol 0 : M → M) x =
      ContinuousLinearMap.id Real (TangentSpace I x) := by
    rw [hfun]
    exact mfderiv_id
  rw [hmapx, hmfd]
  simp

theorem canonicalMetric_complete
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {t : Real} (ht : t ∈ canonicalTimeDomain sigma) :
    RiemannianMetricComplete (I := I)
      (canonicalMetric (I := I) g f sigma hcomplete hsol ht) := by
  exact RiemannianMetricComplete.pullbackMetric
    (scaleMetric (I := I) (1 - sigma * t)
      (mem_canonicalTimeDomain_iff.mp ht) g)
    (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
      (canonicalFlowParameter sigma t))
    (RiemannianMetricComplete.scaleMetric hcomplete
      (1 - sigma * t) (mem_canonicalTimeDomain_iff.mp ht))


end DifferentialGeometry.PDE.RicciFlow.Soliton
