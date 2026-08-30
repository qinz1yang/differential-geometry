import DifferentialGeometry.Analysis.ODE.CompactSupportFlow
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Operations
import DifferentialGeometry.Geometry.Metric.RicciSoliton.PotentialCompleteness
import DifferentialGeometry.Geometry.Metric.Scaling
import DifferentialGeometry.Geometry.Metric.Pullback
import DifferentialGeometry.Geometry.Metric.Pullback.Completeness
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivativePullback
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciNaturality
import DifferentialGeometry.Geometry.Flow.RicciFlow.Compactness.Solutions.Pullback
import DifferentialGeometry.Geometry.Flow.RicciFlow.ShortTime.ConjugatingFlow.Properties

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
open DifferentialGeometry.PDE.DeTurck (lieDerivMetric lieDerivMetric_smul_vectorField)
open DifferentialGeometry.PDE.RicciFlow.Pullback (cartan_formula_for_lie_deriv_metric)

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

noncomputable def canonicalMetricFamily
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    (t : Real) : SmoothRiemannianMetric I M := by
  classical
  exact if ht : t ∈ canonicalTimeDomain sigma then
      canonicalMetric (I := I) g f sigma hcomplete hsol ht
    else g

theorem canonicalMetricFamily_eq
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {t : Real} (ht : t ∈ canonicalTimeDomain sigma) :
    canonicalMetricFamily (I := I) g f sigma hcomplete hsol t =
      canonicalMetric (I := I) g f sigma hcomplete hsol ht := by
  classical
  simp only [canonicalMetricFamily, dif_pos ht]

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

omit [NeZero (Module.finrank Real E)] [T2Space (TangentBundle I M)]
  [SigmaCompactSpace M] [ConnectedSpace M] in
private theorem lieDerivMetric_gradFun
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (x : M) (v w : TangentSpace I x) :
    lieDerivMetric (I := I) g
        (⟨fun y => gradFun (I := I) g f y,
          gradFun_contMDiff_total_section (I := I) g f.contMDiff⟩ :
          Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) x v w =
      2 * hessFun (I := I) g f x v w := by
  let W : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨fun y => gradFun (I := I) g f y,
      gradFun_contMDiff_total_section (I := I) g f.contMDiff⟩
  change lieDerivMetric (I := I) g W x v w = _
  rw [cartan_formula_for_lie_deriv_metric]
  change g.inner x
      ((LeviCivita (I := I) g) (fun y => gradFun (I := I) g f y) x v) w +
    g.inner x v
      ((LeviCivita (I := I) g) (fun y => gradFun (I := I) g f y) x w) = _
  rw [← hessFun_eq_cov_grad (I := I) g f.contMDiff x v w]
  rw [g.symm x v]
  rw [← hessFun_eq_cov_grad (I := I) g f.contMDiff x w v]
  rw [hessFun_symm_of_boundaryless (I := I) g f.contMDiff x w v]
  ring

private theorem canonicalPullbackMetric_hasDerivAt
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {t : Real} (ht : t ∈ canonicalTimeDomain sigma)
    (x : M) (v w : TangentSpace I x) :
    HasDerivAt
      (fun s : Real =>
        (Diffeomorph.pullbackMetric g
          (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
            (canonicalFlowParameter sigma s))).inner x v w)
      ((2 / (1 - sigma * t)) *
        hessFun (I := I) g f
          (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
            (canonicalFlowParameter sigma t) x)
          (mfderiv I I
            (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
              (canonicalFlowParameter sigma t) : M → M) x v)
          (mfderiv I I
            (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
              (canonicalFlowParameter sigma t) : M → M) x w)) t := by
  classical
  have hopen : IsOpen (canonicalTimeDomain sigma) := by
    rw [canonicalTimeDomain]
    exact isOpen_lt continuous_const
      (continuous_const.sub (continuous_const.mul continuous_id))
  obtain ⟨a, b, htab, hab⟩ :=
    mem_nhds_iff_exists_Ioo_subset.mp (hopen.mem_nhds ht)
  let gradSection : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ :=
    ⟨fun y => gradFun (I := I) g f y,
      gradFun_contMDiff_total_section (I := I) g f.contMDiff⟩
  let Phi : Real → M ≃ₘ⟮I, I⟯ M := fun r =>
    canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
      (canonicalFlowParameter sigma (a + r))
  let Y : Real → Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯ := fun r =>
    (1 / (1 - sigma * (a + r))) • gradSection
  have htime : ∀ r ∈ Ioo (0 : Real) (b - a),
      a + r ∈ canonicalTimeDomain sigma := by
    intro r hr
    apply hab
    constructor <;> linarith [hr.1, hr.2]
  have hPhiOde : ∀ z : M, ∀ r ∈ Ioo (0 : Real) (b - a),
      HasMFDerivWithinAt 𝓘(Real, Real) I
        (fun s : Real => (Phi s : M → M) z) (Ici (0 : Real)) r
        ((1 : Real →L[Real] Real).smulRight (Y r (Phi r z))) := by
    intro z r hr
    have hflow := canonicalFlowDiffeomorph_hasMFDerivAt
      (I := I) g f sigma hcomplete hsol (htime r hr) z
    have htrans : HasDerivAt (fun s : Real => a + s) 1 r :=
      (hasDerivAt_id r).const_add a
    have hcomp := hflow.comp r htrans.hasFDerivAt.hasMFDerivAt
    have hcomp' : HasMFDerivAt 𝓘(Real, Real) I
        (fun s : Real => (Phi s : M → M) z) r
        ((1 : Real →L[Real] Real).smulRight (Y r (Phi r z))) := by
      have hder :
          ((1 : Real →L[Real] Real).smulRight
              ((1 / (1 - sigma * (a + r))) •
                gradFun (I := I) g f
                  (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
                    (canonicalFlowParameter sigma (a + r)) z))) ∘SL
            ContinuousLinearMap.toSpanSingleton Real 1 =
          (1 : Real →L[Real] Real).smulRight (Y r (Phi r z)) := by
        apply ContinuousLinearMap.ext
        intro c
        change (c * 1) • ((1 / (1 - sigma * (a + r))) •
            gradFun (I := I) g f
              (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
                (canonicalFlowParameter sigma (a + r)) z)) =
          c • ((1 / (1 - sigma * (a + r))) •
            gradFun (I := I) g f
              (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
                (canonicalFlowParameter sigma (a + r)) z))
        rw [mul_one]
      have hcompDer := hcomp.congr_mfderiv hder
      rw [show (fun s : Real => (Phi s : M → M) z) =
          (fun s : Real =>
            canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
              (canonicalFlowParameter sigma s) z) ∘ (fun s : Real => a + s) by
        funext s
        rfl]
      exact hcompDer
    exact hcomp'.hasMFDerivWithinAt
  have hPhiJoint : ContMDiffOn (𝓘(Real, Real).prod I) I ∞
      (fun q : Real × M => (Phi q.1 : M → M) q.2)
      (Ioo (0 : Real) (b - a) ×ˢ (Set.univ : Set M)) := by
    intro q hq
    have hflow := canonicalFlowMap_contMDiffAt
      (I := I) g f sigma hcomplete hsol (htime q.1 hq.1) q.2
    have hfirst : ContMDiffAt (𝓘(Real, Real).prod I) 𝓘(Real, Real) ∞
        (fun p : Real × M => a + p.1) q := by
      exact contMDiffAt_const.add contMDiffAt_fst
    have hpair : ContMDiffAt (𝓘(Real, Real).prod I)
        (𝓘(Real, Real).prod I) ∞
        (fun p : Real × M => (a + p.1, p.2)) q :=
      hfirst.prodMk contMDiffAt_snd
    have hcomp := hflow.comp q hpair
    have hcomp' : ContMDiffAt (𝓘(Real, Real).prod I) I ∞
        (fun p : Real × M => (Phi p.1 : M → M) p.2) q := by
      refine hcomp.congr_of_eventuallyEq ?_
      filter_upwards with p
      change (Phi p.1 : M → M) p.2 =
        canonicalFlowMap (I := I) g f sigma hcomplete hsol
          (canonicalFlowParameter sigma (a + p.1)) p.2
      exact canonicalFlowDiffeomorph_apply
        (I := I) g f sigma hcomplete hsol _ _
    exact hcomp'.contMDiffWithinAt
  have hr : t - a ∈ Ioo (0 : Real) (b - a) := by
    constructor <;> linarith [htab.1, htab.2]
  have hslot := flow_slot_pos (I := I) g Y (b - a) Phi hPhiOde hPhiJoint
    (t - a) hr x v w
  have hslotAt := hslot.hasDerivAt (Ici_mem_nhds hr.1)
  have hback := hslotAt.comp t ((hasDerivAt_id t).sub_const a)
  have htimeEq : a + (t - a) = t := by ring
  rw [show Phi (t - a) =
      canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
        (canonicalFlowParameter sigma t) by
      simp only [Phi, htimeEq]] at hback
  rw [show Y (t - a) =
      (1 / (1 - sigma * t)) • gradSection by
      simp only [Y, htimeEq]] at hback
  rw [lieDerivMetric_smul_vectorField] at hback
  have hlie := lieDerivMetric_gradFun (I := I) g f
    (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
      (canonicalFlowParameter sigma t) x)
    (mfderiv I I
      (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
        (canonicalFlowParameter sigma t) : M → M) x v)
    (mfderiv I I
      (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
        (canonicalFlowParameter sigma t) : M → M) x w)
  change lieDerivMetric (I := I) g gradSection _ _ _ = _ at hlie
  rw [hlie] at hback
  have hvalue :
      (1 / (1 - sigma * t)) *
          (2 * hessFun (I := I) g f
            (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
              (canonicalFlowParameter sigma t) x)
            (mfderiv I I
              (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
                (canonicalFlowParameter sigma t) : M → M) x v)
            (mfderiv I I
              (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
                (canonicalFlowParameter sigma t) : M → M) x w)) * 1 =
        (2 / (1 - sigma * t)) *
          hessFun (I := I) g f
            (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
              (canonicalFlowParameter sigma t) x)
            (mfderiv I I
              (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
                (canonicalFlowParameter sigma t) : M → M) x v)
            (mfderiv I I
              (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
                (canonicalFlowParameter sigma t) : M → M) x w) := by
    ring
  have hback' := hback.congr_deriv hvalue
  have hfun :
      ((fun r : Real =>
        g.inner (Phi r x)
          (mfderiv I I (Phi r : M → M) x v)
          (mfderiv I I (Phi r : M → M) x w)) ∘
          (fun s : Real => id s - a)) =
        (fun s : Real =>
          (Diffeomorph.pullbackMetric g
            (canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
              (canonicalFlowParameter sigma s))).inner x v w) := by
    funext s
    rw [Diffeomorph.pullbackMetric_inner]
    simp only [Function.comp_apply, id_eq, Phi]
    rw [show a + (s - a) = s by ring]
    rfl
  rw [hfun] at hback'
  exact hback'

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

theorem canonicalMetricFamily_ricciFlow
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {t : Real} (ht : t ∈ canonicalTimeDomain sigma)
    (x : M) (v w : TangentSpace I x) :
    HasDerivAt
      (fun s : Real =>
        (canonicalMetricFamily (I := I) g f sigma hcomplete hsol s).inner x v w)
      ((-2 : Real) * ricciTensor (I := I)
        (canonicalMetricFamily (I := I) g f sigma hcomplete hsol t) x v w) t := by
  classical
  let Phi : Real → M ≃ₘ⟮I, I⟯ M := fun s =>
    canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
      (canonicalFlowParameter sigma s)
  let pullbackInner : Real → Real := fun s =>
    (Diffeomorph.pullbackMetric g (Phi s)).inner x v w
  have hpullback : HasDerivAt pullbackInner
      ((2 / (1 - sigma * t)) *
        hessFun (I := I) g f (Phi t x)
          (mfderiv I I (Phi t : M → M) x v)
          (mfderiv I I (Phi t : M → M) x w)) t := by
    exact canonicalPullbackMetric_hasDerivAt
      (I := I) g f sigma hcomplete hsol ht x v w
  have hscale : HasDerivAt (fun s : Real => 1 - sigma * s) (-sigma) t := by
    have hraw := (hasDerivAt_const t (1 : Real)).sub
      ((hasDerivAt_const t sigma).mul (hasDerivAt_id t))
    have hfun : ((fun _ : Real => (1 : Real)) - (fun _ : Real => sigma) * id) =
        (fun s : Real => 1 - sigma * s) := by
      funext s
      rfl
    have hder : (0 - (0 * id t + sigma * 1) : Real) = -sigma := by ring
    rw [hfun, hder] at hraw
    exact hraw
  have hproduct := hscale.mul hpullback
  have htau : 1 - sigma * t ≠ 0 := ne_of_gt ht
  have hsolPoint := hsol (Phi t x)
    (mfderiv I I (Phi t : M → M) x v)
    (mfderiv I I (Phi t : M → M) x w)
  have hvalue :
      -sigma * pullbackInner t +
          (1 - sigma * t) *
            ((2 / (1 - sigma * t)) *
              hessFun (I := I) g f (Phi t x)
                (mfderiv I I (Phi t : M → M) x v)
                (mfderiv I I (Phi t : M → M) x w)) =
        (-2 : Real) * ricciTensor (I := I)
          (canonicalMetricFamily (I := I) g f sigma hcomplete hsol t) x v w := by
    dsimp only [pullbackInner]
    rw [canonicalMetricFamily_eq (I := I) g f sigma hcomplete hsol ht]
    rw [canonicalMetric_ricciTensor (I := I) g f sigma hcomplete hsol ht]
    have hPhiPoint :
        canonicalFlowMap (I := I) g f sigma hcomplete hsol
            (canonicalFlowParameter sigma t) x = Phi t x := by
      exact (canonicalFlowDiffeomorph_apply
        (I := I) g f sigma hcomplete hsol _ _).symm
    rw [hPhiPoint]
    rw [Diffeomorph.pullbackMetric_inner]
    let G : Real := g.inner (Phi t x)
      (mfderiv I I (Phi t : M → M) x v)
      (mfderiv I I (Phi t : M → M) x w)
    let Hess : Real := hessFun (I := I) g f (Phi t x)
      (mfderiv I I (Phi t : M → M) x v)
      (mfderiv I I (Phi t : M → M) x w)
    let Ric : Real := ricciTensor (I := I) g (Phi t x)
      (mfderiv I I (Phi t : M → M) x v)
      (mfderiv I I (Phi t : M → M) x w)
    change -sigma * G + (1 - sigma * t) * ((2 / (1 - sigma * t)) * Hess) =
      -2 * Ric
    have hcancel : (1 - sigma * t) * ((2 / (1 - sigma * t)) * Hess) =
        2 * Hess := by
      field_simp [htau]
    rw [hcancel]
    change Ric + Hess = sigma / 2 * G at hsolPoint
    linarith
  have hproduct' := hproduct.congr_deriv hvalue
  have hopen : IsOpen (canonicalTimeDomain sigma) := by
    rw [canonicalTimeDomain]
    exact isOpen_lt continuous_const
      (continuous_const.sub (continuous_const.mul continuous_id))
  have heq :
      (fun s : Real =>
        (canonicalMetricFamily (I := I) g f sigma hcomplete hsol s).inner x v w) =ᶠ[nhds t]
      (fun s : Real => (1 - sigma * s) * pullbackInner s) := by
    filter_upwards [hopen.eventually_mem ht] with s hs
    rw [canonicalMetricFamily_eq (I := I) g f sigma hcomplete hsol hs]
    rw [canonicalMetric, Diffeomorph.pullbackMetric_inner,
      scaleMetric_inner]
    dsimp only [pullbackInner]
    rw [Diffeomorph.pullbackMetric_inner]
  exact hproduct'.congr_of_eventuallyEq heq

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

theorem canonicalMetric_normGradSqFun
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {t : Real} (ht : t ∈ canonicalTimeDomain sigma) (x : M) :
    normGradSqFun (I := I)
        (canonicalMetric (I := I) g f sigma hcomplete hsol ht)
        (canonicalPotential (I := I) g f sigma hcomplete hsol t) x =
      (1 - sigma * t)⁻¹ * normGradSqFun (I := I) g f
        (canonicalFlowMap (I := I) g f sigma hcomplete hsol
          (canonicalFlowParameter sigma t) x) := by
  let tau : Real := 1 - sigma * t
  let Phi := canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
    (canonicalFlowParameter sigma t)
  have hτ : 0 < tau := by
    dsimp [tau]
    exact mem_canonicalTimeDomain_iff.mp ht
  rw [normGradSqFun_def, normGradSqFun_def]
  have hgrad := DifferentialGeometry.PDE.RicciFlow.gradientFun_pullback
    (I := I) (M := M) (N := M) (g := scaleMetric (I := I) tau hτ g)
    Phi (f : M → Real) x ((f.contMDiff (Phi x)).mdifferentiableAt (by simp))
  have hgrad' :
      gradientFun (I := I)
        (canonicalMetric (I := I) g f sigma hcomplete hsol ht)
        (canonicalPotential (I := I) g f sigma hcomplete hsol t) x =
        (Phi.mfderivToContinuousLinearEquiv (by simp) x).symm
          (gradientFun (I := I) (scaleMetric (I := I) tau hτ g)
            (f : M → Real) (Phi x)) := by
    change gradientFun (I := I)
        (Diffeomorph.pullbackMetric (scaleMetric (I := I) tau hτ g) Phi)
        (f ∘ (Phi : M → M)) x = _
    exact hgrad
  change ((canonicalMetric (I := I) g f sigma hcomplete hsol ht).inner x)
      (gradientFun (I := I)
        (canonicalMetric (I := I) g f sigma hcomplete hsol ht)
        (canonicalPotential (I := I) g f sigma hcomplete hsol t) x)
      (gradientFun (I := I)
        (canonicalMetric (I := I) g f sigma hcomplete hsol ht)
        (canonicalPotential (I := I) g f sigma hcomplete hsol t) x) =
      (1 - sigma * t)⁻¹ * ((g.inner
        (canonicalFlowMap (I := I) g f sigma hcomplete hsol
          (canonicalFlowParameter sigma t) x))
        (gradientFun (I := I) g (f : M → Real)
          (canonicalFlowMap (I := I) g f sigma hcomplete hsol
            (canonicalFlowParameter sigma t) x)))
        (gradientFun (I := I) g (f : M → Real)
          (canonicalFlowMap (I := I) g f sigma hcomplete hsol
            (canonicalFlowParameter sigma t) x))
  rw [hgrad']
  rw [canonicalMetric, Diffeomorph.pullbackMetric_inner]
  rw [← Phi.mfderivToContinuousLinearEquiv_coe (by simp) (x := x)]
  simp only [ContinuousLinearEquiv.coe_coe, ContinuousLinearEquiv.apply_symm_apply]
  rw [Operator.gradientFun_scale (I := I) tau hτ g (f : M → Real) (Phi x)]
  rw [scaleMetric_inner]
  simp only [map_smul, smul_apply, smul_eq_mul]
  dsimp [tau]
  have ha : 1 - sigma * t = tau := rfl
  rw [ha]
  field_simp [ne_of_gt hτ]
  rw [show canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
      (canonicalFlowParameter sigma t) x = Phi x by rfl]
  rw [canonicalFlowDiffeomorph_apply]

theorem canonicalPotential_evolution_slice
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {t : Real} (ht : t ∈ canonicalTimeDomain sigma) (x : M) :
    HasDerivAt
      (fun s : Real => canonicalPotential (I := I) g f sigma hcomplete hsol s x)
      (normGradSqFun (I := I)
        (canonicalMetric (I := I) g f sigma hcomplete hsol ht)
        (canonicalPotential (I := I) g f sigma hcomplete hsol t) x) t := by
  have hevol := canonicalPotential_evolution (I := I) g f sigma hcomplete hsol ht x
  have hnorm := canonicalMetric_normGradSqFun (I := I) g f sigma hcomplete hsol ht x
  rw [hnorm]
  simpa only [one_div] using hevol

theorem canonicalMetric_hamilton_constant_scaled
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {t : Real} (ht : t ∈ canonicalTimeDomain sigma) (C : Real)
    (hC : ∀ y : M,
      metricScalarAt (I := I) g y +
          g.inner y (gradFun (I := I) g f y) (gradFun (I := I) g f y) -
        sigma * f y = C) :
    ∀ x : M,
      metricScalarAt (I := I)
          (canonicalMetric (I := I) g f sigma hcomplete hsol ht) x +
        normGradSqFun (I := I)
          (canonicalMetric (I := I) g f sigma hcomplete hsol ht)
          (canonicalPotential (I := I) g f sigma hcomplete hsol t) x -
        (sigma / (1 - sigma * t)) *
          canonicalPotential (I := I) g f sigma hcomplete hsol t x =
      C / (1 - sigma * t) := by
  intro x
  let tau : Real := 1 - sigma * t
  let Phi := canonicalFlowDiffeomorph (I := I) g f sigma hcomplete hsol
    (canonicalFlowParameter sigma t)
  have hscalar := canonicalMetric_scalar (I := I) g f sigma hcomplete hsol ht x
  have hnorm := canonicalMetric_normGradSqFun (I := I) g f sigma hcomplete hsol ht x
  have hPhi : Phi x = canonicalFlowMap (I := I) g f sigma hcomplete hsol
      (canonicalFlowParameter sigma t) x := by
    exact canonicalFlowDiffeomorph_apply (I := I) g f sigma hcomplete hsol
      (canonicalFlowParameter sigma t) x
  rw [hscalar, hnorm, hPhi.symm]
  change (1 - sigma * t)⁻¹ * metricScalarAt (I := I) g (Phi x) +
      tau⁻¹ * ((g.inner (Phi x))
        (gradientFun (I := I) g (f : M → Real) (Phi x)))
        (gradientFun (I := I) g (f : M → Real) (Phi x)) -
      (sigma / (1 - sigma * t)) * f (Phi x) = C / (1 - sigma * t)
  have hCy := hC (Phi x)
  rw [← DifferentialGeometry.Geometry.Connection.gradient_eq_gradFun] at hCy
  dsimp [tau]
  calc
    _ = (metricScalarAt (I := I) g (Phi x) +
      ((g.inner (Phi x))
        (gradientFun (I := I) g (f : M → Real) (Phi x)))
        (gradientFun (I := I) g (f : M → Real) (Phi x)) - sigma * f (Phi x)) /
        (1 - sigma * t) := by
      ring_nf
    _ = C / (1 - sigma * t) := by rw [hCy]

theorem canonicalMetric_exists_hamilton_constant_scaled
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma)
    {t : Real} (ht : t ∈ canonicalTimeDomain sigma) :
    ∃ C : Real,
      (∀ y : M,
        metricScalarAt (I := I) g y +
            g.inner y (gradFun (I := I) g f y) (gradFun (I := I) g f y) -
          sigma * f y = C) ∧
      ∀ x : M,
        metricScalarAt (I := I)
            (canonicalMetric (I := I) g f sigma hcomplete hsol ht) x +
          normGradSqFun (I := I)
            (canonicalMetric (I := I) g f sigma hcomplete hsol ht)
            (canonicalPotential (I := I) g f sigma hcomplete hsol t) x -
          (sigma / (1 - sigma * t)) *
            canonicalPotential (I := I) g f sigma hcomplete hsol t x =
        C / (1 - sigma * t) := by
  obtain ⟨C, hC⟩ := gradientRicciSoliton_hamilton_constant hsol
  exact ⟨C, hC,
    canonicalMetric_hamilton_constant_scaled (I := I) g f sigma hcomplete hsol ht C hC⟩

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

theorem canonicalMetricFamily_zero
    (g : SmoothRiemannianMetric I M) (f : C^∞⟮I, M; Real⟯)
    (sigma : Real) (hcomplete : RiemannianMetricComplete (I := I) g)
    (hsol : gradientRicciSoliton (I := I) g f sigma) :
    canonicalMetricFamily (I := I) g f sigma hcomplete hsol 0 = g := by
  rw [canonicalMetricFamily_eq (I := I) g f sigma hcomplete hsol
    (zero_mem_canonicalTimeDomain sigma)]
  exact canonicalMetric_zero (I := I) g f sigma hcomplete hsol

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
