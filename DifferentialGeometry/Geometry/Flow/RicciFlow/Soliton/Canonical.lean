import DifferentialGeometry.Analysis.ODE.CompactSupportFlow
import DifferentialGeometry.Geometry.Metric.RicciSoliton.Operations
import DifferentialGeometry.Geometry.Metric.RicciSoliton.PotentialCompleteness
import DifferentialGeometry.Geometry.Metric.Scaling
import DifferentialGeometry.Geometry.Metric.Pullback
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivativePullback

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

end DifferentialGeometry.PDE.RicciFlow.Soliton
