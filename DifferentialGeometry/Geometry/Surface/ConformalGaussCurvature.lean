import DifferentialGeometry.Geometry.Surface.GaussCurvature
import DifferentialGeometry.Geometry.Metric.Conformal
import DifferentialGeometry.Geometry.Hodge.Codifferential
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.RicciConnDiffPalatini
import DifferentialGeometry.Geometry.Curvature.Bochner.OrthonormalFrameTrace
import DifferentialGeometry.Geometry.Curvature.Bochner.WeitzenbockIdentity
import DifferentialGeometry.Geometry.Connection.ChartBridge.Hessian
import DifferentialGeometry.Bundle.PartialMfderiv.Basic

set_option autoImplicit false
set_option linter.style.longLine false
set_option linter.unusedSectionVars false

noncomputable section

namespace DifferentialGeometry.Integral.Connection

open Bundle Tensor0SBundle Manifold Set FiberBundle
open DifferentialGeometry.Geometry.Riemannian.Forms
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.PDE.DeTurck
open scoped Manifold ContDiff BigOperators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable [InnerProductSpace Real E] [FiniteDimensional Real E] [NeZero (Module.finrank Real E)]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H}
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
variable [IsManifold I 1 M] [IsManifold I ((∞ : WithTop ℕ∞) + 1) M]
variable [CompleteSpace E] [SigmaCompactSpace M] [T2Space M]
variable [I.Boundaryless] [BoundarylessManifold I M]


private lemma mdifferentiableAt_metric_inner_pair
    (g : SmoothRiemannianMetric I M)
    {X Y : (p : M) -> TangentSpace I p} {x : M}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x) :
    MDiffAt (fun y : M => g.inner y (X y) (Y y)) x := by
  have hg :
      MDifferentiableAt I
        (I.prod 𝓘(Real, E →L[Real] E →L[Real] Real))
        (fun y : M =>
          TotalSpace.mk' (E →L[Real] E →L[Real] Real)
            (E := fun y : M =>
              TangentSpace I y →L[Real] TangentSpace I y →L[Real] Real)
            y (g.inner y)) x :=
    g.contMDiff.mdifferentiableAt (by simp)
  have htotal :
      MDifferentiableAt I (I.prod 𝓘(Real, Real))
        (fun y : M =>
          TotalSpace.mk' Real (E := Bundle.Trivial M Real) y
            (g.inner y (X y) (Y y))) x := by
    exact MDifferentiableAt.clm_bundle_apply₂
      (F₁ := E) (F₂ := E) hg hX hY
  rw [mdifferentiableAt_totalSpace] at htotal
  exact htotal.2


private lemma hasMFDerivAt_exp_comp
    {h : M -> Real} {x : M} {h' : TangentSpace I x →L[Real] Real}
    (hh : HasMFDerivAt I 𝓘(Real, Real) h x h') :
    HasMFDerivAt I 𝓘(Real, Real) (fun y : M => Real.exp (h y)) x
      (Real.exp (h x) • h') := by
  refine ⟨Real.continuous_exp.continuousAt.comp hh.1, ?_⟩
  simpa [writtenInExtChartAt, Function.comp_def] using hh.2.exp


private def conformalOneForm (f : M -> Real) (g : SmoothRiemannianMetric I M) (x : M) :
    TangentSpace I x →L[Real] TangentSpace I x →L[Real] TangentSpace I x :=
  haveI : T2Space (TangentSpace I x) := inferInstanceAs (T2Space E)
  haveI : FiniteDimensional Real (TangentSpace I x) :=
    inferInstanceAs (FiniteDimensional Real E)
  LinearMap.toContinuousLinearMap
    { toFun := fun z =>
        (extDerivFun (I := I) f x).smulRight z
          + extDerivFun (I := I) f x z • ContinuousLinearMap.id Real (TangentSpace I x)
          - (g.inner x z).smulRight (gradFun (I := I) g f x)
      map_add' := fun z₁ z₂ => by
        ext u
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
          ContinuousLinearMap.id_apply, map_add]
        module
      map_smul' := fun c z => by
        ext u
        simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
          ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
          ContinuousLinearMap.id_apply, map_smul, RingHom.id_apply, smul_eq_mul]
        module }

private lemma conformalOneForm_apply
    (f : M -> Real) (g : SmoothRiemannianMetric I M) (x : M)
    (z u : TangentSpace I x) :
    conformalOneForm (I := I) f g x z u =
      extDerivFun (I := I) f x u • z + extDerivFun (I := I) f x z • u
        - g.inner x z u • gradFun (I := I) g f x := by
  have h : conformalOneForm (I := I) f g x z =
      (extDerivFun (I := I) f x).smulRight z
        + extDerivFun (I := I) f x z • ContinuousLinearMap.id Real (TangentSpace I x)
        - (g.inner x z).smulRight (gradFun (I := I) g f x) := rfl
  rw [h]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.id_apply]

private lemma conformalOneForm_apply_inner
    (f : M -> Real) (g : SmoothRiemannianMetric I M) (x : M)
    (z u : TangentSpace I x) :
    conformalOneForm (I := I) f g x z u =
      g.inner x (gradFun (I := I) g f x) u • z
        + g.inner x (gradFun (I := I) g f x) z • u
        - g.inner x z u • gradFun (I := I) g f x := by
  rw [conformalOneForm_apply]
  have hu : extDerivFun (I := I) f x u = g.inner x (gradFun (I := I) g f x) u := by
    rw [show extDerivFun (I := I) f x u = mfderiv I 𝓘(Real, Real) f x u from rfl]
    exact (inner_gradFun (I := I) g f x u).symm
  have hz : extDerivFun (I := I) f x z = g.inner x (gradFun (I := I) g f x) z := by
    rw [show extDerivFun (I := I) f x z = mfderiv I 𝓘(Real, Real) f x z from rfl]
    exact (inner_gradFun (I := I) g f x z).symm
  rw [hu, hz]

private lemma conformalOneForm_symm
    (f : M -> Real) (g : SmoothRiemannianMetric I M) (x : M)
    (z u : TangentSpace I x) :
    conformalOneForm (I := I) f g x z u = conformalOneForm (I := I) f g x u z := by
  rw [conformalOneForm_apply, conformalOneForm_apply, g.symm x z u]
  module


private def conformalConnection (f : M -> Real) (g : SmoothRiemannianMetric I M) :
    CovariantDerivative I E (TangentSpace I : M → Type _) where
  toFun := fun σ x => (LeviCivita (I := I) g).toFun σ x
    + conformalOneForm (I := I) f g x (σ x)
  isCovariantDerivativeOnUniv :=
    (LeviCivita (I := I) g).isCovariantDerivativeOnUniv.add_one_form
      (fun x => conformalOneForm (I := I) f g x)

private lemma conformalConnection_toFun_apply
    (f : M -> Real) (g : SmoothRiemannianMetric I M)
    (σ : Π b : M, TangentSpace I b) (x : M) (u : TangentSpace I x) :
    (conformalConnection (I := I) f g).toFun σ x u =
      (LeviCivita (I := I) g).toFun σ x u
        + conformalOneForm (I := I) f g x (σ x) u := by
  change ((LeviCivita (I := I) g).toFun σ x
    + conformalOneForm (I := I) f g x (σ x)) u = _
  rw [ContinuousLinearMap.add_apply]

private lemma conformalConnection_torsion_eq_zero
    (f : M -> Real) (g : SmoothRiemannianMetric I M) :
    (conformalConnection (I := I) f g).torsion = 0 := by
  rw [CovariantDerivative.torsion_eq_zero_iff]
  intro X Y x hX hY
  have hLC : (LeviCivita (I := I) g).toFun Y x (X x)
      - (LeviCivita (I := I) g).toFun X x (Y x) = VectorField.mlieBracket I X Y x :=
    (CovariantDerivative.torsion_eq_zero_iff (LeviCivita (I := I) g)).mp
      (LeviCivita_torsion_eq_zero (I := I) g) hX hY
  change (conformalConnection (I := I) f g).toFun Y x (X x)
      - (conformalConnection (I := I) f g).toFun X x (Y x) = VectorField.mlieBracket I X Y x
  rw [conformalConnection_toFun_apply, conformalConnection_toFun_apply,
    conformalOneForm_symm (I := I) f g x (Y x) (X x), ← hLC]
  abel

private lemma conformalConnection_isMetricCompatible
    (f : M -> Real) (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (g : SmoothRiemannianMetric I M) :
    IsMetricCompatible (conformalConnection (I := I) f g) (conformalMetric f hf g) := by
  intro Y Z x hY hZ _ v
  have hf_at : MDifferentiableAt I 𝓘(Real, Real) f x := hf.mdifferentiable (by simp) x
  have h2f : ContMDiff I 𝓘(Real, Real) ∞ (fun y : M => 2 * f y) :=
    contMDiff_const.mul hf
  have hφ : ContMDiff I 𝓘(Real, Real) ∞ (fun y : M => Real.exp (2 * f y)) :=
    Real.contDiff_exp.comp_contMDiff h2f
  have hφ_at : MDifferentiableAt I 𝓘(Real, Real) (fun y : M => Real.exp (2 * f y)) x :=
    hφ.mdifferentiable (by simp) x
  have hinner_at : MDifferentiableAt I 𝓘(Real, Real)
      (fun b : M => g.inner b (Y b) (Z b)) x :=
    mdifferentiableAt_metric_inner_pair (I := I) g hY hZ
  have hfun : (fun b : M => (conformalMetric f hf g).inner b (Y b) (Z b))
      = fun b : M => Real.exp (2 * f b) * g.inner b (Y b) (Z b) := by
    funext b
    rw [conformalMetric_inner]
  change extDerivFun (I := I) (fun b : M => (conformalMetric f hf g).inner b (Y b) (Z b)) x v
    = (conformalMetric f hf g).inner x ((conformalConnection (I := I) f g).toFun Y x v) (Z x)
      + (conformalMetric f hf g).inner x (Y x) ((conformalConnection (I := I) f g).toFun Z x v)
  rw [hfun]
  have hprod := extDerivFun_mul_at (I := I) (f := fun y : M => Real.exp (2 * f y))
    (g := fun b : M => g.inner b (Y b) (Z b)) v hφ_at hinner_at
  rw [hprod]
  have hmc' : extDerivFun (I := I) (fun b : M => g.inner b (Y b) (Z b)) x v
      = g.inner x ((LeviCivita (I := I) g).toFun Y x v) (Z x)
        + g.inner x (Y x) ((LeviCivita (I := I) g).toFun Z x v) :=
    (LeviCivita_isMetricCompatible (I := I) g).apply hY hZ v
  rw [hmc']
  have h2f_at : MDifferentiableAt I 𝓘(Real, Real) (fun y : M => 2 * f y) x :=
    h2f.mdifferentiable (by simp) x
  have hexp_d : extDerivFun (I := I) (fun y : M => Real.exp (2 * f y)) x v
      = Real.exp (2 * f x) * extDerivFun (I := I) (fun y : M => 2 * f y) x v := by
    have h0 : mfderiv I 𝓘(Real, Real) (fun y : M => Real.exp (2 * f y)) x
        = Real.exp (2 * f x) • mfderiv I 𝓘(Real, Real) (fun y : M => 2 * f y) x :=
      (hasMFDerivAt_exp_comp (I := I) h2f_at.hasMFDerivAt).mfderiv
    rw [extDerivFun, extDerivFun]
    simp only [NormedSpace.fromTangentSpace, ContinuousLinearMap.comp_apply]
    have happly := congrArg (fun L => L v) h0
    simpa [smul_eq_mul] using happly
  have h2f_d : extDerivFun (I := I) (fun y : M => 2 * f y) x v
      = 2 * extDerivFun (I := I) f x v := by
    rw [extDerivFun_const_mul (I := I) 2 hf_at, ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [hexp_d, h2f_d]
  have hYv : (conformalConnection (I := I) f g).toFun Y x v
      = (LeviCivita (I := I) g).toFun Y x v + conformalOneForm (I := I) f g x (Y x) v :=
    conformalConnection_toFun_apply (I := I) f g Y x v
  have hZv : (conformalConnection (I := I) f g).toFun Z x v
      = (LeviCivita (I := I) g).toFun Z x v + conformalOneForm (I := I) f g x (Z x) v :=
    conformalConnection_toFun_apply (I := I) f g Z x v
  rw [conformalMetric_inner, conformalMetric_inner, hYv, hZv,
    conformalOneForm_apply_inner, conformalOneForm_apply_inner]
  have hmf_v : extDerivFun (I := I) f x v
      = g.inner x (gradFun (I := I) g f x) v := (inner_gradFun (I := I) g f x v).symm
  rw [hmf_v]
  have hsplit₁ : g.inner x ((LeviCivita (I := I) g).toFun Y x v
        + (g.inner x (gradFun (I := I) g f x) v • Y x
            + g.inner x (gradFun (I := I) g f x) (Y x) • v
            - g.inner x (Y x) v • gradFun (I := I) g f x)) (Z x)
      = g.inner x ((LeviCivita (I := I) g).toFun Y x v) (Z x)
        + (g.inner x (gradFun (I := I) g f x) v * g.inner x (Y x) (Z x)
            + g.inner x (gradFun (I := I) g f x) (Y x) * g.inner x v (Z x)
            - g.inner x (Y x) v * g.inner x (gradFun (I := I) g f x) (Z x)) := by
    simp only [map_add, map_sub, map_smul, ContinuousLinearMap.add_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  have hsplit₂ : g.inner x (Y x) ((LeviCivita (I := I) g).toFun Z x v
        + (g.inner x (gradFun (I := I) g f x) v • Z x
            + g.inner x (gradFun (I := I) g f x) (Z x) • v
            - g.inner x (Z x) v • gradFun (I := I) g f x))
      = g.inner x (Y x) ((LeviCivita (I := I) g).toFun Z x v)
        + (g.inner x (gradFun (I := I) g f x) v * g.inner x (Y x) (Z x)
            + g.inner x (gradFun (I := I) g f x) (Z x) * g.inner x (Y x) v
            - g.inner x (Z x) v * g.inner x (Y x) (gradFun (I := I) g f x)) := by
    simp only [map_add, map_sub, map_smul, smul_eq_mul]
  rw [hsplit₁, hsplit₂]
  have hsym₁ : g.inner x (Z x) v = g.inner x v (Z x) := g.symm x (Z x) v
  have hsym₂ : g.inner x (Y x) (gradFun (I := I) g f x)
      = g.inner x (gradFun (I := I) g f x) (Y x) :=
    g.symm x (Y x) (gradFun (I := I) g f x)
  rw [hsym₁, hsym₂]
  ring


private lemma leviCivita_conformalMetric_toFun_apply
    (f : M -> Real) (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (g : SmoothRiemannianMetric I M)
    {σ : Π b : M, TangentSpace I b} {x : M}
    (hσ : MDiffAt (T% σ) x) (u : TangentSpace I x) :
    (LeviCivita (I := I) (conformalMetric f hf g)).toFun σ x u =
      (LeviCivita (I := I) g).toFun σ x u
        + conformalOneForm (I := I) f g x (σ x) u := by
  have h := LeviCivita_unique (I := I) (g := conformalMetric f hf g)
    (conformalConnection (I := I) f g)
    (conformalConnection_torsion_eq_zero (I := I) f g)
    (conformalConnection_isMetricCompatible (I := I) f hf g)
    hσ u
  rw [← h]
  exact conformalConnection_toFun_apply (I := I) f g σ x u

private lemma connDiff_conformalMetric_apply
    (f : M -> Real) (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (g : SmoothRiemannianMetric I M) (x : M) (z u : TangentSpace I x) :
    connDiff (I := I) (conformalMetric f hf g) g x z u =
      g.inner x (gradFun (I := I) g f x) u • z
        + g.inner x (gradFun (I := I) g f x) z • u
        - g.inner x z u • gradFun (I := I) g f x := by
  classical
  obtain ⟨σ, hσx⟩ := ContMDiffSection.exists_eq_at (I := I) (n := (⊤ : ℕ∞))
    (F := E) (V := (TangentSpace I : M → Type _)) x z
  have hσ : MDiffAt (T% (fun y => σ y)) x := σ.mdifferentiableAt
  have h1 : connDiff (I := I) (conformalMetric f hf g) g x (σ x) u =
      (LeviCivita (I := I) (conformalMetric f hf g)).toFun (fun y => σ y) x u
        - (LeviCivita (I := I) g).toFun (fun y => σ y) x u :=
    connDiff_apply (I := I) (conformalMetric f hf g) g hσ u
  rw [leviCivita_conformalMetric_toFun_apply (I := I) f hf g hσ u] at h1
  rw [hσx] at h1
  rw [h1, ← conformalOneForm_apply_inner (I := I) f g x z u]
  abel


private lemma covDerivConnDiff_conformalMetric_apply
    (f : M -> Real) (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (g : SmoothRiemannianMetric I M)
    {X Y Z : Π b : M, TangentSpace I b}
    (hX : ContMDiff I (I.prod 𝓘(Real, E)) ∞ (T% X))
    (hY : ContMDiff I (I.prod 𝓘(Real, E)) ∞ (T% Y))
    (hZ : ContMDiff I (I.prod 𝓘(Real, E)) ∞ (T% Z)) (x : M) :
    covDerivConnDiff (I := I) g (conformalMetric f hf g) X Y Z x =
      g.inner x ((LeviCivita (I := I) g).toFun (fun b => gradFun (I := I) g f b) x (X x)) (Y x) • Z x
        + g.inner x ((LeviCivita (I := I) g).toFun (fun b => gradFun (I := I) g f b) x (X x)) (Z x) • Y x
        - g.inner x (Z x) (Y x) • (LeviCivita (I := I) g).toFun (fun b => gradFun (I := I) g f b) x (X x) := by
  classical
  have hX_at : MDiffAt (T% X) x := (hX x).mdifferentiableAt (by simp)
  have hY_at : MDiffAt (T% Y) x := (hY x).mdifferentiableAt (by simp)
  have hZ_at : MDiffAt (T% Z) x := (hZ x).mdifferentiableAt (by simp)
  have hP_sm : ContMDiff I (I.prod 𝓘(Real, E)) ∞ (T% (fun b : M => gradFun (I := I) g f b)) :=
    gradFun_contMDiff_total (I := I) g hf
  have hP_at : MDiffAt (T% (fun b : M => gradFun (I := I) g f b)) x :=
    (hP_sm x).mdifferentiableAt (by simp)
  have hh₁_at : MDiffAt (fun b : M => g.inner b (gradFun (I := I) g f b) (Y b)) x :=
    mdifferentiableAt_metric_inner_pair (I := I) g hP_at hY_at
  have hh₂_at : MDiffAt (fun b : M => g.inner b (gradFun (I := I) g f b) (Z b)) x :=
    mdifferentiableAt_metric_inner_pair (I := I) g hP_at hZ_at
  have hZY_at : MDiffAt (fun b : M => g.inner b (Z b) (Y b)) x :=
    mdifferentiableAt_metric_inner_pair (I := I) g hZ_at hY_at
  have hh₃_at : MDiffAt (fun b : M => -(g.inner b (Z b) (Y b))) x := by
    have heq : (fun b : M => -(g.inner b (Z b) (Y b)))
        = fun b : M => (-1 : Real) * g.inner b (Z b) (Y b) := by
      funext b; ring
    rw [heq]
    exact (mdifferentiableAt_const (I := I) (I' := 𝓘(Real, Real)) (c := (-1 : Real))).mul hZY_at
  have hsec : diffSec (LeviCivita (I := I) g) (LeviCivita (I := I) (conformalMetric f hf g)) Y Z
      = (fun b : M => g.inner b (gradFun (I := I) g f b) (Y b)) • Z
        + ((fun b : M => g.inner b (gradFun (I := I) g f b) (Z b)) • Y
          + (fun b : M => -(g.inner b (Z b) (Y b))) • (fun b : M => gradFun (I := I) g f b)) := by
    funext b
    change connDiff (I := I) (conformalMetric f hf g) g b (Z b) (Y b)
      = g.inner b (gradFun (I := I) g f b) (Y b) • Z b
        + (g.inner b (gradFun (I := I) g f b) (Z b) • Y b
          + -(g.inner b (Z b) (Y b)) • gradFun (I := I) g f b)
    rw [connDiff_conformalMetric_apply (I := I) f hf g b (Z b) (Y b)]
    module
  have hcov1 : MDiffAt (T% ((fun b : M => g.inner b (gradFun (I := I) g f b) (Y b)) • Z)) x :=
    hh₁_at.smul_section hZ_at
  have hcov2 : MDiffAt (T% ((fun b : M => g.inner b (gradFun (I := I) g f b) (Z b)) • Y)) x :=
    hh₂_at.smul_section hY_at
  have hcov3 : MDiffAt (T% ((fun b : M => -(g.inner b (Z b) (Y b)))
      • (fun b : M => gradFun (I := I) g f b))) x :=
    hh₃_at.smul_section hP_at
  have hcov23 : MDiffAt (T% ((fun b : M => g.inner b (gradFun (I := I) g f b) (Z b)) • Y
      + (fun b : M => -(g.inner b (Z b) (Y b))) • (fun b : M => gradFun (I := I) g f b))) x :=
    mdifferentiableAt_add_section hcov2 hcov3
  have hstep : (LeviCivita (I := I) g).toFun
        (diffSec (LeviCivita (I := I) g) (LeviCivita (I := I) (conformalMetric f hf g)) Y Z) x
      = (LeviCivita (I := I) g).toFun
          ((fun b : M => g.inner b (gradFun (I := I) g f b) (Y b)) • Z) x
        + ((LeviCivita (I := I) g).toFun
            ((fun b : M => g.inner b (gradFun (I := I) g f b) (Z b)) • Y) x
          + (LeviCivita (I := I) g).toFun
            ((fun b : M => -(g.inner b (Z b) (Y b))) • (fun b : M => gradFun (I := I) g f b)) x) := by
    rw [hsec]
    rw [(LeviCivita (I := I) g).isCovariantDerivativeOnUniv.add hcov1 hcov23]
    rw [(LeviCivita (I := I) g).isCovariantDerivativeOnUniv.add hcov2 hcov3]
  have hleib₁ := (LeviCivita (I := I) g).isCovariantDerivativeOnUniv.leibniz
    (σ := Z) (g := fun b : M => g.inner b (gradFun (I := I) g f b) (Y b)) hZ_at hh₁_at
  have hleib₂ := (LeviCivita (I := I) g).isCovariantDerivativeOnUniv.leibniz
    (σ := Y) (g := fun b : M => g.inner b (gradFun (I := I) g f b) (Z b)) hY_at hh₂_at
  have hleib₃ := (LeviCivita (I := I) g).isCovariantDerivativeOnUniv.leibniz
    (σ := fun b : M => gradFun (I := I) g f b)
    (g := fun b : M => -(g.inner b (Z b) (Y b))) hP_at hh₃_at
  have hd₁ : extDerivFun (I := I) (fun b : M => g.inner b (gradFun (I := I) g f b) (Y b)) x (X x)
      = g.inner x ((LeviCivita (I := I) g).toFun (fun b : M => gradFun (I := I) g f b) x (X x)) (Y x)
        + g.inner x (gradFun (I := I) g f x) ((LeviCivita (I := I) g).toFun Y x (X x)) :=
    (LeviCivita_isMetricCompatible (I := I) g).apply hP_at hY_at (X x)
  have hd₂ : extDerivFun (I := I) (fun b : M => g.inner b (gradFun (I := I) g f b) (Z b)) x (X x)
      = g.inner x ((LeviCivita (I := I) g).toFun (fun b : M => gradFun (I := I) g f b) x (X x)) (Z x)
        + g.inner x (gradFun (I := I) g f x) ((LeviCivita (I := I) g).toFun Z x (X x)) :=
    (LeviCivita_isMetricCompatible (I := I) g).apply hP_at hZ_at (X x)
  have hd₃ : extDerivFun (I := I) (fun b : M => -(g.inner b (Z b) (Y b))) x (X x)
      = -(g.inner x ((LeviCivita (I := I) g).toFun Z x (X x)) (Y x)
          + g.inner x (Z x) ((LeviCivita (I := I) g).toFun Y x (X x))) := by
    have heq : (fun b : M => -(g.inner b (Z b) (Y b)))
        = fun b : M => (-1 : Real) * g.inner b (Z b) (Y b) := by
      funext b; ring
    rw [heq, extDerivFun_const_mul (I := I) (-1) hZY_at, ContinuousLinearMap.smul_apply,
      smul_eq_mul]
    have hb : extDerivFun (I := I) (fun b : M => g.inner b (Z b) (Y b)) x (X x)
        = mfderiv I 𝓘(Real) (fun b : M => g.inner b (Z b) (Y b)) x (X x) := rfl
    rw [hb, (LeviCivita_isMetricCompatible (I := I) g).apply hZ_at hY_at (X x)]
    ring
  have hfirst : (LeviCivita (I := I) g).toFun
        (diffSec (LeviCivita (I := I) g) (LeviCivita (I := I) (conformalMetric f hf g)) Y Z) x (X x)
      = (g.inner x (gradFun (I := I) g f x) (Y x) • (LeviCivita (I := I) g).toFun Z x (X x)
          + extDerivFun (I := I) (fun b : M => g.inner b (gradFun (I := I) g f b) (Y b)) x (X x) • Z x)
        + ((g.inner x (gradFun (I := I) g f x) (Z x) • (LeviCivita (I := I) g).toFun Y x (X x)
            + extDerivFun (I := I) (fun b : M => g.inner b (gradFun (I := I) g f b) (Z b)) x (X x) • Y x)
          + ((-(g.inner x (Z x) (Y x))) • (LeviCivita (I := I) g).toFun (fun b : M => gradFun (I := I) g f b) x (X x)
            + extDerivFun (I := I) (fun b : M => -(g.inner b (Z b) (Y b))) x (X x) • gradFun (I := I) g f x)) := by
    rw [hstep]
    rw [show ((LeviCivita (I := I) g).toFun
          ((fun b : M => g.inner b (gradFun (I := I) g f b) (Y b)) • Z) x
        + ((LeviCivita (I := I) g).toFun
            ((fun b : M => g.inner b (gradFun (I := I) g f b) (Z b)) • Y) x
          + (LeviCivita (I := I) g).toFun
            ((fun b : M => -(g.inner b (Z b) (Y b))) • (fun b : M => gradFun (I := I) g f b)) x)) (X x)
      = (LeviCivita (I := I) g).toFun
          ((fun b : M => g.inner b (gradFun (I := I) g f b) (Y b)) • Z) x (X x)
        + ((LeviCivita (I := I) g).toFun
            ((fun b : M => g.inner b (gradFun (I := I) g f b) (Z b)) • Y) x (X x)
          + (LeviCivita (I := I) g).toFun
            ((fun b : M => -(g.inner b (Z b) (Y b))) • (fun b : M => gradFun (I := I) g f b)) x (X x))
      from by simp only [ContinuousLinearMap.add_apply]]
    rw [hleib₁, hleib₂, hleib₃]
    simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.smulRight_apply]
  have hexpand : covDerivConnDiff (I := I) g (conformalMetric f hf g) X Y Z x
      = (LeviCivita (I := I) g).toFun
          (diffSec (LeviCivita (I := I) g) (LeviCivita (I := I) (conformalMetric f hf g)) Y Z) x (X x)
        - CovariantDerivative.difference (LeviCivita (I := I) (conformalMetric f hf g))
            (LeviCivita (I := I) g) x (Z x) (covApply (LeviCivita (I := I) g) X Y x)
        - CovariantDerivative.difference (LeviCivita (I := I) (conformalMetric f hf g))
            (LeviCivita (I := I) g) x (covApply (LeviCivita (I := I) g) X Z x) (Y x) := rfl
  rw [hexpand, hfirst, hd₁, hd₂, hd₃]
  rw [show CovariantDerivative.difference (LeviCivita (I := I) (conformalMetric f hf g))
        (LeviCivita (I := I) g) x (Z x) (covApply (LeviCivita (I := I) g) X Y x)
      = connDiff (I := I) (conformalMetric f hf g) g x (Z x) (covApply (LeviCivita (I := I) g) X Y x)
      from rfl]
  rw [show CovariantDerivative.difference (LeviCivita (I := I) (conformalMetric f hf g))
        (LeviCivita (I := I) g) x (covApply (LeviCivita (I := I) g) X Z x) (Y x)
      = connDiff (I := I) (conformalMetric f hf g) g x (covApply (LeviCivita (I := I) g) X Z x) (Y x)
      from rfl]
  rw [connDiff_conformalMetric_apply (I := I) f hf g x (Z x) (covApply (LeviCivita (I := I) g) X Y x)]
  rw [connDiff_conformalMetric_apply (I := I) f hf g x (covApply (LeviCivita (I := I) g) X Z x) (Y x)]
  simp only [covApply_apply]
  module


private def basisVec (x : M) (i : Fin (Module.finrank Real E)) : TangentSpace I x :=
  (chartModelBasis E) i

private lemma sum_repr_mul_apply (φ : E →L[Real] Real) (u : E) :
    ∑ i : Fin (Module.finrank Real E),
      (chartModelBasis E).repr u i * φ ((chartModelBasis E) i) = φ u := by
  classical
  conv_rhs => rw [← (chartModelBasis E).sum_repr u]
  rw [map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [map_smul, smul_eq_mul]

private lemma sum_repr_basis_diag :
    ∑ i : Fin (Module.finrank Real E),
      (chartModelBasis E).repr ((chartModelBasis E) i) i = (Module.finrank Real E : Real) := by
  classical
  have h : ∀ i : Fin (Module.finrank Real E),
      (chartModelBasis E).repr ((chartModelBasis E) i) i = 1 := by
    intro i
    rw [Module.Basis.repr_self]
    exact Finsupp.single_eq_same
  rw [Finset.sum_congr rfl (fun i _ => h i)]
  simp

private lemma repr_three_combination (a b c : Real) (u v' w' : E)
    (i : Fin (Module.finrank Real E)) :
    (chartModelBasis E).repr (a • u + b • v' - c • w') i =
      a * (chartModelBasis E).repr u i + b * (chartModelBasis E).repr v' i
        - c * (chartModelBasis E).repr w' i := by
  rw [map_sub, map_add, map_smul, map_smul, map_smul]
  rw [Finsupp.sub_apply, Finsupp.add_apply, Finsupp.smul_apply, Finsupp.smul_apply,
    Finsupp.smul_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul]

private lemma bilin_three_combination_right (B : E →L[Real] E →L[Real] Real)
    (s : E) (a b c : Real) (u v' w' : E) :
    B s (a • u + b • v' - c • w') = a * B s u + b * B s v' - c * B s w' := by
  simp only [map_add, map_sub, map_smul, smul_eq_mul]

private lemma bilin_three_combination_left (B : E →L[Real] E →L[Real] Real)
    (a b c : Real) (u v' w' t : E) :
    B (a • u + b • v' - c • w') t = a * B u t + b * B v' t - c * B w' t := by
  simp only [map_add, map_sub, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]

private lemma palatini_sum_hessian (B : E →L[Real] E →L[Real] Real)
    (Q : E →L[Real] E) (v w : E) (Δval : Real)
    (hQ : ∑ i : Fin (Module.finrank Real E),
      (chartModelBasis E).repr (Q ((chartModelBasis E) i)) i = Δval) :
    ∑ i : Fin (Module.finrank Real E),
      (chartModelBasis E).repr
        (B (Q ((chartModelBasis E) i)) v • w + B (Q ((chartModelBasis E) i)) w • v
          - B w v • Q ((chartModelBasis E) i)) i
      = B (Q w) v + B (Q v) w - B w v * Δval := by
  classical
  calc ∑ i : Fin (Module.finrank Real E),
      (chartModelBasis E).repr
        (B (Q ((chartModelBasis E) i)) v • w + B (Q ((chartModelBasis E) i)) w • v
          - B w v • Q ((chartModelBasis E) i)) i
      = ∑ i : Fin (Module.finrank Real E),
          (B (Q ((chartModelBasis E) i)) v * (chartModelBasis E).repr w i
            + B (Q ((chartModelBasis E) i)) w * (chartModelBasis E).repr v i
            - B w v * (chartModelBasis E).repr (Q ((chartModelBasis E) i)) i) :=
        Finset.sum_congr rfl (fun i _ => repr_three_combination _ _ _ _ _ _ i)
    _ = (∑ i : Fin (Module.finrank Real E),
            B (Q ((chartModelBasis E) i)) v * (chartModelBasis E).repr w i)
        + (∑ i : Fin (Module.finrank Real E),
            B (Q ((chartModelBasis E) i)) w * (chartModelBasis E).repr v i)
        - ∑ i : Fin (Module.finrank Real E),
            B w v * (chartModelBasis E).repr (Q ((chartModelBasis E) i)) i := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ = B (Q w) v + B (Q v) w - B w v * Δval := by
        have hA : ∑ i : Fin (Module.finrank Real E),
            B (Q ((chartModelBasis E) i)) v * (chartModelBasis E).repr w i
            = B (Q w) v := by
          have hφ := sum_repr_mul_apply ((B.flip v).comp Q) w
          simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply] at hφ
          rw [← hφ]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          ring
        have hBsum : ∑ i : Fin (Module.finrank Real E),
            B (Q ((chartModelBasis E) i)) w * (chartModelBasis E).repr v i
            = B (Q v) w := by
          have hφ := sum_repr_mul_apply ((B.flip w).comp Q) v
          simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply] at hφ
          rw [← hφ]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          ring
        have hC : ∑ i : Fin (Module.finrank Real E),
            B w v * (chartModelBasis E).repr (Q ((chartModelBasis E) i)) i
            = B w v * Δval := by
          rw [← Finset.mul_sum, hQ]
        rw [hA, hBsum, hC]

private lemma palatini_sum_oneForm (B : E →L[Real] E →L[Real] Real)
    (hB : ∀ a b : E, B a b = B b a) (q w' : E) :
    ∑ i : Fin (Module.finrank Real E),
      (chartModelBasis E).repr
        (B q ((chartModelBasis E) i) • w' + B q w' • ((chartModelBasis E) i)
          - B w' ((chartModelBasis E) i) • q) i
      = (Module.finrank Real E : Real) * B q w' := by
  classical
  calc ∑ i : Fin (Module.finrank Real E),
      (chartModelBasis E).repr
        (B q ((chartModelBasis E) i) • w' + B q w' • ((chartModelBasis E) i)
          - B w' ((chartModelBasis E) i) • q) i
      = ∑ i : Fin (Module.finrank Real E),
          (B q ((chartModelBasis E) i) * (chartModelBasis E).repr w' i
            + B q w' * (chartModelBasis E).repr ((chartModelBasis E) i) i
            - B w' ((chartModelBasis E) i) * (chartModelBasis E).repr q i) :=
        Finset.sum_congr rfl (fun i _ => repr_three_combination _ _ _ _ _ _ i)
    _ = (∑ i : Fin (Module.finrank Real E),
            B q ((chartModelBasis E) i) * (chartModelBasis E).repr w' i)
        + (∑ i : Fin (Module.finrank Real E),
            B q w' * (chartModelBasis E).repr ((chartModelBasis E) i) i)
        - ∑ i : Fin (Module.finrank Real E),
            B w' ((chartModelBasis E) i) * (chartModelBasis E).repr q i := by
        rw [Finset.sum_sub_distrib, Finset.sum_add_distrib]
    _ = (Module.finrank Real E : Real) * B q w' := by
        have hA : ∑ i : Fin (Module.finrank Real E),
            B q ((chartModelBasis E) i) * (chartModelBasis E).repr w' i
            = B q w' := by
          have hφ := sum_repr_mul_apply (B q) w'
          rw [← hφ]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          ring
        have hBs : ∑ i : Fin (Module.finrank Real E),
            B q w' * (chartModelBasis E).repr ((chartModelBasis E) i) i
            = B q w' * (Module.finrank Real E : Real) := by
          rw [← Finset.mul_sum, sum_repr_basis_diag]
        have hC : ∑ i : Fin (Module.finrank Real E),
            B w' ((chartModelBasis E) i) * (chartModelBasis E).repr q i
            = B q w' := by
          have hφ := sum_repr_mul_apply (B w') q
          rw [show B q w' = B w' q from hB q w', ← hφ]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          ring
        rw [hA, hBs, hC]
        ring

private lemma palatini_sum_oneForm_sq (B : E →L[Real] E →L[Real] Real)
    (hB : ∀ a b : E, B a b = B b a) (p v w : E) :
    ∑ i : Fin (Module.finrank Real E),
      (chartModelBasis E).repr
        (B p v •
            (B p ((chartModelBasis E) i) • w + B p w • ((chartModelBasis E) i)
              - B w ((chartModelBasis E) i) • p)
          + B p (B p ((chartModelBasis E) i) • w + B p w • ((chartModelBasis E) i)
              - B w ((chartModelBasis E) i) • p) • v
          - B (B p ((chartModelBasis E) i) • w + B p w • ((chartModelBasis E) i)
              - B w ((chartModelBasis E) i) • p) v • p) i
      = (Module.finrank Real E : Real) * (B p v * B p w)
        + 2 * (B p v * B p w) - 2 * (B p p * B w v) := by
  classical
  have hstep : ∀ i : Fin (Module.finrank Real E),
      (chartModelBasis E).repr
        (B p v •
            (B p ((chartModelBasis E) i) • w + B p w • ((chartModelBasis E) i)
              - B w ((chartModelBasis E) i) • p)
          + B p (B p ((chartModelBasis E) i) • w + B p w • ((chartModelBasis E) i)
              - B w ((chartModelBasis E) i) • p) • v
          - B (B p ((chartModelBasis E) i) • w + B p w • ((chartModelBasis E) i)
              - B w ((chartModelBasis E) i) • p) v • p) i
      = B p v * (B p ((chartModelBasis E) i) * (chartModelBasis E).repr w i)
        + (B p v * B p w) * (chartModelBasis E).repr ((chartModelBasis E) i) i
        + 2 * B p w * (B p ((chartModelBasis E) i) * (chartModelBasis E).repr v i)
        - B p p * (B w ((chartModelBasis E) i) * (chartModelBasis E).repr v i)
        - B w v * (B p ((chartModelBasis E) i) * (chartModelBasis E).repr p i)
        - B p w * (B v ((chartModelBasis E) i) * (chartModelBasis E).repr p i) := by
    intro i
    rw [repr_three_combination, repr_three_combination,
      bilin_three_combination_right B p, bilin_three_combination_left B]
    rw [hB ((chartModelBasis E) i) v]
    ring
  calc ∑ i : Fin (Module.finrank Real E),
      (chartModelBasis E).repr
        (B p v •
            (B p ((chartModelBasis E) i) • w + B p w • ((chartModelBasis E) i)
              - B w ((chartModelBasis E) i) • p)
          + B p (B p ((chartModelBasis E) i) • w + B p w • ((chartModelBasis E) i)
              - B w ((chartModelBasis E) i) • p) • v
          - B (B p ((chartModelBasis E) i) • w + B p w • ((chartModelBasis E) i)
              - B w ((chartModelBasis E) i) • p) v • p) i
      = ∑ i : Fin (Module.finrank Real E),
          (B p v * (B p ((chartModelBasis E) i) * (chartModelBasis E).repr w i)
            + (B p v * B p w) * (chartModelBasis E).repr ((chartModelBasis E) i) i
            + 2 * B p w * (B p ((chartModelBasis E) i) * (chartModelBasis E).repr v i)
            - B p p * (B w ((chartModelBasis E) i) * (chartModelBasis E).repr v i)
            - B w v * (B p ((chartModelBasis E) i) * (chartModelBasis E).repr p i)
            - B p w * (B v ((chartModelBasis E) i) * (chartModelBasis E).repr p i)) :=
        Finset.sum_congr rfl (fun i _ => hstep i)
    _ = (Module.finrank Real E : Real) * (B p v * B p w)
        + 2 * (B p v * B p w) - 2 * (B p p * B w v) := by
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
          Finset.sum_add_distrib, Finset.sum_add_distrib]
        have h₁ : ∑ i : Fin (Module.finrank Real E),
            B p v * (B p ((chartModelBasis E) i) * (chartModelBasis E).repr w i)
            = B p v * B p w := by
          rw [← Finset.mul_sum]
          congr 1
          have hφ := sum_repr_mul_apply (B p) w
          rw [← hφ]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          ring
        have h₂ : ∑ i : Fin (Module.finrank Real E),
            (B p v * B p w) * (chartModelBasis E).repr ((chartModelBasis E) i) i
            = (B p v * B p w) * (Module.finrank Real E : Real) := by
          rw [← Finset.mul_sum, sum_repr_basis_diag]
        have h₃ : ∑ i : Fin (Module.finrank Real E),
            2 * B p w * (B p ((chartModelBasis E) i) * (chartModelBasis E).repr v i)
            = 2 * B p w * B p v := by
          rw [← Finset.mul_sum]
          congr 1
          have hφ := sum_repr_mul_apply (B p) v
          rw [← hφ]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          ring
        have h₄ : ∑ i : Fin (Module.finrank Real E),
            B p p * (B w ((chartModelBasis E) i) * (chartModelBasis E).repr v i)
            = B p p * B w v := by
          rw [← Finset.mul_sum]
          congr 1
          have hφ := sum_repr_mul_apply (B w) v
          rw [← hφ]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          ring
        have h₅ : ∑ i : Fin (Module.finrank Real E),
            B w v * (B p ((chartModelBasis E) i) * (chartModelBasis E).repr p i)
            = B w v * B p p := by
          rw [← Finset.mul_sum]
          congr 1
          have hφ := sum_repr_mul_apply (B p) p
          rw [← hφ]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          ring
        have h₆ : ∑ i : Fin (Module.finrank Real E),
            B p w * (B v ((chartModelBasis E) i) * (chartModelBasis E).repr p i)
            = B p w * B v p := by
          rw [← Finset.mul_sum]
          congr 1
          have hφ := sum_repr_mul_apply (B v) p
          rw [← hφ]
          refine Finset.sum_congr rfl (fun i _ => ?_)
          ring
        rw [h₁, h₂, h₃, h₄, h₅, h₆, hB v p]
        ring

private lemma conformal_palatini_sum_collapse (B : E →L[Real] E →L[Real] Real)
    (hB : ∀ a b : E, B a b = B b a)
    (Q : E →L[Real] E) (p v w : E) (Δval : Real)
    (hQ : ∑ i : Fin (Module.finrank Real E),
      (chartModelBasis E).repr (Q ((chartModelBasis E) i)) i = Δval)
    (hn : (Module.finrank Real E : Real) = 2)
    (hQsym : B (Q w) v = B (Q v) w) :
    ∑ i : Fin (Module.finrank Real E),
      (chartModelBasis E).repr
        ((B (Q ((chartModelBasis E) i)) v • w + B (Q ((chartModelBasis E) i)) w • v
            - B w v • Q ((chartModelBasis E) i)
          - (B (Q v) ((chartModelBasis E) i) • w + B (Q v) w • ((chartModelBasis E) i)
              - B w ((chartModelBasis E) i) • Q v))
         + ((B p ((chartModelBasis E) i) • (B p v • w + B p w • v - B w v • p)
              + B p (B p v • w + B p w • v - B w v • p) • ((chartModelBasis E) i)
              - B (B p v • w + B p w • v - B w v • p) ((chartModelBasis E) i) • p)
            - (B p v •
                  (B p ((chartModelBasis E) i) • w + B p w • ((chartModelBasis E) i)
                    - B w ((chartModelBasis E) i) • p)
                + B p (B p ((chartModelBasis E) i) • w + B p w • ((chartModelBasis E) i)
                    - B w ((chartModelBasis E) i) • p) • v
                - B (B p ((chartModelBasis E) i) • w + B p w • ((chartModelBasis E) i)
                    - B w ((chartModelBasis E) i) • p) v • p))) i
      = -(B w v * Δval) := by
  classical
  have hsplit : ∀ (t1 t2 t3 t4 : E) (i : Fin (Module.finrank Real E)),
      (chartModelBasis E).repr (t1 - t2 + (t3 - t4)) i
        = (chartModelBasis E).repr t1 i - (chartModelBasis E).repr t2 i
          + ((chartModelBasis E).repr t3 i - (chartModelBasis E).repr t4 i) := by
    intro t1 t2 t3 t4 i
    rw [map_add, map_sub, map_sub, Finsupp.add_apply, Finsupp.sub_apply, Finsupp.sub_apply]
  simp only [hsplit]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  rw [palatini_sum_hessian B Q v w Δval hQ]
  rw [palatini_sum_oneForm B hB (Q v) w]
  rw [palatini_sum_oneForm B hB p (B p v • w + B p w • v - B w v • p)]
  rw [palatini_sum_oneForm_sq B hB p v w]
  rw [bilin_three_combination_right B p (B p v) (B p w) (B w v) w v p]
  rw [hQsym, hn]
  ring


private lemma sum_repr_covGrad_eq_laplacian
    (f : M -> Real) (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (g : SmoothRiemannianMetric I M) (x : M) :
    ∑ i : Fin (Module.finrank Real E),
      (chartModelBasis E).repr
        ((LeviCivita (I := I) g).toFun (fun b : M => gradFun (I := I) g f b) x
          ((chartModelBasis E) i)) i
      = Δ_g (I := I) g hf x := by
  classical
  haveI : FiniteDimensional Real (TangentSpace I x) :=
    inferInstanceAs (FiniteDimensional Real E)
  set T : TangentSpace I x →ₗ[Real] TangentSpace I x :=
    ((LeviCivita (I := I) g).toFun (fun b : M => gradFun (I := I) g f b) x
      : TangentSpace I x →L[Real] TangentSpace I x).toLinearMap with hT
  have h1 : LinearMap.trace Real (TangentSpace I x) T
      = ∑ i : Fin (Module.finrank Real E),
          (chartModelBasis E).repr
            ((LeviCivita (I := I) g).toFun (fun b : M => gradFun (I := I) g f b) x
              ((chartModelBasis E) i)) i := by
    rw [LinearMap.trace_eq_matrix_trace Real (chartModelBasis (TangentSpace I x)) T]
    unfold Matrix.trace
    refine Finset.sum_congr rfl ?_
    intro k _
    simp only [Matrix.diag_apply]
    rw [LinearMap.toMatrix_apply]
    rfl
  rw [← h1]
  rw [trace_eq_ortho_sum (I := I) g x T
    (fun i => smoothOrthoFrame (I := I) g x i x)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j)]
  rw [← sum_abstractHessian_orthonormal_eq_laplacian (I := I) g hf x
    (fun i => smoothOrthoFrame (I := I) g x i x)
    (fun i j => smoothOrthoFrame_orthonormal_at_center (I := I) g x i j)]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  exact abstractHessian_eq_inner_cov_gradFun_extend (I := I) g hf x
    (smoothOrthoFrame (I := I) g x i x) (smoothOrthoFrame (I := I) g x i x)


theorem ricciTensor_conformalMetric_twoDim
    (hdim : Module.finrank Real E = 2)
    (f : M -> Real) (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    ricciTensor (I := I) (conformalMetric f hf g) x v w
      = ricciTensor (I := I) g x v w
        + formLaplacianScalar (I := I) g hf x * g.inner x v w := by
  classical
  have hpal := ricciTensor_sub_eq_connDiff_palatini (I := I) g (conformalMetric f hf g) x v w
  have hV_sm : ContMDiff I (I.prod 𝓘(Real, E)) ∞ (T% (smoothExtensionTangent (I := I) x v)) :=
    smoothExtensionTangent_contMDiff (I := I) x v
  have hW_sm : ContMDiff I (I.prod 𝓘(Real, E)) ∞ (T% (smoothExtensionTangent (I := I) x w)) :=
    smoothExtensionTangent_contMDiff (I := I) x w
  have he1 : ∀ i : Fin (Module.finrank Real E),
      covDerivConnDiff (I := I) g (conformalMetric f hf g)
        (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
        (smoothExtensionTangent (I := I) x v)
        (smoothExtensionTangent (I := I) x w) x
      = g.inner x ((LeviCivita (I := I) g).toFun (fun b : M => gradFun (I := I) g f b) x
            ((chartModelBasis E) i)) v • w
        + g.inner x ((LeviCivita (I := I) g).toFun (fun b : M => gradFun (I := I) g f b) x
            ((chartModelBasis E) i)) w • v
        - g.inner x w v • (LeviCivita (I := I) g).toFun (fun b : M => gradFun (I := I) g f b) x
            ((chartModelBasis E) i) := by
    intro i
    rw [covDerivConnDiff_conformalMetric_apply (I := I) f hf g
      (smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)) hV_sm hW_sm x]
    simp only [smoothExtensionTangent_eq]
  have he2 : ∀ i : Fin (Module.finrank Real E),
      covDerivConnDiff (I := I) g (conformalMetric f hf g)
        (smoothExtensionTangent (I := I) x v)
        (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
        (smoothExtensionTangent (I := I) x w) x
      = g.inner x ((LeviCivita (I := I) g).toFun (fun b : M => gradFun (I := I) g f b) x v)
            ((chartModelBasis E) i) • w
        + g.inner x ((LeviCivita (I := I) g).toFun (fun b : M => gradFun (I := I) g f b) x v)
            w • basisVec (I := I) x i
        - g.inner x w ((chartModelBasis E) i)
            • (LeviCivita (I := I) g).toFun (fun b : M => gradFun (I := I) g f b) x v := by
    intro i
    rw [covDerivConnDiff_conformalMetric_apply (I := I) f hf g hV_sm
      (smoothExtensionTangent_contMDiff (I := I) x ((chartModelBasis E) i)) hW_sm x]
    simp only [smoothExtensionTangent_eq]
    rfl
  have hm : diffSec (LeviCivita (I := I) g) (LeviCivita (I := I) (conformalMetric f hf g))
      (smoothExtensionTangent (I := I) x v) (smoothExtensionTangent (I := I) x w) x
      = g.inner x (gradFun (I := I) g f x) v • w
        + g.inner x (gradFun (I := I) g f x) w • v
        - g.inner x w v • gradFun (I := I) g f x := by
    change connDiff (I := I) (conformalMetric f hf g) g x
        (smoothExtensionTangent (I := I) x w x) (smoothExtensionTangent (I := I) x v x) = _
    rw [smoothExtensionTangent_eq, smoothExtensionTangent_eq]
    exact connDiff_conformalMetric_apply (I := I) f hf g x w v
  have hmB : ∀ i : Fin (Module.finrank Real E),
      diffSec (LeviCivita (I := I) g) (LeviCivita (I := I) (conformalMetric f hf g))
        (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
        (smoothExtensionTangent (I := I) x w) x
      = g.inner x (gradFun (I := I) g f x) ((chartModelBasis E) i) • w
        + g.inner x (gradFun (I := I) g f x) w • basisVec (I := I) x i
        - g.inner x w ((chartModelBasis E) i) • gradFun (I := I) g f x := by
    intro i
    change connDiff (I := I) (conformalMetric f hf g) g x
        (smoothExtensionTangent (I := I) x w x)
        (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x) = _
    rw [smoothExtensionTangent_eq, smoothExtensionTangent_eq]
    exact connDiff_conformalMetric_apply (I := I) f hf g x w ((chartModelBasis E) i)
  have he3 : ∀ i : Fin (Module.finrank Real E),
      connDiff (I := I) (conformalMetric f hf g) g x
        (diffSec (LeviCivita (I := I) g) (LeviCivita (I := I) (conformalMetric f hf g))
          (smoothExtensionTangent (I := I) x v)
          (smoothExtensionTangent (I := I) x w) x)
        (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
      = g.inner x (gradFun (I := I) g f x) ((chartModelBasis E) i) •
          (g.inner x (gradFun (I := I) g f x) v • w
            + g.inner x (gradFun (I := I) g f x) w • v
            - g.inner x w v • gradFun (I := I) g f x)
        + g.inner x (gradFun (I := I) g f x)
            (g.inner x (gradFun (I := I) g f x) v • w
              + g.inner x (gradFun (I := I) g f x) w • v
              - g.inner x w v • gradFun (I := I) g f x) • basisVec (I := I) x i
        - g.inner x
            (g.inner x (gradFun (I := I) g f x) v • w
              + g.inner x (gradFun (I := I) g f x) w • v
              - g.inner x w v • gradFun (I := I) g f x) ((chartModelBasis E) i)
            • gradFun (I := I) g f x := by
    intro i
    rw [hm, smoothExtensionTangent_eq]
    exact connDiff_conformalMetric_apply (I := I) f hf g x _ ((chartModelBasis E) i)
  have he4 : ∀ i : Fin (Module.finrank Real E),
      connDiff (I := I) (conformalMetric f hf g) g x
        (diffSec (LeviCivita (I := I) g) (LeviCivita (I := I) (conformalMetric f hf g))
          (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
          (smoothExtensionTangent (I := I) x w) x)
        (smoothExtensionTangent (I := I) x v x)
      = g.inner x (gradFun (I := I) g f x) v •
          (g.inner x (gradFun (I := I) g f x) ((chartModelBasis E) i) • w
            + g.inner x (gradFun (I := I) g f x) w • basisVec (I := I) x i
            - g.inner x w ((chartModelBasis E) i) • gradFun (I := I) g f x)
        + g.inner x (gradFun (I := I) g f x)
            (g.inner x (gradFun (I := I) g f x) ((chartModelBasis E) i) • w
              + g.inner x (gradFun (I := I) g f x) w • basisVec (I := I) x i
              - g.inner x w ((chartModelBasis E) i) • gradFun (I := I) g f x) • v
        - g.inner x
            (g.inner x (gradFun (I := I) g f x) ((chartModelBasis E) i) • w
              + g.inner x (gradFun (I := I) g f x) w • basisVec (I := I) x i
              - g.inner x w ((chartModelBasis E) i) • gradFun (I := I) g f x) v
            • gradFun (I := I) g f x := by
    intro i
    rw [hmB i, smoothExtensionTangent_eq]
    exact connDiff_conformalMetric_apply (I := I) f hf g x _ v
  have hsum2 : (∑ i : Fin (Module.finrank Real E),
      (chartModelBasis E).repr
        ((covDerivConnDiff (I := I) g (conformalMetric f hf g)
              (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
              (smoothExtensionTangent (I := I) x v)
              (smoothExtensionTangent (I := I) x w) x
            - covDerivConnDiff (I := I) g (conformalMetric f hf g)
              (smoothExtensionTangent (I := I) x v)
              (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
              (smoothExtensionTangent (I := I) x w) x)
          + (connDiff (I := I) (conformalMetric f hf g) g x
                (diffSec (LeviCivita (I := I) g) (LeviCivita (I := I) (conformalMetric f hf g))
                  (smoothExtensionTangent (I := I) x v)
                  (smoothExtensionTangent (I := I) x w) x)
                (smoothExtensionTangent (I := I) x ((chartModelBasis E) i) x)
              - connDiff (I := I) (conformalMetric f hf g) g x
                (diffSec (LeviCivita (I := I) g) (LeviCivita (I := I) (conformalMetric f hf g))
                  (smoothExtensionTangent (I := I) x ((chartModelBasis E) i))
                  (smoothExtensionTangent (I := I) x w) x)
                (smoothExtensionTangent (I := I) x v x))) i)
      = ∑ i : Fin (Module.finrank Real E),
          (chartModelBasis E).repr
            ((g.inner x ((LeviCivita (I := I) g).toFun (fun b : M => gradFun (I := I) g f b) x
                  ((chartModelBasis E) i)) v • w
                + g.inner x ((LeviCivita (I := I) g).toFun (fun b : M => gradFun (I := I) g f b) x
                  ((chartModelBasis E) i)) w • v
                - g.inner x w v • (LeviCivita (I := I) g).toFun
                  (fun b : M => gradFun (I := I) g f b) x ((chartModelBasis E) i)
              - (g.inner x ((LeviCivita (I := I) g).toFun (fun b : M => gradFun (I := I) g f b) x v)
                    ((chartModelBasis E) i) • w
                  + g.inner x ((LeviCivita (I := I) g).toFun (fun b : M => gradFun (I := I) g f b) x v)
                    w • basisVec (I := I) x i
                  - g.inner x w ((chartModelBasis E) i)
                    • (LeviCivita (I := I) g).toFun (fun b : M => gradFun (I := I) g f b) x v))
             + ((g.inner x (gradFun (I := I) g f x) ((chartModelBasis E) i) •
                    (g.inner x (gradFun (I := I) g f x) v • w
                      + g.inner x (gradFun (I := I) g f x) w • v
                      - g.inner x w v • gradFun (I := I) g f x)
                  + g.inner x (gradFun (I := I) g f x)
                      (g.inner x (gradFun (I := I) g f x) v • w
                        + g.inner x (gradFun (I := I) g f x) w • v
                        - g.inner x w v • gradFun (I := I) g f x) • basisVec (I := I) x i
                  - g.inner x
                      (g.inner x (gradFun (I := I) g f x) v • w
                        + g.inner x (gradFun (I := I) g f x) w • v
                        - g.inner x w v • gradFun (I := I) g f x) ((chartModelBasis E) i)
                      • gradFun (I := I) g f x)
                - (g.inner x (gradFun (I := I) g f x) v •
                      (g.inner x (gradFun (I := I) g f x) ((chartModelBasis E) i) • w
                        + g.inner x (gradFun (I := I) g f x) w • basisVec (I := I) x i
                        - g.inner x w ((chartModelBasis E) i) • gradFun (I := I) g f x)
                    + g.inner x (gradFun (I := I) g f x)
                        (g.inner x (gradFun (I := I) g f x) ((chartModelBasis E) i) • w
                          + g.inner x (gradFun (I := I) g f x) w • basisVec (I := I) x i
                          - g.inner x w ((chartModelBasis E) i) • gradFun (I := I) g f x) • v
                    - g.inner x
                        (g.inner x (gradFun (I := I) g f x) ((chartModelBasis E) i) • w
                          + g.inner x (gradFun (I := I) g f x) w • basisVec (I := I) x i
                          - g.inner x w ((chartModelBasis E) i) • gradFun (I := I) g f x) v
                        • gradFun (I := I) g f x))) i :=
    Finset.sum_congr rfl (fun i _ => by rw [he1 i, he2 i, he3 i, he4 i])
  have hn : (Module.finrank Real E : Real) = 2 := by
    rw [hdim]; norm_num
  have hf₂ : ContMDiffAt I 𝓘(Real) 2 f x := by
    refine (hf.contMDiffAt).of_le ?_
    have h1 : ((2 : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := by
      exact_mod_cast (le_top : (2 : ℕ∞) ≤ ⊤)
    simpa using h1
  have hQsym : g.inner x
      ((LeviCivita (I := I) g).toFun (fun b : M => gradFun (I := I) g f b) x w) v
      = g.inner x
          ((LeviCivita (I := I) g).toFun (fun b : M => gradFun (I := I) g f b) x v) w := by
    rw [abstractHessian_eq_inner_cov_gradFun_extend (I := I) g hf x w v,
      abstractHessian_symm (I := I) g hf₂ w v,
      ← abstractHessian_eq_inner_cov_gradFun_extend (I := I) g hf x v w]
  have hmega := conformal_palatini_sum_collapse (E := E) (g.inner x)
    (fun a b => g.symm x a b)
    ((LeviCivita (I := I) g).toFun (fun b : M => gradFun (I := I) g f b) x)
    (gradFun (I := I) g f x) v w (Δ_g (I := I) g hf x)
    (sum_repr_covGrad_eq_laplacian (I := I) f hf g x) hn hQsym
  have hfix : -(g.inner x w v * Δ_g (I := I) g hf x)
      = formLaplacianScalar (I := I) g hf x * g.inner x v w := by
    have hL := formLaplacianScalar_eq_neg_Δ_g (I := I) g hf x
    have hΔ : Δ_g (I := I) g hf x = -formLaplacianScalar (I := I) g hf x := by
      linarith
    rw [g.symm x w v, hΔ]
    ring
  have hdiff := ((hpal.trans hsum2).trans hmega).trans hfix
  linarith [hdiff]

theorem ricci_conformalMetric_twoDim
    (hdim : Module.finrank Real E = 2)
    (f : M -> Real) (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (g : SmoothRiemannianMetric I M) (x : M) (v w : TangentSpace I x) :
    metricRicciAt (I := I) (conformalMetric f hf g) x (vec2 (I := I) v w)
      = metricRicciAt (I := I) g x (vec2 (I := I) v w)
        + formLaplacianScalar (I := I) g hf x * g.inner x v w := by
  rw [metricRicciAt_apply_eq_ricciTensor (I := I) (conformalMetric f hf g) x v w,
      metricRicciAt_apply_eq_ricciTensor (I := I) g x v w]
  exact ricciTensor_conformalMetric_twoDim (I := I) hdim f hf g x v w


theorem gaussCurvature_conformalMetric
    (hdim : Module.finrank Real E = 2)
    (f : M -> Real) (hf : ContMDiff I 𝓘(Real, Real) ∞ f)
    (g : SmoothRiemannianMetric I M) (x : M) :
    gaussCurvature (I := I) (conformalMetric f hf g) x
      = Real.exp (-(2 * f x)) * (gaussCurvature (I := I) g x + formLaplacianScalar (I := I) g hf x) := by
  haveI hntE : Nontrivial E := Module.nontrivial_of_finrank_pos (by rw [hdim]; norm_num)
  haveI : Nontrivial (TangentSpace I x) := hntE
  obtain ⟨v₀, hv₀⟩ := exists_ne (0 : TangentSpace I x)
  have hpos : 0 < g.inner x v₀ v₀ := g.pos x v₀ hv₀
  have hne : g.inner x v₀ v₀ ≠ 0 := ne_of_gt hpos
  have hE2 : Real.exp (2 * f x) ≠ 0 := Real.exp_ne_zero _
  have hEg : metricRicciAt (I := I) g x (vec2 (I := I) v₀ v₀)
      = gaussCurvature (I := I) g x * g.inner x v₀ v₀ :=
    ricci_eq_gaussCurvature_smul_metric_twoDim (I := I) hdim g x v₀ v₀
  have hEĝ : metricRicciAt (I := I) (conformalMetric f hf g) x (vec2 (I := I) v₀ v₀)
      = gaussCurvature (I := I) (conformalMetric f hf g) x
          * (conformalMetric f hf g).inner x v₀ v₀ :=
    ricci_eq_gaussCurvature_smul_metric_twoDim (I := I) hdim (conformalMetric f hf g) x v₀ v₀
  rw [conformalMetric_inner] at hEĝ
  have hRic := ricci_conformalMetric_twoDim (I := I) hdim f hf g x v₀ v₀
  have hchain : gaussCurvature (I := I) (conformalMetric f hf g) x
        * (Real.exp (2 * f x) * g.inner x v₀ v₀)
      = (gaussCurvature (I := I) g x + formLaplacianScalar (I := I) g hf x)
          * g.inner x v₀ v₀ := by
    rw [← hEĝ, hRic, hEg]; ring
  have hkey : gaussCurvature (I := I) (conformalMetric f hf g) x * Real.exp (2 * f x)
      = gaussCurvature (I := I) g x + formLaplacianScalar (I := I) g hf x := by
    have h := hchain
    rw [← mul_assoc] at h
    exact mul_right_cancel₀ hne h
  rw [Real.exp_neg, ← hkey,
      mul_comm (gaussCurvature (I := I) (conformalMetric f hf g) x) (Real.exp (2 * f x)),
      ← mul_assoc, inv_mul_cancel₀ hE2, one_mul]


end DifferentialGeometry.Integral.Connection
