import DifferentialGeometry.Analysis.Integration.DivergenceTheorem.Global.CompactSupport
import DifferentialGeometry.Geometry.Metric.RicciSoliton.SurfaceIdentities
import DifferentialGeometry.Geometry.Operator.Laplacian.LeviCivitaIdentification

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set MeasureTheory
open scoped Manifold ContDiff

namespace DifferentialGeometry.Geometry

open Curvature Operator
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Integral.Measure

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [FiniteDimensional Real E]
variable {H : Type*} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [SigmaCompactSpace M] [T2Space M]
  [ConnectedSpace M]

omit [ConnectedSpace M] in
theorem normalizedGradientRicciSoliton_regularized_gradient_divergence
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2) (ε : Real) (hε : 0 < ε) (x : M) :
    divergenceG (I := I) g
        (smoothSmul (I := I)
          (fun y : M =>
            (normGradSqFun (I := I) g f y + ε)⁻¹)
          (by
            have hU : ContMDiff I 𝓘(Real, Real) ∞
                (normGradSqFun (I := I) g (f : M → Real)) :=
              normGradSqFun_contMDiff (I := I) g f.contMDiff
            have hden : ContMDiff I 𝓘(Real, Real) ∞
                (fun y : M => normGradSqFun (I := I) g f y + ε) :=
              hU.add contMDiff_const
            apply hden.inv₀
            intro y
            have hnonneg := normGradSqFun_nonneg (I := I) g (f : M → Real) y
            have hpos : 0 < normGradSqFun (I := I) g (f : M → Real) y + ε :=
              add_pos_of_nonneg_of_pos hnonneg hε
            exact ne_of_gt hpos)
          (gradG (I := I) g f)) x =
      ε * (1 - metricScalarAt (I := I) (M := M) g x) *
        (normGradSqFun (I := I) g f x + ε)⁻¹ ^ 2 := by
  let U : M → Real := normGradSqFun (I := I) g (f : M → Real)
  let d : M → Real := fun y => U y + ε
  have hU_smooth : ContMDiff I 𝓘(Real, Real) ∞ U := by
    exact normGradSqFun_contMDiff (I := I) g f.contMDiff
  have hd_smooth : ContMDiff I 𝓘(Real, Real) ∞ d := by
    exact hU_smooth.add contMDiff_const
  have hd_ne : ∀ y : M, d y ≠ 0 := by
    intro y
    have hnonneg := normGradSqFun_nonneg (I := I) g (f : M → Real) y
    have hpos : 0 < normGradSqFun (I := I) g (f : M → Real) y + ε :=
      add_pos_of_nonneg_of_pos hnonneg hε
    exact ne_of_gt (by simpa [d, U] using hpos)
  have hphi_smooth : ContMDiff I 𝓘(Real, Real) ∞ (fun y : M => (d y)⁻¹) := by
    exact hd_smooth.inv₀ hd_ne
  have hU_eq : ∀ y : M,
      U y = f y - metricScalarAt (I := I) (M := M) g y := by
    intro y
    have hpotential := normalizedGradientRicciSoliton_potential_equation (I := I) h y
    change normGradSqFun (I := I) g (f : M → Real) y =
      f y - metricScalarAt (I := I) (M := M) g y
    rw [normGradSqFun_def]
    linarith
  have hU_grad : ∀ y : M,
      gradientFun (I := I) g U y =
        (1 - metricScalarAt (I := I) (M := M) g y) •
          gradientFun (I := I) g f y := by
    intro y
    have hU_fun : U = fun z : M => f z - metricScalarAt (I := I) (M := M) g z :=
      funext hU_eq
    rw [hU_fun, gradientFun_sub (I := I) g
      ((f.contMDiff y).mdifferentiableAt (by simp))
      ((metricScalar_smooth (I := I) (M := M) g y).mdifferentiableAt (by simp))]
    have hscalar := normalizedGradientRicciSoliton_gradient_scalar_of_finrank_eq_two
      (I := I) h hdim y
    have hscalar' : gradientFun (I := I) g
        (fun z : M => metricScalarAt (I := I) (M := M) g z) y =
        metricScalarAt (I := I) (M := M) g y • gradientFun (I := I) g f y := by
      calc
        gradientFun (I := I) g
              (fun z : M => metricScalarAt (I := I) (M := M) g z) y =
            gradFun (I := I) g
              (fun z : M => metricScalarAt (I := I) (M := M) g z) y :=
          Connection.gradient_eq_gradFun (I := I) g
            (fun z : M => metricScalarAt (I := I) (M := M) g z) y
        _ = metricScalarAt (I := I) (M := M) g y •
            gradFun (I := I) g f y := hscalar
        _ = metricScalarAt (I := I) (M := M) g y •
            gradientFun (I := I) g f y := by
          rw [Connection.gradient_eq_gradFun]
    rw [hscalar']
    calc
      gradientFun (I := I) g f y -
          metricScalarAt (I := I) (M := M) g y • gradientFun (I := I) g f y =
        (1 : Real) • gradientFun (I := I) g f y -
          metricScalarAt (I := I) (M := M) g y • gradientFun (I := I) g f y := by
            rw [one_smul]
      _ = (1 - metricScalarAt (I := I) (M := M) g y) •
          gradientFun (I := I) g f y := by
            rw [sub_smul]
  have hd_grad : ∀ y : M,
      gradientFun (I := I) g d y =
        (1 - metricScalarAt (I := I) (M := M) g y) •
          gradientFun (I := I) g f y := by
    intro y
    dsimp [d]
    have hUy : MDifferentiableAt I 𝓘(Real, Real) U y :=
      (hU_smooth y).mdifferentiableAt (by simp)
    rw [gradientFun_add (I := I) g
      hUy
      (mdifferentiableAt_const (c := ε)), gradientFun_const, add_zero]
    exact hU_grad y
  have hphi_grad : ∀ y : M,
      gradientFun (I := I) g (fun z : M => (d z)⁻¹) y =
        -(d y ^ 2)⁻¹ •
          ((1 - metricScalarAt (I := I) (M := M) g y) •
            gradientFun (I := I) g f y) := by
    intro y
    have hdy : MDifferentiableAt I 𝓘(Real, Real) d y :=
      (hd_smooth y).mdifferentiableAt (by simp)
    have hcomp := gradientFun_comp (I := I) g
      (hasDerivAt_inv (hd_ne y)).differentiableAt hdy
    rw [hcomp, deriv_inv, hd_grad]
  have hinner : ∀ y : M,
      g.inner y (gradientFun (I := I) g f y)
          (gradientFun (I := I) g f y) = U y := by
    intro y
    change g.inner y (gradFun (I := I) g (f : M → Real) y)
        (gradFun (I := I) g (f : M → Real) y) =
      normGradSqFun (I := I) g (f : M → Real) y
    rfl
  have hdiv := divergence_g_smoothSmul (I := I) g
    (fun y : M => (d y)⁻¹) hphi_smooth (gradG (I := I) g f) x
  rw [hdiv]
  rw [← Δ_g_def (I := I) g f x]
  rw [normalizedGradientRicciSoliton_laplacian_potential_of_finrank_eq_two
    (I := I) h hdim x]
  rw [tangentSectionAction_grad_g_eq_inner (I := I) g hphi_smooth
    (gradG (I := I) g f) x]
  have hgradphi_section :
      (gradG (I := I) g
          ⟨(fun y : M => (d y)⁻¹), hphi_smooth⟩) x =
        gradientFun (I := I) g (fun y : M => (d y)⁻¹) x :=
    grad_g_apply (I := I) g
      ⟨(fun y : M => (d y)⁻¹), hphi_smooth⟩ x
  have hgradf_section :
      (gradG (I := I) g f) x = gradientFun (I := I) g f x :=
    grad_g_apply (I := I) g f x
  rw [hgradf_section, hgradphi_section, hphi_grad]
  have hinner_nested :
      ((g.inner x) (gradientFun (I := I) g f x))
          ((-(d x ^ 2)⁻¹) •
            ((1 - metricScalarAt (I := I) (M := M) g x) •
              gradientFun (I := I) g f x)) =
        -(d x ^ 2)⁻¹ * (1 - metricScalarAt (I := I) (M := M) g x) * U x := by
    rw [map_smul, map_smul, smul_eq_mul, smul_eq_mul, hinner]
    ring
  change (d x)⁻¹ * (1 - metricScalarAt (I := I) (M := M) g x) +
      ((g.inner x) (gradientFun (I := I) g f x))
        ((-(d x ^ 2)⁻¹) •
          ((1 - metricScalarAt (I := I) (M := M) g x) •
            gradientFun (I := I) g f x)) = _
  rw [hinner_nested]
  dsimp [d, U]
  field_simp [hd_ne x]
  ring

omit [ConnectedSpace M] in
theorem normalizedGradientRicciSoliton_regularized_gradient_integral_eq_zero
    [CompactSpace M]
    {g : SmoothRiemannianMetric I M} {f : C^∞⟮I, M; Real⟯}
    (h : normalizedGradientRicciSoliton (I := I) g f)
    (hdim : Module.finrank Real E = 2) (ε : Real) (hε : 0 < ε) :
    ∫ y, ε * (1 - metricScalarAt (I := I) (M := M) g y) *
        (normGradSqFun (I := I) g f y + ε)⁻¹ ^ 2
      ∂(riemannianVolumeMeasure (I := I) (M := M) g) = 0 := by
  let U : M → Real := normGradSqFun (I := I) g (f : M → Real)
  let d : M → Real := fun y => U y + ε
  have hU_smooth : ContMDiff I 𝓘(Real, Real) ∞ U := by
    exact normGradSqFun_contMDiff (I := I) g f.contMDiff
  have hd_smooth : ContMDiff I 𝓘(Real, Real) ∞ d := by
    exact hU_smooth.add contMDiff_const
  have hd_ne : ∀ y : M, d y ≠ 0 := by
    intro y
    have hnonneg := normGradSqFun_nonneg (I := I) g (f : M → Real) y
    have hpos : 0 < normGradSqFun (I := I) g (f : M → Real) y + ε :=
      add_pos_of_nonneg_of_pos hnonneg hε
    exact ne_of_gt (by simpa [d, U] using hpos)
  have hphi_smooth : ContMDiff I 𝓘(Real, Real) ∞ (fun y : M => (d y)⁻¹) := by
    exact hd_smooth.inv₀ hd_ne
  let X := smoothSmul (I := I) (fun y : M => (d y)⁻¹)
    hphi_smooth (gradG (I := I) g f)
  have hzero := integral_divergence_eq_zero_of_compact (I := I) g X
  have hpoint : ∀ y : M,
      divergenceG (I := I) g X y =
        ε * (1 - metricScalarAt (I := I) (M := M) g y) *
          (normGradSqFun (I := I) g f y + ε)⁻¹ ^ 2 := by
    intro y
    dsimp [X, d, U]
    exact normalizedGradientRicciSoliton_regularized_gradient_divergence
      (I := I) h hdim ε hε y
  calc
    ∫ y, ε * (1 - metricScalarAt (I := I) (M := M) g y) *
          (normGradSqFun (I := I) g f y + ε)⁻¹ ^ 2
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) =
      ∫ y, divergenceG (I := I) g X y
        ∂(riemannianVolumeMeasure (I := I) (M := M) g) :=
      integral_congr_ae (Filter.Eventually.of_forall fun y => (hpoint y).symm)
    _ = 0 := hzero

end DifferentialGeometry.Geometry
