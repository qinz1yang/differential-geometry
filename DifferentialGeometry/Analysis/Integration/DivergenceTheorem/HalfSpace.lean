import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Support
import Mathlib.Analysis.Calculus.LineDeriv.IntegrationByParts
import Mathlib.LinearAlgebra.Trace

set_option autoImplicit false

open MeasureTheory Set Filter
open scoped Topology

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
  [MeasurableSpace E] [BorelSpace E]
variable {F : Type*} [NormedAddCommGroup F] [NormedSpace Real F] [CompleteSpace F]
variable {mu : Measure E} [SFinite mu] [IsFiniteMeasureOnCompacts mu]

theorem integral_fderiv_normal_half_space_of_hasCompactSupport
    {u : E × Real → F} (hu : ContDiff Real 1 u) (hcs : HasCompactSupport u) (a : Real) :
    ∫ p, fderiv Real u p (0, 1) ∂(mu.prod (volume.restrict (Ioi a))) =
      -∫ x, u (x, a) ∂mu := by
  have hcont : Continuous (fun p => fderiv Real u p (0, 1)) :=
    (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hpartial_cs : HasCompactSupport (fun p => fderiv Real u p (0, 1)) :=
    HasCompactSupport.fderiv_apply Real hcs (0, 1)
  have hint : Integrable (fun p => fderiv Real u p (0, 1))
      (mu.prod (volume.restrict (Ioi a))) :=
    hcont.integrable_of_hasCompactSupport hpartial_cs
  rw [integral_prod _ hint, ← integral_neg]
  apply integral_congr_ae
  filter_upwards with x
  have hslice : ContDiff Real 1 (fun t : Real => u (x, t)) :=
    hu.comp (contDiff_const.prodMk contDiff_id)
  have hiso : Isometry (fun t : Real => (x, t)) := by
    apply Isometry.of_dist_eq
    intro s t
    simp
  have hslice_cs : HasCompactSupport (fun t : Real => u (x, t)) :=
    hcs.comp_isClosedEmbedding hiso.isClosedEmbedding
  have hd (t : Real) : deriv (fun s : Real => u (x, s)) t =
      fderiv Real u (x, t) (0, 1) := by
    exact ((hu.differentiable one_ne_zero (x, t)).hasFDerivAt.comp_hasDerivAt t
      ((hasDerivAt_const t x).prodMk (hasDerivAt_id t))).deriv
  simpa only [hd] using hslice_cs.integral_Ioi_deriv_eq hslice a

theorem integral_smul_fderiv_normal_add_fderiv_smul_half_space_of_hasCompactSupport
    {phi : E × Real → Real} {u : E × Real → F}
    (hphi : ContDiff Real 1 phi) (hu : ContDiff Real 1 u)
    (hcs : HasCompactSupport (fun p => phi p • u p)) (a : Real) :
    ∫ p, phi p • fderiv Real u p (0, 1) + fderiv Real phi p (0, 1) • u p
        ∂(mu.prod (volume.restrict (Ioi a))) =
      -∫ x, phi (x, a) • u (x, a) ∂mu := by
  have h := integral_fderiv_normal_half_space_of_hasCompactSupport
    (mu := mu) (hphi.smul hu) hcs a
  convert h using 1
  · apply integral_congr_ae
    filter_upwards with p
    rw [fderiv_smul (hphi.differentiable one_ne_zero p)
      (hu.differentiable one_ne_zero p)]
    rfl
  · rfl

omit [SFinite mu] [IsFiniteMeasureOnCompacts mu] [CompleteSpace F] in
theorem integral_fderiv_tangent_half_space_eq_zero_of_hasCompactSupport
    [FiniteDimensional Real E] [mu.IsAddHaarMeasure]
    {u : E × Real → F} (hu : ContDiff Real 1 u) (hcs : HasCompactSupport u)
    (a : Real) (v : E) :
    ∫ p, fderiv Real u p (v, 0) ∂(mu.prod (volume.restrict (Ioi a))) = 0 := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  have hcont : Continuous (fun p => fderiv Real u p (v, 0)) :=
    (hu.continuous_fderiv one_ne_zero).clm_apply continuous_const
  have hpartial_cs : HasCompactSupport (fun p => fderiv Real u p (v, 0)) :=
    HasCompactSupport.fderiv_apply Real hcs (v, 0)
  have hint : Integrable (fun p => fderiv Real u p (v, 0))
      (mu.prod (volume.restrict (Ioi a))) :=
    hcont.integrable_of_hasCompactSupport hpartial_cs
  rw [integral_prod_symm _ hint]
  have hslice (t : Real) : ∫ x, fderiv Real u (x, t) (v, 0) ∂mu = 0 := by
    have hut : ContDiff Real 1 (fun x : E => u (x, t)) :=
      hu.comp (contDiff_id.prodMk contDiff_const)
    have hiso : Isometry (fun x : E => (x, t)) := by
      apply Isometry.of_dist_eq
      intro x y
      simp
    have hcut : HasCompactSupport (fun x : E => u (x, t)) :=
      hcs.comp_isClosedEmbedding hiso.isClosedEmbedding
    have hu_int : Integrable (fun x : E => u (x, t)) mu :=
      hut.continuous.integrable_of_hasCompactSupport hcut
    have hdu_int : Integrable (fun x : E => fderiv Real (fun y => u (y, t)) x v) mu :=
      ((hut.continuous_fderiv one_ne_zero).clm_apply continuous_const)
        |>.integrable_of_hasCompactSupport (HasCompactSupport.fderiv_apply Real hcut v)
    have hd (x : E) : fderiv Real (fun y => u (y, t)) x v =
        fderiv Real u (x, t) (v, 0) := by
      exact congrArg (fun L : E →L[Real] F => L v)
        ((hu.differentiable one_ne_zero (x, t)).hasFDerivAt.comp x
          ((hasFDerivAt_id x).prodMk (hasFDerivAt_const t x))).fderiv
    have hibp := integral_smul_fderiv_eq_neg_fderiv_smul_of_integrable
      (μ := mu) (f := fun _ : E => (1 : Real)) (g := fun x : E => u (x, t)) (v := v)
      (by simp) (by simpa only [one_smul] using hdu_int)
      (by simpa only [one_smul] using hu_int)
      (by intro x _; exact differentiableAt_const (1 : Real))
      (fun x _ => hut.differentiable one_ne_zero x)
    simpa [hd] using hibp
  simp only [hslice, integral_zero]

omit [SFinite mu] [IsFiniteMeasureOnCompacts mu] in
theorem integral_trace_fderiv_half_space_of_hasCompactSupport
    [FiniteDimensional Real E] [mu.IsAddHaarMeasure]
    {u : E × Real → E × Real} (hu : ContDiff Real 1 u) (hcs : HasCompactSupport u)
    (a : Real) :
    ∫ p, LinearMap.trace Real (E × Real) (fderiv Real u p).toLinearMap
        ∂(mu.prod (volume.restrict (Ioi a))) =
      -∫ x, (u (x, a)).2 ∂mu := by
  let _ : CompleteSpace E := FiniteDimensional.complete Real E
  let nu := mu.prod (volume.restrict (Ioi a))
  have hDint : Integrable (fderiv Real u) nu :=
    (hu.continuous_fderiv one_ne_zero).integrable_of_hasCompactSupport
      (HasCompactSupport.fderiv Real hcs)
  let A := ∫ p, fderiv Real u p ∂nu
  have htangent (v : E) : A (v, 0) = 0 := by
    rw [ContinuousLinearMap.integral_apply hDint]
    exact integral_fderiv_tangent_half_space_eq_zero_of_hasCompactSupport hu hcs a v
  have hnormal : A (0, 1) = -∫ x, u (x, a) ∂mu := by
    rw [ContinuousLinearMap.integral_apply hDint]
    exact integral_fderiv_normal_half_space_of_hasCompactSupport hu hcs a
  have hD : (∫ p, fderiv Real u p ∂nu) =
      (ContinuousLinearMap.snd Real E Real).smulRight (-∫ x, u (x, a) ∂mu) := by
    apply ContinuousLinearMap.ext
    intro v
    change A v = _
    conv_lhs => rw [show v = (v.1, 0) + v.2 • (0, 1) by ext <;> simp]
    rw [map_add, map_smul, htangent, hnormal, zero_add]
    rfl
  let trLinear : ((E × Real) →L[Real] (E × Real)) →ₗ[Real] Real :=
    { toFun := fun L => LinearMap.trace Real (E × Real) L.toLinearMap
      map_add' := by intro L K; exact map_add (LinearMap.trace Real (E × Real)) _ _
      map_smul' := by intro c L; exact map_smul (LinearMap.trace Real (E × Real)) c _ }
  let tr := trLinear.toContinuousLinearMap
  have htrace := tr.integral_comp_comm hDint
  change (∫ p, LinearMap.trace Real (E × Real) (fderiv Real u p).toLinearMap ∂nu) =
    LinearMap.trace Real (E × Real) (∫ p, fderiv Real u p ∂nu).toLinearMap at htrace
  rw [htrace, hD]
  change LinearMap.trace Real (E × Real)
    ((LinearMap.snd Real E Real).smulRight (-∫ x, u (x, a) ∂mu)) = _
  rw [LinearMap.trace_smulRight]
  have hiso : Isometry (fun x : E => (x, a)) := by
    apply Isometry.of_dist_eq
    intro x y
    simp
  have hboundary : Integrable (fun x : E => u (x, a)) mu :=
    (hu.continuous.comp (continuous_id.prodMk continuous_const))
      |>.integrable_of_hasCompactSupport (hcs.comp_isClosedEmbedding hiso.isClosedEmbedding)
  change -(∫ x, u (x, a) ∂mu).2 = _
  rw [snd_integral hboundary]

omit [SFinite mu] [IsFiniteMeasureOnCompacts mu] in
theorem integral_mul_trace_fderiv_add_fderiv_half_space_of_hasCompactSupport
    [FiniteDimensional Real E] [mu.IsAddHaarMeasure]
    {phi : E × Real → Real} {u : E × Real → E × Real}
    (hphi : ContDiff Real 1 phi) (hu : ContDiff Real 1 u)
    (hcs : HasCompactSupport (fun p => phi p • u p)) (a : Real) :
    ∫ p, phi p * LinearMap.trace Real (E × Real) (fderiv Real u p).toLinearMap +
        fderiv Real phi p (u p) ∂(mu.prod (volume.restrict (Ioi a))) =
      -∫ x, phi (x, a) * (u (x, a)).2 ∂mu := by
  have h := integral_trace_fderiv_half_space_of_hasCompactSupport
    (mu := mu) (hphi.smul hu) hcs a
  convert h using 1
  · apply integral_congr_ae
    filter_upwards with p
    rw [fderiv_smul (hphi.differentiable one_ne_zero p)
      (hu.differentiable one_ne_zero p)]
    change _ = LinearMap.trace Real (E × Real)
      (phi p • (fderiv Real u p).toLinearMap + (fderiv Real phi p).toLinearMap.smulRight (u p))
    rw [map_add, map_smul, LinearMap.trace_smulRight]
    rfl
  · rfl

end DifferentialGeometry.Analysis
