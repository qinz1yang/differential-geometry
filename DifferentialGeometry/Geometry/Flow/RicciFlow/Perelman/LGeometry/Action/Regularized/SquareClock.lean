import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Action.Regularized.Defs
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.CarrierBaseTime
import Mathlib.Analysis.SpecialFunctions.Sqrt

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Set MeasureTheory
open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
private theorem lVelocity_comp_of_hasDerivAt
    (alpha : ℝ → M) {f : ℝ → ℝ} {c s : ℝ}
    (halpha : MDifferentiableAt 𝓘(ℝ, ℝ) I alpha (f s))
    (hf : HasDerivAt f c s) :
    lVelocity (I := I) (alpha ∘ f) s =
      c • lVelocity (I := I) alpha (f s) := by
  have hfm : MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) f s :=
    mdifferentiableAt_iff_differentiableAt.mpr hf.differentiableAt
  have hchain := mfderiv_comp (I := 𝓘(ℝ, ℝ)) (I' := 𝓘(ℝ, ℝ)) (I'' := I)
    (f := f) (g := alpha) s halpha hfm
  have hfval : (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) f s) (1 : ℝ) = c := by
    rw [mfderiv_eq_fderiv]
    exact hf.deriv
  have hchain1 := congrArg (fun L => L (1 : ℝ)) hchain
  have hcompval :
      ((mfderiv 𝓘(ℝ, ℝ) I alpha (f s)).comp
        (mfderiv 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) f s)) (1 : ℝ) =
        (mfderiv 𝓘(ℝ, ℝ) I alpha (f s)) c := by
    with_unfolding_all
      exact congrArg (mfderiv 𝓘(ℝ, ℝ) I alpha (f s)) hfval
  have hlin : (mfderiv 𝓘(ℝ, ℝ) I alpha (f s)) c =
      c • lVelocity (I := I) alpha (f s) := by
    have h := (tangentLinearMapToModel (mfderiv 𝓘(ℝ, ℝ) I alpha (f s))).map_smul c (1 : ℝ)
    apply (tangentSpaceModelContinuousLinearEquiv (I := I) (alpha (f s))).injective
    simpa only [smul_eq_mul, mul_one, lVelocity, tangentLinearMapToModel_apply,
      tangentSpaceModelContinuousLinearEquiv_apply,
      tangentSpaceModelContinuousLinearEquiv_symm_apply, map_smul] using h
  with_unfolding_all exact (hchain1.trans hcompval).trans hlin

variable [FiniteDimensional ℝ E] [IsManifold I ∞ M]
  {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
theorem lRegularizedLagrangian_sqrt_sub_sq_mul
    (S : SolutionOn (I := I) (M := M) D) {d r : ℝ} (hd : 0 ≤ d) (hr : 0 < r)
    (alpha : ℝ → M) (halpha : MDifferentiableAt 𝓘(ℝ, ℝ) I alpha r) :
    lRegularizedLagrangian S 0 (fun s => alpha (Real.sqrt (s ^ 2 - d)))
        (Real.sqrt (r ^ 2 + d)) * (r / Real.sqrt (r ^ 2 + d)) =
      (Real.sqrt (r ^ 2 + d) / r) * lRegularizedLagrangian S (-d) alpha r := by
  let s : ℝ := Real.sqrt (r ^ 2 + d)
  have hspos : 0 < s := Real.sqrt_pos.mpr (by positivity)
  have hs2 : s ^ 2 = r ^ 2 + d := Real.sq_sqrt (by positivity)
  have hinner : s ^ 2 - d = r ^ 2 := by rw [hs2]; ring
  have hinverse : Real.sqrt (s ^ 2 - d) = r := by rw [hinner, Real.sqrt_sq hr.le]
  have hclock : HasDerivAt (fun u : ℝ => Real.sqrt (u ^ 2 - d)) (s / r) s := by
    have h := ((hasDerivAt_pow 2 s).sub_const d).sqrt
      (show s ^ 2 - d ≠ 0 by rw [hinner]; positivity)
    convert h using 1
    simp only [hinverse, Nat.reduceSub, pow_one]
    field_simp [hr.ne']
    ring
  have halpha' : MDifferentiableAt 𝓘(ℝ, ℝ) I alpha (Real.sqrt (s ^ 2 - d)) := by
    simpa only [hinverse] using halpha
  have hvel := lVelocity_comp_of_hasDerivAt alpha
    (f := fun u : ℝ => Real.sqrt (u ^ 2 - d)) (s := s) halpha' hclock
  change lRegularizedLagrangian S 0 (fun u => alpha (Real.sqrt (u ^ 2 - d))) s *
    (r / s) = (s / r) * lRegularizedLagrangian S (-d) alpha r
  have htime : 0 - s ^ 2 = -d - r ^ 2 := by rw [hs2]; ring
  dsimp only [lRegularizedLagrangian]
  simp only [Function.comp_def] at hvel
  rw [hvel]
  simp_rw [hinverse, htime]
  simp only [map_smul, smul_apply, smul_eq_mul]
  have hkin := congrArg
    (fun u : ℝ => (S.base.metric (-d - r ^ 2)).inner (alpha u)
      (lVelocity (I := I) alpha u) (lVelocity (I := I) alpha u)) hinverse
  field_simp [hr.ne', hspos.ne']
  nlinarith only [hkin]

theorem lRegularizedAction_sqrt_sub_sq
    (S : SolutionOn (I := I) (M := M) D) {d a c : ℝ}
    (hd : 0 ≤ d) (ha : 0 < a) (hac : a ≤ c)
    (alpha : ℝ → M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha) :
    lRegularizedAction S 0 (fun s => alpha (Real.sqrt (s ^ 2 - d)))
      (Real.sqrt (a ^ 2 + d)) (Real.sqrt (c ^ 2 + d)) =
      ∫ r in a..c, (Real.sqrt (r ^ 2 + d) / r) *
        lRegularizedLagrangian S (-d) alpha r := by
  have hchange := intervalIntegral.integral_comp_mul_deriv_of_deriv_nonneg
    (f := fun r : ℝ => Real.sqrt (r ^ 2 + d))
    (f' := fun r : ℝ => r / Real.sqrt (r ^ 2 + d))
    (g := lRegularizedLagrangian S 0 (fun s => alpha (Real.sqrt (s ^ 2 - d))))
    (a := a) (b := c)
    (by fun_prop)
    (by
      intro r hr
      have hrpos : 0 < r := ha.trans (by simpa only [min_eq_left hac] using hr.1)
      have hrad : 0 < r ^ 2 + d := by positivity
      have hsqrt : 0 < Real.sqrt (r ^ 2 + d) := Real.sqrt_pos.mpr hrad
      have h := ((hasDerivAt_pow 2 r).add_const d).sqrt hrad.ne'
      convert h using 1
      simp only [Nat.reduceSub, pow_one]
      field_simp [hsqrt.ne']
      ring)
    (by
      intro r hr
      have hrpos : 0 < r := ha.trans (by simpa only [min_eq_left hac] using hr.1)
      exact div_nonneg hrpos.le (Real.sqrt_nonneg _))
  refine hchange.symm.trans ?_
  apply intervalIntegral.integral_congr
  intro r hr
  have hrpos : 0 < r := ha.trans_le (by simpa only [min_eq_left hac] using hr.1)
  simpa only [Function.comp_def] using lRegularizedLagrangian_sqrt_sub_sq_mul S hd hrpos
    alpha ((halpha.mdifferentiable (by simp)).mdifferentiableAt)

private theorem sqrt_add_sq_div_le {d a r : ℝ} (hd : 0 ≤ d) (ha : 0 < a) (har : a ≤ r) :
    Real.sqrt (r ^ 2 + d) / r ≤ Real.sqrt (a ^ 2 + d) / a := by
  have hr : 0 < r := ha.trans_le har
  have hradR : 0 ≤ r ^ 2 + d := add_nonneg (sq_nonneg r) hd
  have hradA : 0 ≤ a ^ 2 + d := add_nonneg (sq_nonneg a) hd
  have hsqR := Real.sq_sqrt hradR
  have hsqA := Real.sq_sqrt hradA
  have hasq : a ^ 2 ≤ r ^ 2 := (sq_le_sq₀ ha.le hr.le).mpr har
  have hprod := mul_le_mul_of_nonneg_left hasq hd
  apply (div_le_div_iff₀ hr ha).mpr
  apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) ha.le)
    (mul_nonneg (Real.sqrt_nonneg _) hr.le)).mp
  rw [mul_pow, mul_pow, hsqR, hsqA]
  nlinarith

variable [T2Space M]

theorem lRegularizedAction_sqrt_sub_sq_le
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S) {d a c : ℝ}
    (hd : 0 ≤ d) (ha : 0 < a) (hac : a ≤ c)
    (hcarrier : ∀ r ∈ Icc a c, -d - r ^ 2 ∈ D.carrier)
    (hscalar : ∀ r ∈ Icc a c, ∀ x : M, 0 ≤ S.scalar (-d - r ^ 2) x)
    (alpha : ℝ → M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha) :
    lRegularizedAction S 0 (fun s => alpha (Real.sqrt (s ^ 2 - d)))
      (Real.sqrt (a ^ 2 + d)) (Real.sqrt (c ^ 2 + d)) ≤
      (Real.sqrt (a ^ 2 + d) / a) * lRegularizedAction S (-d) alpha a c := by
  rw [lRegularizedAction_sqrt_sub_sq S hd ha hac alpha halpha]
  have hlag : ContinuousOn (lRegularizedLagrangian S (-d) alpha) (Icc a c) := by
    have h := lRegularizedLagrangian_continuousOn_carrier S hS alpha halpha
    simpa only [Function.comp_def, id_eq] using
      h.comp (continuous_const.prodMk continuous_id).continuousOn hcarrier
  have hweight : ContinuousOn (fun r : ℝ => Real.sqrt (r ^ 2 + d) / r) (Icc a c) := by
    have hnum : Continuous (fun r : ℝ => Real.sqrt (r ^ 2 + d)) := by fun_prop
    exact hnum.continuousOn.div continuousOn_id
      (fun r hr => (ha.trans_le hr.1).ne')
  have hint := intervalIntegral.integral_mono_on (μ := volume) hac
    ((hweight.mul hlag).intervalIntegrable_of_Icc hac)
    ((hlag.intervalIntegrable_of_Icc hac).const_mul (Real.sqrt (a ^ 2 + d) / a))
    (fun r hr => mul_le_mul_of_nonneg_right (sqrt_add_sq_div_le hd ha hr.1) (by
      dsimp only [lRegularizedLagrangian]
      exact add_nonneg
        (mul_nonneg (by norm_num) (metric_inner_self_nonneg _ _ _))
        (mul_nonneg (by positivity) (hscalar r hr (alpha r)))))
  rw [intervalIntegral.integral_const_mul] at hint
  exact hint

end DifferentialGeometry.PDE.RicciFlow.Perelman
