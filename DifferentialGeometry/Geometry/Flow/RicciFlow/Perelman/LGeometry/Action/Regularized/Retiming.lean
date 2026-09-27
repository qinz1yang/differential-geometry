import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Cost.Continuity.CarrierBaseTime

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open MeasureTheory Set
open DifferentialGeometry.Geometry.Curvature
open scoped _root_.Manifold ContDiff

variable {E H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [T2Space M] {D : RealTimeInterval}

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M] in
private theorem lVelocity_mul_of_mdifferentiableAt
    (alpha : ℝ → M) (c s : ℝ)
    (halpha : MDifferentiableAt 𝓘(ℝ, ℝ) I alpha (c * s)) :
    lVelocity (I := I) (fun r => alpha (c * r)) s =
      c • lVelocity (I := I) alpha (c * s) := by
  let A : TangentSpace 𝓘(ℝ, ℝ) s →L[ℝ] TangentSpace 𝓘(ℝ, ℝ) (c * s) :=
    modelLinearMapToTangent
      (x := s) (y := c * s) (A := c • ContinuousLinearMap.id ℝ ℝ)
  have hscale : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ)
      (fun r : ℝ => c * r) s A :=
    HasFDerivAt.hasMFDerivAt_model ((hasFDerivAt_id s).const_mul c)
  have hcomp := halpha.hasMFDerivAt.comp s hscale
  have hmodel := congrArg tangentLinearMapToModel hcomp.mfderiv
  rw [tangentLinearMapToModel_comp] at hmodel
  have hA : tangentLinearMapToModel A = c • ContinuousLinearMap.id ℝ ℝ :=
    tangentLinearMapToModel_modelLinearMapToTangent
  rw [hA] at hmodel
  have happ := congrArg (fun L : ℝ →L[ℝ] E => L 1) hmodel
  apply (tangentSpaceModelContinuousLinearEquiv (I := I) (alpha (c * s))).injective
  simpa only [lVelocity, tangentLinearMapToModel_apply,
    tangentSpaceModelContinuousLinearEquiv_apply,
    tangentSpaceModelContinuousLinearEquiv_symm_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply,
    Function.comp_def, smul_apply, id_eq, map_smul] using happ

theorem lRegularizedAction_mul_le_of_metric_comparison
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b c C a : ℝ} (ha : 0 ≤ a) (hc : 1 ≤ c) (hC : 1 ≤ C)
    (hsource : ∀ s ∈ Icc 0 a, b - s ^ 2 ∈ D.carrier)
    (htarget : ∀ s ∈ Icc 0 (c * a), -(s ^ 2) ∈ D.carrier)
    (hmetric : ∀ s ∈ Icc 0 a, ∀ x : M, ∀ v : TangentSpace I x,
      (S.base.metric (b - s ^ 2)).inner x v v ≤
        C * (S.base.metric (-((c * s) ^ 2))).inner x v v)
    (hscalar : ∀ s ∈ Icc 0 a, ∀ x : M,
      S.scalar (b - s ^ 2) x ≤ S.scalar (-((c * s) ^ 2)) x)
    (hnonneg : ∀ s ∈ Icc 0 a, ∀ x : M,
      0 ≤ S.scalar (-((c * s) ^ 2)) x)
    (alpha : ℝ → M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha) :
    lRegularizedAction S b (fun s => alpha (c * s)) 0 a ≤
      C * c * lRegularizedAction S 0 alpha 0 (c * a) := by
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  have hc2 : 1 ≤ c ^ 2 := by nlinarith
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hbeta : ContMDiff 𝓘(ℝ, ℝ) I 1 (fun s => alpha (c * s)) :=
    halpha.comp (contDiff_const.mul contDiff_id).contMDiff
  have hsourceCont :
      ContinuousOn (lRegularizedLagrangian S b (fun s => alpha (c * s))) (Icc 0 a) := by
    have h := lRegularizedLagrangian_continuousOn_carrier S hS
      (fun s => alpha (c * s)) hbeta
    simpa only [Function.comp_def, id_eq] using
      h.comp (continuous_const.prodMk continuous_id).continuousOn hsource
  have htargetCont : ContinuousOn (lRegularizedLagrangian S 0 alpha) (Icc 0 (c * a)) := by
    have h := lRegularizedLagrangian_continuousOn_carrier S hS alpha halpha
    apply h.comp (continuous_const.prodMk continuous_id).continuousOn
    intro s hs
    change 0 - s ^ 2 ∈ D.carrier
    simpa only [zero_sub] using htarget s hs
  have hscaledCont :
      ContinuousOn (fun s => lRegularizedLagrangian S 0 alpha (c * s)) (Icc 0 a) :=
    htargetCont.comp (continuous_const.mul continuous_id).continuousOn
      (fun s hs => ⟨mul_nonneg hcpos.le hs.1,
        mul_le_mul_of_nonneg_left hs.2 hcpos.le⟩)
  have hpoint (s : ℝ) (hs : s ∈ Icc 0 a) :
      lRegularizedLagrangian S b (fun r => alpha (c * r)) s ≤
        (C * c ^ 2) * lRegularizedLagrangian S 0 alpha (c * s) := by
    have hv := lVelocity_mul_of_mdifferentiableAt alpha c s
      ((halpha.mdifferentiable (by simp)).mdifferentiableAt)
    have hquad :
        (S.base.metric (b - s ^ 2)).inner (alpha (c * s))
          (c • lVelocity (I := I) alpha (c * s))
          (c • lVelocity (I := I) alpha (c * s)) =
        c ^ 2 * (S.base.metric (b - s ^ 2)).inner (alpha (c * s))
          (lVelocity (I := I) alpha (c * s))
          (lVelocity (I := I) alpha (c * s)) := by
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
    have hkin := mul_le_mul_of_nonneg_left
      (hmetric s hs (alpha (c * s)) (lVelocity (I := I) alpha (c * s)))
      (sq_nonneg c)
    have hscal := mul_le_mul_of_nonneg_left (hscalar s hs (alpha (c * s)))
      (by positivity : 0 ≤ 2 * s ^ 2)
    have hfactor : 1 ≤ C * c ^ 2 * c ^ 2 := by
      calc
        1 = 1 * 1 * 1 := by norm_num
        _ ≤ C * c ^ 2 * c ^ 2 :=
          mul_le_mul (mul_le_mul hC hc2 zero_le_one hC0) hc2
            zero_le_one (mul_nonneg hC0 (sq_nonneg c))
    have hpot := mul_le_mul_of_nonneg_right hfactor
      (mul_nonneg (by positivity : 0 ≤ 2 * s ^ 2) (hnonneg s hs (alpha (c * s))))
    dsimp only [lRegularizedLagrangian]
    rw [hv, hquad]
    simp only [zero_sub]
    nlinarith
  have hint := intervalIntegral.integral_mono_on (μ := volume) ha
    (hsourceCont.intervalIntegrable_of_Icc ha)
    ((hscaledCont.intervalIntegrable_of_Icc ha).const_mul (C * c ^ 2)) hpoint
  rw [intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left _ hcpos.ne', mul_zero, smul_eq_mul] at hint
  change lRegularizedAction S b (fun s => alpha (c * s)) 0 a ≤
    (C * c ^ 2) * (c⁻¹ * lRegularizedAction S 0 alpha 0 (c * a)) at hint
  have hcoeff : (C * c ^ 2) * c⁻¹ = C * c := by
    calc
      (C * c ^ 2) * c⁻¹ = (C * c) * (c * c⁻¹) := by ring
      _ = C * c := by rw [mul_inv_cancel₀ hcpos.ne', mul_one]
  exact hint.trans_eq (by rw [← mul_assoc, hcoeff])

theorem lRegularizedAction_mul_le_add_of_metric_antitone
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn S)
    {b c a R : ℝ} (ha : 0 ≤ a) (hcpos : 0 < c) (hc : c ≤ 1)
    (hshift : (1 - c ^ 2) * a ^ 2 ≤ -b)
    (hcarrier : D.carrier = Iic 0)
    (hmetric : ∀ x : M, ∀ v : TangentSpace I x,
      AntitoneOn (fun t => (S.base.metric t).inner x v v) (Iic 0))
    (hscalar : ∀ t ≤ 0, ∀ x : M, 0 ≤ S.scalar t x ∧ S.scalar t x ≤ R)
    (alpha : ℝ → M) (halpha : ContMDiff 𝓘(ℝ, ℝ) I 1 alpha) :
    lRegularizedAction S 0 (fun s => alpha (c * s)) 0 a ≤
      c * lRegularizedAction S b alpha 0 (c * a) + 2 * R * a ^ 3 := by
  have hcoef : 0 ≤ 1 - c ^ 2 := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hc) (by linarith : 0 ≤ 1 + c)]
  have hb : b ≤ 0 := by
    have hprod := mul_nonneg hcoef (sq_nonneg a)
    linarith
  have hR : 0 ≤ R := (hscalar 0 le_rfl (alpha 0)).1.trans
    (hscalar 0 le_rfl (alpha 0)).2
  have hbeta : ContMDiff 𝓘(ℝ, ℝ) I 1 (fun s => alpha (c * s)) :=
    halpha.comp (contDiff_const.mul contDiff_id).contMDiff
  have htargetCont :
      ContinuousOn (lRegularizedLagrangian S 0 (fun s => alpha (c * s))) (Icc 0 a) := by
    have h := lRegularizedLagrangian_continuousOn_carrier S hS
      (fun s => alpha (c * s)) hbeta
    apply h.comp (continuous_const.prodMk continuous_id).continuousOn
    intro s _
    change 0 - s ^ 2 ∈ D.carrier
    rw [hcarrier]
    exact sub_nonpos.mpr (sq_nonneg s)
  have hsourceCont :
      ContinuousOn (lRegularizedLagrangian S b alpha) (Icc 0 (c * a)) := by
    have h := lRegularizedLagrangian_continuousOn_carrier S hS alpha halpha
    apply h.comp (continuous_const.prodMk continuous_id).continuousOn
    intro r _
    change b - r ^ 2 ∈ D.carrier
    rw [hcarrier]
    exact (sub_le_self b (sq_nonneg r)).trans hb
  have hscaledCont :
      ContinuousOn (fun s => lRegularizedLagrangian S b alpha (c * s)) (Icc 0 a) :=
    hsourceCont.comp (continuous_const.mul continuous_id).continuousOn
      (fun s hs => ⟨mul_nonneg hcpos.le hs.1,
        mul_le_mul_of_nonneg_left hs.2 hcpos.le⟩)
  have hpoint (s : ℝ) (hs : s ∈ Icc 0 a) :
      lRegularizedLagrangian S 0 (fun r => alpha (c * r)) s ≤
        c ^ 2 * lRegularizedLagrangian S b alpha (c * s) + 2 * a ^ 2 * R := by
    have hsquare : s ^ 2 ≤ a ^ 2 := pow_le_pow_left₀ hs.1 hs.2 2
    have hscaled : (1 - c ^ 2) * s ^ 2 ≤ -b :=
      (mul_le_mul_of_nonneg_left hsquare hcoef).trans hshift
    have horder : b - (c * s) ^ 2 ≤ -(s ^ 2) := by
      nlinarith only [hscaled]
    have htarget : -(s ^ 2) ≤ 0 := neg_nonpos.mpr (sq_nonneg s)
    have hsource : b - (c * s) ^ 2 ≤ 0 := horder.trans htarget
    have hv := lVelocity_mul_of_mdifferentiableAt alpha c s
      ((halpha.mdifferentiable (by simp)).mdifferentiableAt)
    have hquad :
        (S.base.metric (-(s ^ 2))).inner (alpha (c * s))
          (c • lVelocity (I := I) alpha (c * s))
          (c • lVelocity (I := I) alpha (c * s)) =
        c ^ 2 * (S.base.metric (-(s ^ 2))).inner (alpha (c * s))
          (lVelocity (I := I) alpha (c * s))
          (lVelocity (I := I) alpha (c * s)) := by
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
    have hkin := mul_le_mul_of_nonneg_left
      (hmetric (alpha (c * s)) (lVelocity (I := I) alpha (c * s))
        hsource htarget horder) (sq_nonneg c)
    have hpot0 := mul_le_mul_of_nonneg_left
      (hscalar _ htarget (alpha (c * s))).2
      (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) (sq_nonneg s))
    have hpot1 := mul_le_mul_of_nonneg_right hsquare hR
    have hpad : 0 ≤ c ^ 2 *
        (2 * (c * s) ^ 2 * S.scalar (b - (c * s) ^ 2) (alpha (c * s))) :=
      mul_nonneg (sq_nonneg c)
        (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg (c * s)))
          (hscalar _ hsource (alpha (c * s))).1)
    dsimp only [lRegularizedLagrangian]
    rw [hv]
    simp only [zero_sub]
    rw [hquad]
    nlinarith only [hkin, hpot0, hpot1, hpad]
  have hscaledInt :
      IntervalIntegrable (fun s => lRegularizedLagrangian S b alpha (c * s)) volume 0 a :=
    hscaledCont.intervalIntegrable_of_Icc ha
  have hint := intervalIntegral.integral_mono_on (μ := volume) ha
    (htargetCont.intervalIntegrable_of_Icc ha)
    ((hscaledInt.const_mul (c ^ 2)).add intervalIntegrable_const) hpoint
  rw [intervalIntegral.integral_add (hscaledInt.const_mul (c ^ 2)) intervalIntegrable_const,
    intervalIntegral.integral_const_mul,
    intervalIntegral.integral_comp_mul_left _ hcpos.ne', mul_zero,
    intervalIntegral.integral_const] at hint
  simp only [sub_zero, smul_eq_mul] at hint
  change lRegularizedAction S 0 (fun s => alpha (c * s)) 0 a ≤
    c ^ 2 * (c⁻¹ * lRegularizedAction S b alpha 0 (c * a)) + a * (2 * a ^ 2 * R) at hint
  have hcoeff : c ^ 2 * c⁻¹ = c := by
    calc
      c ^ 2 * c⁻¹ = c * (c * c⁻¹) := by ring
      _ = c := by rw [mul_inv_cancel₀ hcpos.ne', mul_one]
  refine hint.trans_eq ?_
  rw [← mul_assoc, hcoeff]
  ring

end DifferentialGeometry.PDE.RicciFlow.Perelman
