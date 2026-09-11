import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Geometry.Manifold.Diffeomorph
import Mathlib.Topology.Order.IntermediateValue

set_option autoImplicit false
noncomputable section
open Set Filter Function Manifold
open scoped ContDiff Topology
namespace DifferentialGeometry.Topology.Manifold

private def exponentialRadius (r : ℝ) : ℝ :=
  r + Real.smoothTransition (r - 1) * (Real.exp r - r)

private theorem radius_small {r : ℝ} (hr : r ≤ 1) : exponentialRadius r = r := by
  simp only [exponentialRadius, Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hr),
    zero_mul, add_zero]

private theorem radius_large {r : ℝ} (hr : 2 ≤ r) : exponentialRadius r = Real.exp r := by
  rw [exponentialRadius, Real.smoothTransition.one_of_one_le (by linarith), one_mul]
  ring

private theorem radius_smooth : ContDiff ℝ ∞ exponentialRadius :=
  contDiff_id.add ((Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const)).mul
    (Real.contDiff_exp.sub contDiff_id))

private theorem radius_deriv (r : ℝ) :
    HasDerivAt exponentialRadius
      (1 + deriv Real.smoothTransition (r - 1) * (Real.exp r - r) +
        Real.smoothTransition (r - 1) * (Real.exp r - 1)) r := by
  have hh := (hasDerivAt_id r).add
    ((((Real.smoothTransition.contDiff (n := (⊤ : ℕ∞))).differentiable (by simp)) (r - 1)).hasDerivAt.comp r
      ((hasDerivAt_id r).sub_const 1) |>.mul ((Real.hasDerivAt_exp r).sub (hasDerivAt_id r)))
  convert hh using 1
  all_goals first | rfl | (dsimp only [id_eq, Pi.sub_apply, Function.comp_apply]; ring)

private theorem radius_deriv_pos (r : ℝ) : 0 < deriv exponentialRadius r := by
  rw [(radius_deriv r).deriv]
  have hd : 0 ≤ deriv Real.smoothTransition (r - 1) := Real.smoothTransition.monotone.deriv_nonneg
  have he : 0 ≤ Real.exp r - r := by linarith [Real.add_one_le_exp r]
  have hp := mul_nonneg hd he
  by_cases hr : r ≤ 1
  · rw [Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hr), zero_mul, add_zero]
    linarith
  · have hx : 0 ≤ Real.exp r - 1 := by linarith [Real.add_one_le_exp r]
    have hq := mul_nonneg (Real.smoothTransition.nonneg (r - 1)) hx
    linarith

private theorem radius_strictMono : StrictMono exponentialRadius :=
  strictMono_of_deriv_pos radius_deriv_pos

private def radiusOrderIso : ℝ ≃o ℝ :=
  radius_strictMono.orderIsoOfSurjective exponentialRadius (radius_smooth.continuous.surjective
    (by
      apply Real.tendsto_exp_atTop.congr'
      filter_upwards [eventually_ge_atTop (2 : ℝ)] with r hr
      exact (radius_large hr).symm)
    (by
      apply tendsto_id.congr'
      filter_upwards [eventually_le_atBot (1 : ℝ)] with r hr
      exact (radius_small hr).symm))

private theorem inverse_smooth : ContDiff ℝ ∞ (radiusOrderIso.symm : ℝ → ℝ) :=
  radiusOrderIso.toHomeomorph.contDiff_symm_deriv
    (fun r => (radius_deriv_pos r).ne')
    (fun r => (radius_smooth.differentiable (by simp) r).hasDerivAt) radius_smooth

private theorem inverse_small {r : ℝ} (hr : r ≤ 1) : radiusOrderIso.symm r = r := by
  apply radiusOrderIso.injective
  rw [radiusOrderIso.apply_symm_apply]
  exact (radius_small hr).symm

private theorem radius_pos {r : ℝ} (hr : 0 < r) : 0 < exponentialRadius r := by
  have hh := radius_strictMono hr
  rwa [radius_small (by norm_num : (0 : ℝ) ≤ 1)] at hh

private theorem inverse_pos {r : ℝ} (hr : 0 < r) : 0 < radiusOrderIso.symm r := by
  have hh := radiusOrderIso.symm.strictMono hr
  rwa [inverse_small (by norm_num : (0 : ℝ) ≤ 1)] at hh

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

private def radialLift (f : ℝ → ℝ) (x : E) : E := by
  classical
  exact if x = 0 then 0 else (f ‖x‖ / ‖x‖) • x

private theorem lift_small (f : ℝ → ℝ) (hf : ∀ r ≤ 1, f r = r)
    (x : E) (hx : ‖x‖ ≤ 1) : radialLift f x = x := by
  classical
  by_cases hz : x = 0
  · simp only [radialLift, hz, ite_true]
  · simp only [radialLift, if_neg hz, hf _ hx, div_self (norm_ne_zero_iff.mpr hz), one_smul]

private theorem lift_norm (f : ℝ → ℝ) (hzero : f 0 = 0)
    (hnonneg : ∀ r, 0 ≤ r → 0 ≤ f r) (x : E) : ‖radialLift f x‖ = f ‖x‖ := by
  classical
  by_cases hz : x = 0
  · simp only [radialLift, hz, ite_true, norm_zero, hzero]
  · rw [radialLift, if_neg hz, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (div_nonneg (hnonneg _ (norm_nonneg x)) (norm_nonneg x)),
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hz)]

private theorem lift_smooth (f : ℝ → ℝ) (hf : ContDiff ℝ ∞ f)
    (hsmall : ∀ r ≤ 1, f r = r) : ContDiff ℝ ∞ (radialLift f : E → E) := by
  classical
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = 0
  · subst x
    apply contDiffAt_id.congr_of_eventuallyEq
    filter_upwards [continuous_norm.continuousAt.eventually_lt_const
      (by simp : ‖(0 : E)‖ < 1)] with y hy
    exact lift_small f hsmall y hy.le
  · have hn := contDiffAt_norm ℝ (n := ∞) hx
    apply (((hf.contDiffAt.comp x hn).div hn (norm_ne_zero_iff.mpr hx)).smul contDiffAt_id).congr_of_eventuallyEq
    filter_upwards [isOpen_compl_singleton.mem_nhds hx] with y hy
    change radialLift f y = (f ‖y‖ / ‖y‖) • y
    exact if_neg (show y ≠ 0 from hy)

private theorem lift_cancel (f g : ℝ → ℝ) (hf0 : f 0 = 0)
    (hfpos : ∀ r, 0 < r → 0 < f r) (hgf : ∀ r, g (f r) = r) (x : E) :
    radialLift g (radialLift f x) = x := by
  classical
  by_cases hx : x = 0
  · simp only [hx, radialLift, ite_true]
  · have hr := norm_pos_iff.mpr hx
    have hn := lift_norm f hf0 (fun r hr => by
      rcases hr.eq_or_lt with he | hp
      · rw [← he, hf0]
      · exact (hfpos r hp).le) x
    have hfx : radialLift f x ≠ 0 := norm_pos_iff.mp (hn.trans_gt (hfpos _ hr))
    rw [radialLift, if_neg hfx, hn, hgf, radialLift, if_neg hx, smul_smul]
    have hc : (‖x‖ / f ‖x‖) * (f ‖x‖ / ‖x‖) = 1 := by
      field_simp [(hfpos _ hr).ne', hr.ne']
    rw [hc, one_smul]

def radialExponentialDiffeomorph : E ≃ₘ[ℝ] E where
  toFun := radialLift exponentialRadius
  invFun := radialLift radiusOrderIso.symm
  left_inv := lift_cancel exponentialRadius radiusOrderIso.symm
    (radius_small (by norm_num)) (fun _ hr => radius_pos hr) radiusOrderIso.symm_apply_apply
  right_inv := lift_cancel radiusOrderIso.symm exponentialRadius
    (inverse_small (by norm_num)) (fun _ hr => inverse_pos hr) radiusOrderIso.apply_symm_apply
  contMDiff_toFun := (lift_smooth exponentialRadius radius_smooth (fun _ hr => radius_small hr)).contMDiff
  contMDiff_invFun := (lift_smooth radiusOrderIso.symm inverse_smooth (fun _ hr => inverse_small hr)).contMDiff

theorem radialExponentialDiffeomorph_of_norm_le_one (x : E) (hx : ‖x‖ ≤ 1) :
    radialExponentialDiffeomorph x = x := lift_small _ (fun _ hr => radius_small hr) x hx

theorem radialExponentialDiffeomorph_of_two_le_norm (x : E) (hx : 2 ≤ ‖x‖) :
    radialExponentialDiffeomorph x = (Real.exp ‖x‖ / ‖x‖) • x := by
  have hz : x ≠ 0 := norm_pos_iff.mp (by linarith)
  change radialLift exponentialRadius x = _
  rw [radialLift, if_neg hz, radius_large hx]

theorem norm_radialExponentialDiffeomorph (x : E) (hx : 2 ≤ ‖x‖) :
    ‖radialExponentialDiffeomorph x‖ = Real.exp ‖x‖ := by
  rw [radialExponentialDiffeomorph_of_two_le_norm x hx, norm_smul, Real.norm_eq_abs,
    abs_of_pos (div_pos (Real.exp_pos _) (by linarith)), div_mul_cancel₀ _ (by linarith : ‖x‖ ≠ 0)]

theorem radialExponentialDiffeomorph_linearIsometryEquiv (A : E ≃ₗᵢ[ℝ] E) (x : E) :
    radialExponentialDiffeomorph (A x) = A (radialExponentialDiffeomorph x) := by
  classical
  change radialLift exponentialRadius (A x) = A (radialLift exponentialRadius x)
  by_cases hx : x = 0
  · simp only [hx, map_zero, radialLift, ite_true]
  · have hAx : A x ≠ 0 := fun he => hx (A.injective (he.trans A.map_zero.symm))
    simp only [radialLift, if_neg hx, if_neg hAx, A.norm_map, map_smul]

theorem norm_radialExponentialDiffeomorph_lt_iff (x : E) (r : ℝ) (hr : 2 ≤ r) :
    ‖radialExponentialDiffeomorph x‖ < Real.exp r ↔ ‖x‖ < r := by
  have hn : ‖radialExponentialDiffeomorph x‖ = exponentialRadius ‖x‖ :=
    lift_norm exponentialRadius (radius_small (by norm_num))
      (fun s hs => by
        rcases hs.eq_or_lt with he | hp
        · rw [← he, radius_small (by norm_num)]
        · exact (radius_pos hp).le) x
  rw [hn, ← radius_large hr]
  exact radius_strictMono.lt_iff_lt

theorem radialExponentialDiffeomorph_image_ball (r : ℝ) (hr : 2 ≤ r) :
    radialExponentialDiffeomorph '' Metric.ball (0 : E) r = Metric.ball 0 (Real.exp r) := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    simpa only [Metric.mem_ball, dist_zero_right] using
      (norm_radialExponentialDiffeomorph_lt_iff x r hr).mpr
        (by simpa only [Metric.mem_ball, dist_zero_right] using hx)
  · intro hy
    refine ⟨radialExponentialDiffeomorph.symm y, ?_, radialExponentialDiffeomorph.apply_symm_apply y⟩
    rw [Metric.mem_ball, dist_zero_right, ← norm_radialExponentialDiffeomorph_lt_iff _ r hr,
      radialExponentialDiffeomorph.apply_symm_apply]
    simpa only [Metric.mem_ball, dist_zero_right] using hy
end DifferentialGeometry.Topology.Manifold
