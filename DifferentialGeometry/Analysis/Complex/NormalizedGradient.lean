import DifferentialGeometry.Analysis.Calculus.BilinearBounds
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NormNum
import Lean.Elab.Tactic.Omega
import Mathlib.Tactic.Ring

set_option autoImplicit false

noncomputable section

open Set Filter Metric
open scoped Topology ContDiff

namespace DifferentialGeometry.Analysis

/-- The differential of a height composed with inverse multiplication by the
branched projection differential. At a positive branch order this is zero at
zero, using the field inverse of zero. -/
def complexPowerNormalizedGradient (m : ℕ) (H : ℂ → ℝ) (w : ℂ) : ℂ →L[ℝ] ℝ :=
  (fderiv ℝ H w).comp (ContinuousLinearMap.mul ℝ ℂ ((w ^ m)⁻¹))

private theorem norm_fderiv_order_of_hessian_order
    {h : ℂ → ℝ} {a : ℂ} {m : ℕ} {C : ℝ}
    (hh : ContDiffAt ℝ 2 h a) (ha : fderiv ℝ h a = 0) (hC : 0 ≤ C)
    (hbound : ∀ᶠ z in 𝓝 a,
      ‖fderiv ℝ (fderiv ℝ h) z‖ ≤ C * ‖z - a‖ ^ m) :
    ∀ᶠ z in 𝓝 a, ‖fderiv ℝ h z‖ ≤ C * ‖z - a‖ ^ (m + 1) := by
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp
    ((hh.eventually (by norm_num)).and hbound)
  filter_upwards [ball_mem_nhds a hr] with z hz
  have hzlt : ‖z - a‖ < r := by simpa only [mem_ball, dist_eq_norm] using hz
  have hsub : closedBall a ‖z - a‖ ⊆ ball a r := closedBall_subset_ball hzlt
  have hd (y : ℂ) (hy : y ∈ closedBall a ‖z - a‖) :
      DifferentiableAt ℝ (fderiv ℝ h) y :=
    ((hball (hsub hy)).1.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hnorm (y : ℂ) (hy : y ∈ closedBall a ‖z - a‖) :
      ‖fderiv ℝ (fderiv ℝ h) y‖ ≤ C * ‖z - a‖ ^ m := by
    have hrad : ‖y - a‖ ≤ ‖z - a‖ := by
      simpa only [mem_closedBall, dist_eq_norm] using hy
    exact (hball (hsub hy)).2.trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) hrad _) hC)
  have hmean := Convex.norm_image_sub_le_of_norm_fderiv_le hd hnorm
    (convex_closedBall a ‖z - a‖)
    (mem_closedBall_self (norm_nonneg (z - a)))
    (show z ∈ closedBall a ‖z - a‖ by simp only [mem_closedBall, dist_eq_norm, le_refl])
  simpa only [ha, sub_zero, pow_succ, mul_assoc] using hmean

private theorem inverse_power_fderiv
    (m : ℕ) {w : ℂ} (hw : w ≠ 0) :
    HasFDerivAt (fun z : ℂ => (z ^ m)⁻¹)
      ((ContinuousLinearMap.toSpanSingleton ℂ
        (-(m : ℂ) * (w ^ (m + 1))⁻¹)).restrictScalars ℝ) w := by
  have he : -(m : ℤ) - 1 = -((m + 1 : ℕ) : ℤ) := by omega
  have hd := ((hasDerivAt_zpow (-(m : ℤ)) w (Or.inl hw)).hasFDerivAt).restrictScalars ℝ
  simpa only [he, Int.cast_neg, Int.cast_natCast, zpow_neg, zpow_natCast] using hd

private theorem normalized_gradient_pointwise_derivative_bound
    {H : ℂ → ℝ} {m : ℕ} {C : ℝ} (hC : 0 ≤ C) {w : ℂ} (hw : w ≠ 0)
    (hH : ContDiffAt ℝ 2 H w)
    (hD : ‖fderiv ℝ H w‖ ≤ C * ‖w‖ ^ (m + 1))
    (hDD : ‖fderiv ℝ (fderiv ℝ H) w‖ ≤ C * ‖w‖ ^ m) :
    DifferentiableAt ℝ (complexPowerNormalizedGradient m H) w ∧
      ‖fderiv ℝ (complexPowerNormalizedGradient m H) w‖ ≤ C * ((m : ℝ) + 1) := by
  let M : ℂ → ℂ →L[ℝ] ℂ := fun z => ContinuousLinearMap.mul ℝ ℂ ((z ^ m)⁻¹)
  have hi := inverse_power_fderiv m hw
  have hdH : DifferentiableAt ℝ (fderiv ℝ H) w :=
    (hH.fderiv_right (m := 1) (by norm_num)).differentiableAt_one
  have hdM : DifferentiableAt ℝ M w :=
    ((ContinuousLinearMap.mul ℝ ℂ).hasFDerivAt.comp w hi).differentiableAt
  refine ⟨hdH.clm_comp hdM, ?_⟩
  have hM : ‖M w‖ = (‖w‖ ^ m)⁻¹ := by
    simp only [M, ContinuousLinearMap.opNorm_mul_apply, norm_inv, norm_pow]
  have hiNorm : ‖fderiv ℝ (fun z : ℂ => (z ^ m)⁻¹) w‖ =
      (m : ℝ) * (‖w‖ ^ (m + 1))⁻¹ := by
    rw [hi.fderiv, ContinuousLinearMap.norm_restrictScalars,
      ContinuousLinearMap.norm_toSpanSingleton]
    simp only [norm_mul, norm_neg, Complex.norm_natCast, norm_inv, norm_pow]
  have hDM : ‖fderiv ℝ M w‖ ≤ (m : ℝ) * (‖w‖ ^ (m + 1))⁻¹ := by
    change ‖fderiv ℝ ((ContinuousLinearMap.mul ℝ ℂ) ∘
      (fun z : ℂ => (z ^ m)⁻¹)) w‖ ≤ (m : ℝ) * (‖w‖ ^ (m + 1))⁻¹
    rw [((ContinuousLinearMap.mul ℝ ℂ).hasFDerivAt.comp w hi).fderiv]
    calc
      _ ≤ ‖ContinuousLinearMap.mul ℝ ℂ‖ *
          ‖(ContinuousLinearMap.toSpanSingleton ℂ
            (-(m : ℂ) * (w ^ (m + 1))⁻¹)).restrictScalars ℝ‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ 1 * ‖(ContinuousLinearMap.toSpanSingleton ℂ
            (-(m : ℂ) * (w ^ (m + 1))⁻¹)).restrictScalars ℝ‖ :=
        mul_le_mul_of_nonneg_right (ContinuousLinearMap.opNorm_mul_le ℝ ℂ) (norm_nonneg _)
      _ = _ := by
        rw [one_mul, ← hi.fderiv, hiNorm]
  have hbil := ContinuousLinearMap.norm_fderiv_bilinear_le
    (ContinuousLinearMap.compL ℝ ℂ ℂ ℝ) hdH hdM
  have hbase : ‖fderiv ℝ (complexPowerNormalizedGradient m H) w‖ ≤
      ‖fderiv ℝ H w‖ * ‖fderiv ℝ M w‖ +
        ‖fderiv ℝ (fderiv ℝ H) w‖ * ‖M w‖ := by
    apply hbil.trans
    exact mul_le_of_le_one_left (by positivity)
      (ContinuousLinearMap.norm_compL_le ℝ ℂ ℂ ℝ)
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  calc
    _ ≤ (C * ‖w‖ ^ (m + 1)) * ((m : ℝ) * (‖w‖ ^ (m + 1))⁻¹) +
        (C * ‖w‖ ^ m) * (‖w‖ ^ m)⁻¹ := by
      apply hbase.trans
      rw [hM]
      exact add_le_add
        (mul_le_mul hD hDM (norm_nonneg _) (by positivity))
        (mul_le_mul_of_nonneg_right hDD (by positivity))
    _ = C * ((m : ℝ) + 1) := by
      field_simp [hn]

private theorem lipschitzOnWith_of_radial_and_punctured_derivative_bounds
    {f : ℂ → ℂ →L[ℝ] ℝ} {r K : ℝ} (hK : 0 ≤ K)
    (hsize : ∀ w ∈ ball (0 : ℂ) r, ‖f w‖ ≤ K * ‖w‖)
    (hd : ∀ w ∈ ball (0 : ℂ) r, w ≠ 0 → DifferentiableAt ℝ f w)
    (hder : ∀ w ∈ ball (0 : ℂ) r, w ≠ 0 → ‖fderiv ℝ f w‖ ≤ K) :
    LipschitzOnWith (3 * K).toNNReal f (ball (0 : ℂ) r) := by
  apply LipschitzOnWith.of_dist_le'
  intro x hx y hy
  simp only [dist_eq_norm]
  by_cases hnear : ‖x - y‖ < ‖x‖
  · let s := ball (0 : ℂ) r ∩ ball x ‖x‖
    have hzero (z : ℂ) (hz : z ∈ s) : z ≠ 0 := by
      intro hz0
      have hz' := hz.2
      exact (lt_irrefl ‖x‖) (by
        simpa only [hz0, mem_ball, dist_zero_left] using hz')
    have hnormx : 0 < ‖x‖ := lt_of_le_of_lt (norm_nonneg _) hnear
    have hxs : x ∈ s := ⟨hx, mem_ball_self hnormx⟩
    have hys : y ∈ s := ⟨hy, by simpa only [mem_ball, dist_eq_norm, norm_sub_rev] using hnear⟩
    have hmean := Convex.norm_image_sub_le_of_norm_fderiv_le
      (fun z hz => hd z hz.1 (hzero z hz))
      (fun z hz => hder z hz.1 (hzero z hz))
      ((convex_ball (0 : ℂ) r).inter (convex_ball x ‖x‖)) hys hxs
    exact hmean.trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
  · have hfar : ‖x‖ ≤ ‖x - y‖ := le_of_not_gt hnear
    have htri : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
      have ht : ‖y‖ ≤ ‖y - x‖ + ‖x‖ := by
        simpa only [dist_eq_norm, sub_zero] using (dist_triangle y x (0 : ℂ))
      calc
        _ ≤ ‖y - x‖ + ‖x‖ := ht
        _ = ‖x‖ + ‖x - y‖ := by rw [norm_sub_rev, add_comm]
    calc
      _ ≤ ‖f x‖ + ‖f y‖ := norm_sub_le _ _
      _ ≤ K * ‖x‖ + K * ‖y‖ := add_le_add (hsize x hx) (hsize y hy)
      _ ≤ (3 * K) * ‖x - y‖ := by
        have hxK := mul_le_mul_of_nonneg_left hfar hK
        have hyK := mul_le_mul_of_nonneg_left htri hK
        nlinarith

/-- A vanishing Hessian controls the actual normalized slope and its punctured
derivative. The resulting slope is Lipschitz through the branch center; no
center derivative for the normalized slope is asserted. -/
theorem exists_normalized_gradient_bounds_of_hessian_order
    {H : ℂ → ℝ} {m : ℕ} (hm : 1 ≤ m)
    (hH : ContDiffAt ℝ 2 H 0) (hD0 : fderiv ℝ H 0 = 0)
    (hbound : ∃ C > 0, ∀ᶠ w in 𝓝 (0 : ℂ),
      ‖fderiv ℝ (fderiv ℝ H) w‖ ≤ C * ‖w‖ ^ m) :
    let R := complexPowerNormalizedGradient m H
    R 0 = 0 ∧ ∃ r > 0, ∃ K > 0,
      (∀ w ∈ ball (0 : ℂ) r, ‖R w‖ ≤ K * ‖w‖) ∧
      (∀ w ∈ ball (0 : ℂ) r, w ≠ 0 →
        DifferentiableAt ℝ R w ∧ ‖fderiv ℝ R w‖ ≤ K) ∧
      LipschitzOnWith (3 * K).toNNReal R (ball (0 : ℂ) r) := by
  let R := complexPowerNormalizedGradient m H
  have hm0 : m ≠ 0 := Nat.ne_of_gt (lt_of_lt_of_le Nat.zero_lt_one hm)
  have hR0 : R 0 = 0 := by
    simp only [R, complexPowerNormalizedGradient, zero_pow hm0, inv_zero, map_zero,
      ContinuousLinearMap.comp_zero]
  obtain ⟨C, hC, hDD⟩ := hbound
  have hDD' : ∀ᶠ w in 𝓝 (0 : ℂ),
      ‖fderiv ℝ (fderiv ℝ H) w‖ ≤ C * ‖w - 0‖ ^ m := by
    simpa only [sub_zero] using hDD
  have hD := norm_fderiv_order_of_hessian_order hH hD0 hC.le hDD'
  obtain ⟨r, hr, hb⟩ := Metric.mem_nhds_iff.mp
    (((hH.eventually (by norm_num)).and hDD).and hD)
  let K := C * ((m : ℝ) + 1)
  have hK : 0 < K := by dsimp only [K]; positivity
  have hCK : C ≤ K := by
    dsimp only [K]
    nlinarith [mul_nonneg hC.le (Nat.cast_nonneg (α := ℝ) m)]
  have hsize (w : ℂ) (hw : w ∈ ball (0 : ℂ) r) : ‖R w‖ ≤ K * ‖w‖ := by
    by_cases hw0 : w = 0
    · subst w
      simp only [hR0, norm_zero, mul_zero, le_refl]
    have hdw : ‖fderiv ℝ H w‖ ≤ C * ‖w‖ ^ (m + 1) := by
      simpa only [sub_zero] using (hb hw).2
    have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw0
    calc
      _ ≤ ‖fderiv ℝ H w‖ * ‖ContinuousLinearMap.mul ℝ ℂ ((w ^ m)⁻¹)‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ (C * ‖w‖ ^ (m + 1)) * (‖w‖ ^ m)⁻¹ := by
        simpa only [ContinuousLinearMap.opNorm_mul_apply, norm_inv, norm_pow] using
          mul_le_mul_of_nonneg_right hdw
            (norm_nonneg (ContinuousLinearMap.mul ℝ ℂ ((w ^ m)⁻¹)))
      _ = C * ‖w‖ := by
        rw [pow_succ]
        field_simp [hn]
      _ ≤ K * ‖w‖ := mul_le_mul_of_nonneg_right hCK (norm_nonneg _)
  have hder (w : ℂ) (hw : w ∈ ball (0 : ℂ) r) (hw0 : w ≠ 0) :
      DifferentiableAt ℝ R w ∧ ‖fderiv ℝ R w‖ ≤ K := by
    apply normalized_gradient_pointwise_derivative_bound hC.le hw0 (hb hw).1.1
    · simpa only [sub_zero] using (hb hw).2
    · exact (hb hw).1.2
  exact ⟨hR0, r, hr, K, hK, hsize, hder,
    lipschitzOnWith_of_radial_and_punctured_derivative_bounds hK.le hsize
      (fun w hw hw0 => (hder w hw hw0).1) (fun w hw hw0 => (hder w hw hw0).2)⟩

end DifferentialGeometry.Analysis
