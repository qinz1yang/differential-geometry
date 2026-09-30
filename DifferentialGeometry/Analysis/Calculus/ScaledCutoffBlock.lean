import DifferentialGeometry.Analysis.Calculus.WeightedAffineCutoff
import DifferentialGeometry.Analysis.Calculus.SecondDerivativeComposition
import DifferentialGeometry.Analysis.Calculus.CompositionBounds
import Mathlib.Analysis.Normed.Lp.ProdLp
import Mathlib.Tactic.FieldSimp

set_option autoImplicit false

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

noncomputable def scaledCutoffBlock (s : ℝ) (φ : E → ℝ) (u : E) : WithLp 2 (E × ℝ) :=
  WithLp.toLp 2 (φ (s⁻¹ • u) • u, s * φ (s⁻¹ • u))

theorem contDiff_scaledCutoffBlock {φ : E → ℝ} {n : WithTop ℕ∞}
    (hφ : ContDiff ℝ n φ) (s : ℝ) : ContDiff ℝ n (scaledCutoffBlock s φ) := by
  have h : ContDiff ℝ n (fun x : E => φ (s⁻¹ • x)) :=
    hφ.comp (contDiff_const.smul contDiff_id)
  exact (WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ).symm.contDiff.comp
    ((h.smul contDiff_id).prodMk (contDiff_const.mul h))

theorem scaledCutoffBlock_derivative_bounds {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ)
    {s C L₁ L₂ : ℝ} (hs : 0 < s) (hC : 0 ≤ C) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hvalue : ∀ x, φ x ∈ Set.Icc 0 1)
    (hsupport : tsupport φ ⊆ Metric.closedBall 0 C)
    (hfirst : ∀ x, ‖fderiv ℝ φ x‖ ≤ L₁)
    (hsecond : ∀ x, ‖fderiv ℝ (fderiv ℝ φ) x‖ ≤ L₂) (x : E) :
    ‖fderiv ℝ (scaledCutoffBlock s φ) x‖ ≤ 1 + (C + 1) * L₁ ∧
      ‖fderiv ℝ (fderiv ℝ (scaledCutoffBlock s φ)) x‖ ≤
        (2 * L₁ + (C + 1) * L₂) / s := by
  let S : E →L[ℝ] E := s⁻¹ • ContinuousLinearMap.id ℝ E
  let ψ : E → ℝ := φ ∘ S
  let L : E →L[ℝ] WithLp 2 (E × ℝ) :=
    (WithLp.prodContinuousLinearEquiv 2 ℝ E ℝ).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.inl ℝ E ℝ)
  let b : WithLp 2 (E × ℝ) := WithLp.toLp 2 (0, s)
  have hS : ‖S‖ ≤ s⁻¹ := by
    rw [show S = s⁻¹ • ContinuousLinearMap.id ℝ E from rfl, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hs)]
    exact (mul_le_mul_of_nonneg_left ContinuousLinearMap.norm_id_le (inv_nonneg.mpr hs.le)).trans_eq
      (mul_one _)
  have hL : ‖L‖ ≤ 1 := by
    apply L.opNorm_le_bound (by norm_num)
    intro y
    change ‖WithLp.toLp 2 (y, (0 : ℝ))‖ ≤ 1 * ‖y‖
    simp
  have hb : ‖b‖ = s := by
    rw [show b = WithLp.toLp 2 ((0 : E), s) from rfl, WithLp.norm_toLp_snd,
      Real.norm_eq_abs, abs_of_pos hs]
  have hψ : ContDiff ℝ 2 ψ := hφ.comp S.contDiff
  have hψderiv (y : E) := linear_precomp_derivative_bounds S hφ (inv_nonneg.mpr hs.le)
    hL₁ hL₂ hS hfirst hsecond y
  have hψsupport : ∀ y ∈ tsupport ψ, ‖L y + b‖ ≤ s * (C + 1) := by
    intro y hy
    have hz := hsupport (tsupport_comp_subset_preimage φ S.continuous hy)
    have hz' : s⁻¹ * ‖y‖ ≤ C := by
      simpa only [Metric.mem_closedBall, dist_zero_right, S, smul_apply,
        ContinuousLinearMap.id_apply, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hs)] using hz
    have hy' : ‖y‖ ≤ s * C := by
      have hh := mul_le_mul_of_nonneg_left hz' hs.le
      rwa [← mul_assoc, mul_inv_cancel₀ hs.ne', one_mul] at hh
    have hLy : ‖L y‖ = ‖y‖ := WithLp.norm_toLp_fst 2 E ℝ y
    have hh := norm_add_le (L y) b
    rw [hLy, hb] at hh
    nlinarith
  have hh := weighted_affine_cutoff_derivative_bounds L b hψ (M := 1) (by norm_num)
    (mul_nonneg hs.le (by linarith)) (mul_nonneg hL₁ (inv_nonneg.mpr hs.le))
    (mul_nonneg hL₂ (sq_nonneg s⁻¹))
    (fun y => by simpa only [ψ, Function.comp_apply, abs_of_nonneg (hvalue (S y)).1]
      using (hvalue (S y)).2)
    (fun y => (hψderiv y).1) (fun y => (hψderiv y).2) hψsupport x
  have heq : (fun y => ψ y • (L y + b)) = scaledCutoffBlock s φ := by
    funext y
    apply (WithLp.equiv 2 (E × ℝ)).injective
    simp [ψ, S, L, b, scaledCutoffBlock, mul_comm]
  dsimp only at hh
  rw [heq] at hh
  have h1 : L₁ * s⁻¹ * (s * (C + 1)) = (C + 1) * L₁ := by field_simp
  have h2 : L₂ * s⁻¹ ^ 2 * (s * (C + 1)) = (C + 1) * L₂ / s := by field_simp
  rw [h1, h2] at hh
  have h3 := mul_le_mul_of_nonneg_left hL (show 0 ≤ 2 * (L₁ * s⁻¹) by positivity)
  constructor
  · nlinarith [hh.1]
  · calc
      _ ≤ 2 * (L₁ * s⁻¹) + (C + 1) * L₂ / s := by nlinarith [hh.2]
      _ = _ := by ring

theorem scaledCutoffBlock_c1_comp_sub_le {X : Type*} [NormedAddCommGroup X]
    [NormedSpace ℝ X] {φ : E → ℝ} (hφ : ContDiff ℝ 2 φ)
    {s C L₁ L₂ : ℝ} (hs : 0 < s) (hC : 0 ≤ C) (hL₁ : 0 ≤ L₁) (hL₂ : 0 ≤ L₂)
    (hvalue : ∀ y, φ y ∈ Set.Icc 0 1)
    (hsupport : tsupport φ ⊆ Metric.closedBall 0 C)
    (hfirst : ∀ y, ‖fderiv ℝ φ y‖ ≤ L₁)
    (hsecond : ∀ y, ‖fderiv ℝ (fderiv ℝ φ) y‖ ≤ L₂)
    {U V : X → E} {x : X} (hU : DifferentiableAt ℝ U x) (hV : DifferentiableAt ℝ V x)
    {ε L : ℝ} (hε : 0 ≤ ε) (hL : 0 ≤ L)
    (hclose : ‖U x - V x‖ ≤ ε) (hDclose : ‖fderiv ℝ U x - fderiv ℝ V x‖ ≤ ε)
    (hDV : ‖fderiv ℝ V x‖ ≤ L) :
    max ‖scaledCutoffBlock s φ (U x) - scaledCutoffBlock s φ (V x)‖
      ‖fderiv ℝ (scaledCutoffBlock s φ ∘ U) x -
        fderiv ℝ (scaledCutoffBlock s φ ∘ V) x‖ ≤
      (1 + (C + 1) * L₁ + (2 * L₁ + (C + 1) * L₂) / s * L) * ε := by
  have hW := contDiff_scaledCutoffBlock hφ s
  have hDW : Differentiable ℝ (fderiv ℝ (scaledCutoffBlock s φ)) :=
    ((contDiff_succ_iff_fderiv (n := 1)).mp hW).2.2.differentiable (by norm_num)
  have hb (y : E) := scaledCutoffBlock_derivative_bounds hφ hs hC hL₁ hL₂
    hvalue hsupport hfirst hsecond y
  exact c1_comp_sub_le_of_derivative_bounds (hW.differentiable (by norm_num)) hDW hU hV
    (by positivity) (by positivity) hL hε (fun y => (hb y).1) (fun y => (hb y).2)
    hclose hDclose hDV

end DifferentialGeometry.Analysis
