import DifferentialGeometry.Analysis.ODE.GeodesicLimits.CommonLocalFlows
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ApproximatesLinearOn

/-!
# Uniform inverse radius under `C¹` convergence (LFR09 kernel, step (b)–(c))

W4-F7b's smallest failing statement for LFR09 was a radius `b > 0`, uniform in `i`, on which the
maps `w ↦ exp_x^{h_i}(w)` are uniformly close in `C¹` to an isomorphism, so that the contraction
argument solves `exp_x^{h_i}(w) = y` for all `y` close to `x`. Abstract form, for any parametrised
family `G i : P × E → E` converging in `C¹` on a box around `(x₀, w₀)`:

* `exists_uniform_surjOn_of_mapCPConvergenceOn_one`: if the partial derivative in `w` of the limit at
  `(x₀, w₀)` is an isomorphism `A` and the limit has a derivative continuous at `(x₀, w₀)`, there are
  `b, c, K > 0` such that for a tail of `i`, every `x ∈ closedBall x₀ b` and every `y` with
  `‖y - G i (x, w₀)‖ ≤ c` there is `w ∈ closedBall w₀ b` with `G i (x, w) = y` and
  `‖w - w₀‖ ≤ K ‖y - G i (x, w₀)‖`.
-/

set_option autoImplicit false

noncomputable section

open Set Function Filter Metric
open scoped Topology NNReal

namespace DifferentialGeometry.Analysis.ODE.GeodesicLimits

open DifferentialGeometry.CheegerGromovCompactness

/-- **Uniform inverse radius under `C¹` convergence.** -/
theorem exists_uniform_surjOn_of_mapCPConvergenceOn_one
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    {G : ℕ → P × E → E} {GInf : P × E → E} {x₀ : P} {w₀ : E} {ρ : ℝ}
    (hconv : MapCPConvergenceOn (closedBall x₀ ρ ×ˢ closedBall w₀ ρ) 1 G GInf)
    (hG : ∀ᶠ i in atTop, ∀ q ∈ closedBall x₀ ρ ×ˢ closedBall w₀ ρ, DifferentiableAt ℝ (G i) q)
    (hGInf : ∀ q ∈ closedBall x₀ ρ ×ˢ closedBall w₀ ρ, DifferentiableAt ℝ GInf q)
    (hcont : ContinuousAt (fderiv ℝ GInf) (x₀, w₀)) (hρ : 0 < ρ) (A : E ≃L[ℝ] E)
    (hA : (fderiv ℝ GInf (x₀, w₀)).comp (ContinuousLinearMap.inr ℝ P E) = (A : E →L[ℝ] E)) :
    ∃ b c K : ℝ, 0 < b ∧ 0 < c ∧ 0 < K ∧ ∀ᶠ i in atTop, ∀ x ∈ closedBall x₀ b, ∀ y : E,
      ‖y - G i (x, w₀)‖ ≤ c →
        ∃ w ∈ closedBall w₀ b, G i (x, w) = y ∧ ‖w - w₀‖ ≤ K * ‖y - G i (x, w₀)‖ := by
  set κ : ℝ≥0 := ‖(A.symm : E →L[ℝ] E)‖₊ + 1 with hκ_def
  have hκ1 : (1 : ℝ) ≤ κ := by
    rw [hκ_def, NNReal.coe_add, NNReal.coe_one]
    linarith [(‖(A.symm : E →L[ℝ] E)‖₊).coe_nonneg]
  have hκ : (0 : ℝ) < κ := by linarith
  set c₀ : ℝ≥0 := ⟨1 / (2 * κ), by positivity⟩ with hc₀_def
  have hc₀ : (c₀ : ℝ) = 1 / (2 * κ) := rfl
  have hc₀pos : (0 : ℝ) < c₀ := by rw [hc₀]; positivity
  obtain ⟨b₁, hb₁, hb₁'⟩ := Metric.continuousAt_iff.mp hcont ((c₀ : ℝ) / 2) (by positivity)
  set b : ℝ := min (b₁ / 2) ρ with hb_def
  have hb : 0 < b := lt_min (by positivity) hρ
  have hbox : ∀ x ∈ closedBall x₀ b, ∀ w ∈ closedBall w₀ b,
      (x, w) ∈ closedBall x₀ ρ ×ˢ closedBall w₀ ρ ∧ dist (x, w) (x₀, w₀) < b₁ := by
    intro x hx w hw
    have hx' : dist x x₀ ≤ b := hx
    have hw' : dist w w₀ ≤ b := hw
    have hbρ : b ≤ ρ := min_le_right _ _
    have hbb : b ≤ b₁ / 2 := min_le_left _ _
    refine ⟨⟨mem_closedBall.mpr (hx'.trans hbρ), mem_closedBall.mpr (hw'.trans hbρ)⟩, ?_⟩
    rw [Prod.dist_eq]
    exact lt_of_le_of_lt (max_le (hx'.trans hbb) (hw'.trans hbb)) (by linarith)
  refine ⟨b, b / (2 * κ), 2 * κ, hb, by positivity, by positivity, ?_⟩
  obtain ⟨k0, hk0⟩ := hconv ((c₀ : ℝ) / 2) (by positivity)
  filter_upwards [hG, eventually_ge_atTop k0] with i hGi hi x hx y hy
  set f : E → E := fun w => G i (x, w) with hf_def
  have hderiv : ∀ w ∈ closedBall w₀ b, HasFDerivWithinAt f
      ((fderiv ℝ (G i) (x, w)).comp (ContinuousLinearMap.inr ℝ P E)) (closedBall w₀ b) w := by
    intro w hw
    have h1 := (hGi (x, w) (hbox x hx w hw).1).hasFDerivAt
    exact (h1.comp w (hasFDerivAt_prodMk_right x w)).hasFDerivWithinAt
  have hbound : ∀ w ∈ closedBall w₀ b,
      ‖(fderiv ℝ (G i) (x, w)).comp (ContinuousLinearMap.inr ℝ P E) - (A : E →L[ℝ] E)‖ ≤ c₀ := by
    intro w hw
    obtain ⟨hq, hq'⟩ := hbox x hx w hw
    have h1 : ‖fderiv ℝ (G i) (x, w) - fderiv ℝ GInf (x, w)‖ ≤ (c₀ : ℝ) / 2 := by
      have h := hk0 i hi 1 le_rfl (x, w) hq
      rwa [mapDerivNorm_one_eq (hGi _ hq) (hGInf _ hq)] at h
    have h2 : ‖fderiv ℝ GInf (x, w) - fderiv ℝ GInf (x₀, w₀)‖ < (c₀ : ℝ) / 2 := by
      have h := hb₁' hq'
      rwa [dist_eq_norm] at h
    rw [← hA, ← ContinuousLinearMap.sub_comp]
    calc ‖(fderiv ℝ (G i) (x, w) - fderiv ℝ GInf (x₀, w₀)).comp (ContinuousLinearMap.inr ℝ P E)‖
        ≤ ‖fderiv ℝ (G i) (x, w) - fderiv ℝ GInf (x₀, w₀)‖ * ‖ContinuousLinearMap.inr ℝ P E‖ :=
          ContinuousLinearMap.opNorm_comp_le _ _
      _ ≤ ‖fderiv ℝ (G i) (x, w) - fderiv ℝ GInf (x₀, w₀)‖ * 1 :=
          mul_le_mul_of_nonneg_left (ContinuousLinearMap.norm_inr_le_one ℝ P E) (norm_nonneg _)
      _ = ‖(fderiv ℝ (G i) (x, w) - fderiv ℝ GInf (x, w)) +
            (fderiv ℝ GInf (x, w) - fderiv ℝ GInf (x₀, w₀))‖ := by
          rw [mul_one, sub_add_sub_cancel]
      _ ≤ ‖fderiv ℝ (G i) (x, w) - fderiv ℝ GInf (x, w)‖ +
            ‖fderiv ℝ GInf (x, w) - fderiv ℝ GInf (x₀, w₀)‖ := norm_add_le _ _
      _ ≤ (c₀ : ℝ) / 2 + (c₀ : ℝ) / 2 := add_le_add h1 h2.le
      _ = c₀ := by ring
  have happrox : ApproximatesLinearOn f (A : E →L[ℝ] E) (closedBall w₀ b) c₀ := by
    intro w₁ hw₁ w₂ hw₂
    exact (convex_closedBall w₀ b).norm_image_sub_le_of_norm_hasFDerivWithin_le' hderiv hbound
      hw₂ hw₁
  let N : (A : E →L[ℝ] E).NonlinearRightInverse :=
    { toFun := A.symm
      nnnorm := κ
      bound' := fun z => by
        have h := (A.symm : E →L[ℝ] E).le_opNorm z
        have hk : ‖(A.symm : E →L[ℝ] E)‖ ≤ κ := by
          rw [hκ_def, NNReal.coe_add, coe_nnnorm, NNReal.coe_one]
          linarith
        exact h.trans (mul_le_mul_of_nonneg_right hk (norm_nonneg _))
      right_inv' := fun z => A.apply_symm_apply z }
  set ε : ℝ := 2 * κ * ‖y - f w₀‖ with hε_def
  have hε0 : 0 ≤ ε := by positivity
  have hεb : ε ≤ b := by
    have h := mul_le_mul_of_nonneg_left hy (by positivity : (0 : ℝ) ≤ 2 * κ)
    rw [hε_def]
    calc 2 * (κ : ℝ) * ‖y - f w₀‖ ≤ 2 * κ * (b / (2 * κ)) := h
      _ = b := by field_simp
  have hsurj := happrox.surjOn_closedBall_of_nonlinearRightInverse N hε0
    (closedBall_subset_closedBall hεb)
  have hy' : y ∈ closedBall (f w₀) (((N.nnnorm : ℝ)⁻¹ - c₀) * ε) := by
    have hN : (N.nnnorm : ℝ) = κ := rfl
    rw [mem_closedBall, dist_eq_norm, hN, hc₀, hε_def]
    have h : ((κ : ℝ)⁻¹ - 1 / (2 * κ)) * (2 * κ * ‖y - f w₀‖) = ‖y - f w₀‖ := by
      field_simp
      ring
    rw [h]
  obtain ⟨w, hw, hfw⟩ := hsurj hy'
  refine ⟨w, closedBall_subset_closedBall hεb hw, hfw, ?_⟩
  rw [mem_closedBall, dist_eq_norm] at hw
  exact hw

end DifferentialGeometry.Analysis.ODE.GeodesicLimits
