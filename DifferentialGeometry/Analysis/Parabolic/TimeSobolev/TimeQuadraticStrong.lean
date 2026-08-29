import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeOperatorWeak
import DifferentialGeometry.Analysis.Parabolic.TimeSobolev.TimeQuadratic

set_option autoImplicit false

noncomputable section

open Filter MeasureTheory Set

namespace DifferentialGeometry.Analysis.Parabolic.TimeSobolev

variable {X : Type*}
variable [NormedAddCommGroup X] [InnerProductSpace ℝ X] [CompleteSpace X]
variable {T : ℝ}

theorem timeQuad_strong
    (A : ℕ → ℝ → X →L[ℝ] X) (A_lim : ℝ → X →L[ℝ] X)
    (hA : ∀ n, AEStronglyMeasurable (A n) (timeMeasure T))
    (hA_lim : AEStronglyMeasurable A_lim (timeMeasure T))
    (C : ℕ → NNReal) (C_lim : NNReal)
    (hC : ∀ n, ∀ᵐ t ∂timeMeasure T, ‖A n t‖ ≤ (C n : ℝ))
    (hC_lim : ∀ᵐ t ∂timeMeasure T, ‖A_lim t‖ ≤ (C_lim : ℝ))
    (hconv : ∀ δ : ℝ, 0 < δ → ∀ᶠ n in atTop,
      ∀ᵐ t ∂timeMeasure T, ‖A n t - A_lim t‖ ≤ δ)
    (u : ℕ → timeL2 X T) (u_lim : timeL2 X T)
    (hu : Tendsto u atTop (nhds u_lim)) :
    Tendsto (fun n ↦ timeQuad (A n) (hA n) (C n) (hC n) (u n)) atTop
      (nhds (timeQuad A_lim hA_lim C_lim hC_lim u_lim)) := by
  let v : ℕ → timeL2 X T :=
    fun n ↦ timeOp (A n) (hA n) (C n) (hC n) (u n)
  let v_lim : timeL2 X T := timeOp A_lim hA_lim C_lim hC_lim u_lim
  have hu_weak : ∀ z, Tendsto (fun n ↦ inner ℝ (u n) z) atTop
      (nhds (inner ℝ u_lim z)) := fun z ↦ hu.inner tendsto_const_nhds
  have hv_weak : ∀ z, Tendsto (fun n ↦ inner ℝ (v n) z) atTop
      (nhds (inner ℝ v_lim z)) := by
    simpa only [v, v_lim] using
      timeOp_weak_unif A A_lim hA hA_lim C C_lim hC hC_lim hconv
        u u_lim hu_weak
  obtain ⟨D, hvD⟩ := banach_steinhaus (g := fun n ↦ innerSL ℝ (v n)) fun z ↦ by
    simpa only [innerSL_apply_apply, forall_mem_range] using
      (isBounded_iff_forall_norm_le.1
        (Metric.isBounded_range_of_tendsto (fun n ↦ inner ℝ (v n) z) (hv_weak z)))
  have hv_norm (n : ℕ) : ‖v n‖ ≤ D := by
    simpa only [innerSL_apply_norm] using hvD n
  have hdiff : Tendsto (fun n ↦ u n - u_lim) atTop (nhds 0) := by
    simpa only [sub_self] using hu.sub_const u_lim
  have hdiff_norm : Tendsto (fun n ↦ ‖u n - u_lim‖) atTop (nhds 0) :=
    tendsto_zero_iff_norm_tendsto_zero.1 hdiff
  have herr_bound (n : ℕ) :
      |inner ℝ (v n) (u n - u_lim)| ≤ D * ‖u n - u_lim‖ :=
    (abs_real_inner_le_norm _ _).trans
      (mul_le_mul_of_nonneg_right (hv_norm n) (norm_nonneg _))
  have herr_abs : Tendsto (fun n ↦ |inner ℝ (v n) (u n - u_lim)|) atTop
      (nhds 0) := by
    apply squeeze_zero (fun n ↦ abs_nonneg _) herr_bound
    simpa only [mul_zero] using hdiff_norm.const_mul D
  have herr : Tendsto (fun n ↦ inner ℝ (v n) (u n - u_lim)) atTop
      (nhds 0) :=
    (tendsto_zero_iff_abs_tendsto_zero _).2 herr_abs
  change Tendsto (fun n ↦ inner ℝ (v n) (u n)) atTop
    (nhds (inner ℝ v_lim u_lim))
  rw [show (fun n ↦ inner ℝ (v n) (u n)) =
      (fun n ↦ inner ℝ (v n) u_lim + inner ℝ (v n) (u n - u_lim)) by
    funext n
    rw [inner_sub_right]
    ring]
  simpa only [add_zero] using (hv_weak u_lim).add herr

end DifferentialGeometry.Analysis.Parabolic.TimeSobolev

end
