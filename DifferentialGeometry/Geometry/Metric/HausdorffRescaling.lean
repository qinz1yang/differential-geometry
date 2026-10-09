import Mathlib.Analysis.Normed.Module.Ball.Pointwise

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped Pointwise ENNReal

namespace GC.MetricGeometry

theorem hausdorffEDist_smul₀
    {𝕜 E : Type*} [NormedDivisionRing 𝕜] [SeminormedAddCommGroup E]
    [Module 𝕜 E] [NormSMulClass 𝕜 E]
    {c : 𝕜} (hc : c ≠ 0) (s t : Set E) :
    hausdorffEDist (c • s) (c • t) = (‖c‖₊ : ℝ≥0∞) * hausdorffEDist s t := by
  rw [hausdorffEDist_def, hausdorffEDist_def]
  change (⨆ x ∈ (fun x : E => c • x) '' s, infEDist x (c • t)) ⊔
      (⨆ y ∈ (fun y : E => c • y) '' t, infEDist y (c • s)) = _
  simp only [iSup_image, infEDist_smul₀ hc, ENNReal.smul_def, smul_eq_mul,
    ENNReal.mul_iSup, mul_max]

variable {H : Type*} [SeminormedAddCommGroup H] [NormedSpace ℝ H]

theorem hausdorffEDist_rescaled_image
    (o : H) {r : ℝ} (hr : 0 < r) (s t : Set H) :
    hausdorffEDist ((fun x => r⁻¹ • (x - o)) '' s)
        ((fun x => r⁻¹ • (x - o)) '' t) =
      ENNReal.ofReal r⁻¹ * hausdorffEDist s t := by
  have htrans : Isometry (fun x : H => x - o) := by
    intro x y
    simp only [edist_dist, dist_eq_norm, sub_sub_sub_cancel_right]
  have himage (u : Set H) : (fun x => r⁻¹ • (x - o)) '' u =
      r⁻¹ • ((fun x => x - o) '' u) := by
    rw [← image_smul, image_image]
  rw [himage, himage, hausdorffEDist_smul₀ (inv_ne_zero hr.ne'),
    hausdorffEDist_image htrans]
  have hc : (‖r⁻¹‖₊ : ℝ≥0∞) = ENNReal.ofReal r⁻¹ := by
    rw [← ENNReal.ofReal_coe_nnreal]
    simp only [coe_nnnorm, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr)]
  rw [hc]

theorem hausdorffEDist_rescaled_ball
    (o : H) {r : ℝ} (hr : 0 < r) (b : ℝ) (s t : Set H) :
    hausdorffEDist (((fun x => r⁻¹ • (x - o)) '' s) ∩ ball 0 b)
        (((fun x => r⁻¹ • (x - o)) '' t) ∩ ball 0 b) =
      ENNReal.ofReal r⁻¹ * hausdorffEDist (s ∩ ball o (r * b))
        (t ∩ ball o (r * b)) := by
  have hpre : (fun x : H => r⁻¹ • (x - o)) ⁻¹' ball 0 b = ball o (r * b) := by
    ext x
    simp only [mem_preimage, mem_ball, dist_eq_norm, sub_zero, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), inv_mul_lt_iff₀ hr]
  rw [← image_inter_preimage, ← image_inter_preimage, hpre]
  exact hausdorffEDist_rescaled_image o hr _ _

theorem hausdorffEDist_rescaled_closedBall
    (o : H) {r : ℝ} (hr : 0 < r) (b : ℝ) (s t : Set H) :
    hausdorffEDist (((fun x => r⁻¹ • (x - o)) '' s) ∩ closedBall 0 b)
        (((fun x => r⁻¹ • (x - o)) '' t) ∩ closedBall 0 b) =
      ENNReal.ofReal r⁻¹ * hausdorffEDist (s ∩ closedBall o (r * b))
        (t ∩ closedBall o (r * b)) := by
  have hpre : (fun x : H => r⁻¹ • (x - o)) ⁻¹' closedBall 0 b =
      closedBall o (r * b) := by
    ext x
    simp only [mem_preimage, mem_closedBall, dist_eq_norm, sub_zero, norm_smul,
      Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), inv_mul_le_iff₀ hr]
  rw [← image_inter_preimage, ← image_inter_preimage, hpre]
  exact hausdorffEDist_rescaled_image o hr _ _

end GC.MetricGeometry
