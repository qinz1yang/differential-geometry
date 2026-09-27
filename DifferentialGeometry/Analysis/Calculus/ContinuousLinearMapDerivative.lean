import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv

open Filter Set
open scoped Topology

namespace ContinuousLinearMap

variable {X Y S : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem norm_sub_le_of_hasDerivAt_of_denseRange
    {e : S → X} (he : DenseRange e) {A B : ℝ → X →L[ℝ] Y}
    {J : Set ℝ} (hJ : Convex ℝ J) {C : ℝ} (hC : 0 ≤ C)
    (hd : ∀ t ∈ J, ∀ v, HasDerivAt (fun s => A s (e v)) (B t (e v)) t)
    (hb : ∀ t ∈ J, ‖B t‖ ≤ C) {s t : ℝ} (hs : s ∈ J) (ht : t ∈ J) :
    ‖A t - A s‖ ≤ C * ‖t - s‖ := by
  apply opNorm_le_bound _ (mul_nonneg hC (norm_nonneg _))
  intro x
  refine he.induction_on x
    (isClosed_le (A t - A s).continuous.norm (continuous_const.mul continuous_norm)) ?_
  intro v
  have hd' (r : ℝ) (hr : r ∈ J) := (hd r hr v).hasDerivWithinAt (s := J)
  have hb' (r : ℝ) (hr : r ∈ J) : ‖B r (e v)‖ ≤ C * ‖e v‖ :=
    (B r).le_opNorm (e v) |>.trans (mul_le_mul_of_nonneg_right (hb r hr) (norm_nonneg _))
  have h := hJ.norm_image_sub_le_of_norm_hasDerivWithin_le hd' hb' hs ht
  simpa only [sub_apply, mul_right_comm] using h

theorem hasDerivAt_of_hasDerivAt_apply_of_denseRange
    {e : S → X} (he : DenseRange e) {A B : ℝ → X →L[ℝ] Y} {t : ℝ}
    (hB : ContinuousAt B t)
    (hd : ∀ᶠ s in 𝓝 t, ∀ v, HasDerivAt (fun r => A r (e v)) (B s (e v)) s) :
    HasDerivAt A (B t) t := by
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hg : ∀ᶠ s in 𝓝 t, dist (B s) (B t) < ε :=
    hB.tendsto.eventually (Metric.ball_mem_nhds (B t) hε)
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp (hd.and hg)
  filter_upwards [Metric.ball_mem_nhds t hδ] with s hs
  apply opNorm_le_bound _ (mul_nonneg hε.le (norm_nonneg _))
  intro x
  refine he.induction_on x
    (isClosed_le (A s - A t - (s - t) • B t).continuous.norm
      (continuous_const.mul continuous_norm)) ?_
  intro v
  have hder (r : ℝ) (hr : r ∈ Metric.ball t δ) :
      HasDerivWithinAt (fun r => A r (e v) - (r - t) • B t (e v))
        ((B r - B t) (e v)) (Metric.ball t δ) r := by
    simpa only [one_smul, sub_apply, id_eq] using
      ((hb hr).1 v |>.fun_sub
        (((hasDerivAt_id r).sub_const t).smul_const (B t (e v)))).hasDerivWithinAt
  have hbound (r : ℝ) (hr : r ∈ Metric.ball t δ) :
      ‖(B r - B t) (e v)‖ ≤ ε * ‖e v‖ := by
    exact ((B r - B t).le_opNorm _).trans
      (mul_le_mul_of_nonneg_right (by simpa only [dist_eq_norm] using (hb hr).2.le)
        (norm_nonneg _))
  have h := (convex_ball t δ).norm_image_sub_le_of_norm_hasDerivWithin_le
    hder hbound (Metric.mem_ball_self hδ) hs
  simpa only [sub_self, zero_smul, sub_zero, sub_apply, smul_apply,
    sub_right_comm, mul_right_comm] using h

theorem continuousAt_of_hasDerivAt_apply_of_denseRange
    {e : S → X} (he : DenseRange e) {A B : ℝ → X →L[ℝ] Y} {t : ℝ}
    {r C : ℝ} (hr : 0 < r) (hC : 0 ≤ C)
    (hd : ∀ s ∈ Metric.ball t r, ∀ v,
      HasDerivAt (fun z => A z (e v)) (B s (e v)) s)
    (hb : ∀ s ∈ Metric.ball t r, ‖B s‖ ≤ C) : ContinuousAt A t := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨min r (ε / (C + 1)), lt_min hr (div_pos hε (by linarith)), ?_⟩
  intro s hs
  have hsball : s ∈ Metric.ball t r := lt_of_lt_of_le hs (min_le_left _ _)
  have hn := norm_sub_le_of_hasDerivAt_of_denseRange he (convex_ball t r) hC
    hd hb (Metric.mem_ball_self hr) hsball
  rw [dist_eq_norm]
  refine hn.trans_lt ?_
  have hsε : ‖s - t‖ < ε / (C + 1) := by
    rw [← dist_eq_norm]
    exact lt_of_lt_of_le hs (min_le_right _ _)
  have he : (C + 1) * ‖s - t‖ < ε := by
    simpa only [mul_comm] using (lt_div_iff₀ (by linarith : 0 < C + 1)).mp hsε
  nlinarith [norm_nonneg (s - t)]

end ContinuousLinearMap
