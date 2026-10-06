import Mathlib.Analysis.Calculus.MeanValue

noncomputable section

open Filter Set Metric Asymptotics
open scoped Topology

namespace DifferentialGeometry

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private theorem norm_sub_le_of_punctured_hasFDerivAt_bound
    {f : E → F} {D : E → E →L[ℝ] F} {a x : E} {r C : ℝ}
    (hf : ContinuousAt f a) (hC : 0 ≤ C)
    (hD : ∀ y ∈ ball a r, y ≠ a → HasFDerivAt f (D y) y)
    (hbound : ∀ y ∈ ball a r, y ≠ a → ‖D y‖ ≤ C)
    (hx : x ∈ ball a r) : ‖f x - f a‖ ≤ C * ‖x - a‖ := by
  by_cases hxa : x = a
  · simp [hxa]
  let v := x - a
  let p : ℝ → E := fun t => a + t • v
  let g : ℝ → F := fun t => f (p t)
  have hp0 : p 0 = a := by simp [p]
  have hp1 : p 1 = x := by simp [p, v]
  have hp : ∀ t ∈ Ioc (0 : ℝ) 1, p t ∈ ball a r ∧ p t ≠ a := by
    intro t ht
    constructor
    · change dist (a + t • v) a < r
      rw [dist_eq_norm, add_sub_cancel_left, norm_smul, Real.norm_of_nonneg ht.1.le]
      exact (mul_le_of_le_one_left (norm_nonneg v) ht.2).trans_lt (by
        simpa [v, dist_eq_norm] using hx)
    · intro heq
      have hz : t • v = 0 := by simpa [p] using congrArg (fun y => y - a) heq
      exact (smul_ne_zero (ne_of_gt ht.1) (sub_ne_zero.mpr hxa)) hz
  have hgD : ∀ t ∈ Ioc (0 : ℝ) 1, HasDerivAt g (D (p t) v) t := by
    intro t ht
    have hpD : HasDerivAt p v t := by
      simpa [p] using ((hasDerivAt_id t).smul_const v).const_add a
    exact (hD (p t) (hp t ht).1 (hp t ht).2).comp_hasDerivAt t hpD
  have hg_bound : ∀ t ∈ Ioc (0 : ℝ) 1, ‖D (p t) v‖ ≤ C * ‖v‖ := by
    intro t ht
    exact (D (p t)).le_of_opNorm_le (hbound (p t) (hp t ht).1 (hp t ht).2) v
  have hkey : ∀ t ∈ Ioc (0 : ℝ) 1, ‖g 1 - g t‖ ≤ C * ‖v‖ := by
    intro t ht
    have hseg : ∀ s ∈ Icc t 1, HasDerivWithinAt g (D (p s) v) (Icc t 1) s := by
      intro s hs
      exact (hgD s ⟨ht.1.trans_le hs.1, hs.2⟩).hasDerivWithinAt
    have hseg_bound : ∀ s ∈ Ico t 1, ‖D (p s) v‖ ≤ C * ‖v‖ := by
      intro s hs
      exact hg_bound s ⟨ht.1.trans_le hs.1, hs.2.le⟩
    have hmean := norm_image_sub_le_of_norm_deriv_le_segment' hseg hseg_bound
      1 ⟨ht.2, le_rfl⟩
    exact hmean.trans (mul_le_of_le_one_right (mul_nonneg hC (norm_nonneg v))
      (sub_le_self 1 ht.1.le))
  have hg0 : ContinuousAt g 0 := by
    have hpcont : ContinuousAt p 0 := (continuous_const.add
      (continuous_id.smul continuous_const)).continuousAt
    change ContinuousAt (f ∘ p) 0
    apply ContinuousAt.comp (x := 0) _ hpcont
    simpa only [hp0] using hf
  have hzero : (0 : ℝ) ∈ closure (Ioc (0 : ℝ) 1) := by
    rw [closure_Ioc zero_ne_one]
    exact ⟨le_rfl, zero_le_one⟩
  have hlimit := ContinuousWithinAt.closure_le hzero
    (continuousAt_const.sub hg0).norm.continuousWithinAt
    continuousWithinAt_const hkey
  simpa only [Pi.sub_apply, g, hp0, hp1, v] using hlimit

/-- A continuous map with derivatives tending to zero off one point has zero derivative there.
-/
theorem hasFDerivAt_zero_of_punctured_tendsto
    {f : E → F} {D : E → E →L[ℝ] F} {a : E}
    (hD : ∀ᶠ y in 𝓝[≠] a, HasFDerivAt f (D y) y)
    (hf : ContinuousAt f a)
    (hlim : Tendsto D (𝓝[≠] a) (𝓝 0)) : HasFDerivAt f (0 : E →L[ℝ] F) a := by
  rw [hasFDerivAt_iff_isLittleO, isLittleO_iff]
  intro ε hε
  have hsmall : ∀ᶠ y in 𝓝[≠] a, ‖D y‖ < ε := by
    exact hlim.norm.eventually (gt_mem_nhds (by simpa only [norm_zero] using hε))
  obtain ⟨r, hr, hball⟩ : ∃ r > 0,
      ball a r ∩ {a}ᶜ ⊆ {y | HasFDerivAt f (D y) y ∧ ‖D y‖ < ε} :=
    mem_nhdsWithin_iff.1 (hD.and hsmall)
  refine Metric.eventually_nhds_iff_ball.mpr ⟨r, hr, ?_⟩
  intro x hx
  have hest := norm_sub_le_of_punctured_hasFDerivAt_bound hf hε.le
    (fun y hy hne => (hball ⟨hy, hne⟩).1)
    (fun y hy hne => (hball ⟨hy, hne⟩).2.le) hx
  simpa only [zero_apply, sub_zero] using hest

end DifferentialGeometry
