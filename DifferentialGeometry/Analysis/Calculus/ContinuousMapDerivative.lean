import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Topology.ContinuousMap.Compact

open Filter Set
open scoped Topology

namespace ContinuousMap

variable {K F : Type*} [TopologicalSpace K] [CompactSpace K]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasDerivAt_of_hasDerivAt_apply {f f' : ℝ → C(K, F)} {t : ℝ}
    (hf' : ContinuousAt f' t)
    (hf : ∀ᶠ s in 𝓝 t, ∀ x, HasDerivAt (fun r => f r x) (f' s x) s) :
    HasDerivAt f (f' t) t := by
  rw [hasDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  have hg : ∀ᶠ s in 𝓝 t, dist (f' s) (f' t) < ε :=
    hf'.tendsto.eventually (Metric.ball_mem_nhds (f' t) hε)
  obtain ⟨δ, hδ, hb⟩ := Metric.eventually_nhds_iff.mp (hf.and hg)
  filter_upwards [Metric.ball_mem_nhds t hδ] with s hs
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).mpr
  intro x
  have hder (r : ℝ) (hr : r ∈ Metric.ball t δ) :
      HasDerivWithinAt (fun r => f r x - (r - t) • f' t x)
        (f' r x - f' t x) (Metric.ball t δ) r := by
    simpa only [one_smul, Pi.sub_apply, id_eq] using
      ((hb hr).1 x |>.fun_sub (((hasDerivAt_id r).sub_const t).smul_const (f' t x))).hasDerivWithinAt
  have hbound (r : ℝ) (hr : r ∈ Metric.ball t δ) : ‖f' r x - f' t x‖ ≤ ε := by
    calc
      ‖f' r x - f' t x‖ ≤ ‖f' r - f' t‖ := norm_coe_le_norm (f' r - f' t) x
      _ ≤ ε := by simpa only [dist_eq_norm] using (hb hr).2.le
  have h := (convex_ball t δ).norm_image_sub_le_of_norm_hasDerivWithin_le
    hder hbound (Metric.mem_ball_self hδ) hs
  simpa only [sub_self, zero_smul, sub_zero, coe_sub, coe_smul, Pi.sub_apply,
    Pi.smul_apply, sub_right_comm] using h

theorem contDiffOn_one_of_hasDerivAt_apply {f f' : ℝ → C(K, F)} {J : Set ℝ}
    (hJ : IsOpen J)
    (hf' : ContinuousOn (fun p : ℝ × K => f' p.1 p.2) (J ×ˢ univ))
    (hf : ∀ s ∈ J, ∀ x, HasDerivAt (fun r => f r x) (f' s x) s) :
    ContDiffOn ℝ 1 f J := by
  have hg : ContinuousOn f' J := continuousOn_of_continuousOn_uncurry f' hf'
  have hd (s : ℝ) (hs : s ∈ J) : HasDerivAt f (f' s) s :=
    hasDerivAt_of_hasDerivAt_apply (hg.continuousAt (hJ.mem_nhds hs))
      (Filter.eventually_of_mem (hJ.mem_nhds hs) fun r hr => hf r hr)
  rw [contDiffOn_one_iff_derivWithin hJ.uniqueDiffOn]
  refine ⟨fun s hs => (hd s hs).differentiableAt.differentiableWithinAt, ?_⟩
  exact hg.congr fun s hs => ((hd s hs).hasDerivWithinAt.derivWithin
    (hJ.uniqueDiffWithinAt hs))

end ContinuousMap
