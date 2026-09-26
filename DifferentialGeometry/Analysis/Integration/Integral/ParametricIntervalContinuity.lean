import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.UniformSpace.HeineCantor

open Filter MeasureTheory Set
open scoped Topology Interval

namespace intervalIntegral

variable {X F : Type*} [TopologicalSpace X] [FirstCountableTopology X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem continuousOn_integral_of_continuousOn_prod
    {f : X × ℝ → F} {V : Set X} {a b : ℝ}
    (hV : IsOpen V) (hf : ContinuousOn f (V ×ˢ [[a, b]])) :
    ContinuousOn (fun x => ∫ s in a..b, f (x, s)) V := by
  intro x hx
  have hcenter : ContinuousOn (fun s => f (x, s)) [[a, b]] :=
    hf.comp (continuous_const.prodMk continuous_id).continuousOn (fun s hs => ⟨hx, hs⟩)
  obtain ⟨C, hC⟩ := isCompact_uIcc.exists_bound_of_continuousOn hcenter
  obtain ⟨W, hW, hnear⟩ := isCompact_uIcc.mem_uniformity_of_prod
    (f := fun x s => f (x, s)) hf hx (Metric.dist_mem_uniformity (by norm_num : (0 : ℝ) < 1))
  have hWnhds : W ∈ 𝓝 x := by simpa only [hV.nhdsWithin_eq hx] using hW
  have hcont : ContinuousAt (fun x => ∫ s in a..b, f (x, s)) x := by
    refine continuousAt_of_dominated_interval (bound := fun _ => C + 1)
      ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [hV.mem_nhds hx] with y hy
      have hs : ContinuousOn (fun s => f (y, s)) (Ι a b) :=
        hf.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun s hs => ⟨hy, uIoc_subset_uIcc hs⟩)
      exact hs.aestronglyMeasurable measurableSet_uIoc
    · filter_upwards [hWnhds] with y hy
      apply ae_of_all
      intro t ht
      have hh := hnear y hy t (uIoc_subset_uIcc ht)
      have hc := hC t (uIoc_subset_uIcc ht)
      have hn : ‖f (y, t)‖ ≤ ‖f (y, t) - f (x, t)‖ + ‖f (x, t)‖ := norm_le_norm_sub_add _ _
      change dist (f (y, t)) (f (x, t)) < 1 at hh
      rw [dist_eq_norm] at hh
      linarith
    · refine ae_of_all _ (fun s hs => ?_)
      have hp : ContinuousOn (fun y => f (y, s)) V :=
        hf.comp (continuous_id.prodMk continuous_const).continuousOn
          (fun y hy => ⟨hy, uIoc_subset_uIcc hs⟩)
      exact (hp x hx).continuousAt (hV.mem_nhds hx)
  exact hcont.continuousWithinAt

end intervalIntegral
