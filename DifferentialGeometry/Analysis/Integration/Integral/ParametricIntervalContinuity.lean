import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Topology.Compactness.LocallyCompact

set_option autoImplicit false

open Filter MeasureTheory Set
open scoped Topology Interval

namespace intervalIntegral

variable {X F : Type*} [TopologicalSpace X] [LocallyCompactSpace X] [FirstCountableTopology X]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem continuousOn_integral_of_continuousOn_prod
    {f : X × ℝ → F} {V : Set X} {a b : ℝ}
    (hV : IsOpen V) (hf : ContinuousOn f (V ×ˢ [[a, b]])) :
    ContinuousOn (fun x => ∫ s in a..b, f (x, s)) V := by
  intro x hx
  obtain ⟨W, hWc, hxW, hWV⟩ := exists_compact_subset hV hx
  have hWnhds : W ∈ 𝓝 x := mem_interior_iff_mem_nhds.mp hxW
  have hcompact := hWc.prod (isCompact_uIcc (a := a) (b := b))
  obtain ⟨C, hC⟩ := hcompact.exists_bound_of_continuousOn
    (hf.mono (prod_mono hWV subset_rfl))
  have hcont : ContinuousAt (fun x => ∫ s in a..b, f (x, s)) x := by
    refine continuousAt_of_dominated_interval (bound := fun _ => C)
      ?_ ?_ intervalIntegrable_const ?_
    · filter_upwards [hV.mem_nhds hx] with y hy
      have hs : ContinuousOn (fun s => f (y, s)) (Ι a b) :=
        hf.comp (continuous_const.prodMk continuous_id).continuousOn
          (fun s hs => ⟨hy, uIoc_subset_uIcc hs⟩)
      exact hs.aestronglyMeasurable measurableSet_uIoc
    · filter_upwards [hWnhds] with y hy
      exact ae_of_all _ (fun s hs => hC (y, s) ⟨hy, uIoc_subset_uIcc hs⟩)
    · refine ae_of_all _ (fun s hs => ?_)
      have hp : ContinuousOn (fun y => f (y, s)) V :=
        hf.comp (continuous_id.prodMk continuous_const).continuousOn
          (fun y hy => ⟨hy, uIoc_subset_uIcc hs⟩)
      exact (hp x hx).continuousAt (hV.mem_nhds hx)
  exact hcont.continuousWithinAt

end intervalIntegral
