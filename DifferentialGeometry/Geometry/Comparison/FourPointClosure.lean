import DifferentialGeometry.Geometry.Comparison.FourPoint
import Mathlib.Topology.Sequences

set_option autoImplicit false

open Set Filter Topology

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem fourPointComparison.closure_zero {X : Type*} [MetricSpace X] {s : Set X}
    (h : fourPointComparison 0 s) : fourPointComparison 0 (closure s) := by
  intro x hx a ha b hb c hc hax hbx hcx
  obtain ⟨x', hx', hxt⟩ := mem_closure_iff_seq_limit.mp hx
  obtain ⟨a', ha', hat⟩ := mem_closure_iff_seq_limit.mp ha
  obtain ⟨b', hb', hbt⟩ := mem_closure_iff_seq_limit.mp hb
  obtain ⟨c', hc', hct⟩ := mem_closure_iff_seq_limit.mp hc
  have hxa := dist_pos.mpr hax.symm
  have hxb := dist_pos.mpr hbx.symm
  have hxc := dist_pos.mpr hcx.symm
  have hsource : ∀ᶠ i in atTop,
      comparisonAngleNegCurvature 0 (dist (x' i) (a' i)) (dist (x' i) (b' i))
          (dist (a' i) (b' i)) +
        comparisonAngleNegCurvature 0 (dist (x' i) (b' i)) (dist (x' i) (c' i))
          (dist (b' i) (c' i)) +
        comparisonAngleNegCurvature 0 (dist (x' i) (c' i)) (dist (x' i) (a' i))
          (dist (c' i) (a' i)) ≤ 2 * Real.pi := by
    filter_upwards [(hxt.dist hat).eventually (Ioi_mem_nhds hxa),
      (hxt.dist hbt).eventually (Ioi_mem_nhds hxb),
      (hxt.dist hct).eventually (Ioi_mem_nhds hxc)] with i hi1 hi2 hi3
    exact h (x' i) (hx' i) (a' i) (ha' i) (b' i) (hb' i) (c' i) (hc' i)
      (dist_pos.mp hi1).symm (dist_pos.mp hi2).symm (dist_pos.mp hi3).symm
  have hang12 := tendsto_comparisonAngleNegCurvature_zero tendsto_const_nhds
    (hxt.dist hat) (hxt.dist hbt) (hat.dist hbt)
    (Eventually.of_forall fun _ => le_refl (0 : ℝ)) hxa hxb
  have hang23 := tendsto_comparisonAngleNegCurvature_zero tendsto_const_nhds
    (hxt.dist hbt) (hxt.dist hct) (hbt.dist hct)
    (Eventually.of_forall fun _ => le_refl (0 : ℝ)) hxb hxc
  have hang31 := tendsto_comparisonAngleNegCurvature_zero tendsto_const_nhds
    (hxt.dist hct) (hxt.dist hat) (hct.dist hat)
    (Eventually.of_forall fun _ => le_refl (0 : ℝ)) hxc hxa
  simpa only [comparisonAngleNegCurvature_zero] using
    le_of_tendsto ((hang12.add hang23).add hang31) hsource

end DifferentialGeometry.Geometry.Comparison.Toponogov
