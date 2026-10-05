import DifferentialGeometry.Topology.ThreeManifold.GraphManifold.Closure.Inhabitants.LoopRegion

/-!
The actual circle region meets the deep core in precisely its whole torus face.
This genuine frontier identification proves disjoint ambient interiors.
-/

set_option autoImplicit false
noncomputable section
open Set Function Metric Manifold DifferentialGeometry DifferentialGeometry.Topology GC.Endpoint
open GC.GraphManifold
open scoped Manifold ContDiff Topology
namespace GC.GraphManifold.Assembly

theorem loopCircleRegion_core_inter :
    loopCircleRegion ∩ Set.range loopComplementVertex.map = loopComplementFace := by
  ext p
  rw [loopComplementFace_height]
  constructor
  · rintro ⟨hr, hc⟩
    rw [loopCircleRegion_shell_fills] at hr
    rcases hr with hs | hf
    · rw [loopComplementVertex_range] at hc
      exact le_antisymm hs.2 hc
    · obtain ⟨b, q, hq, rfl⟩ := mem_iUnion.mp hf
      have hsource : q ∈ (standardLoopBallHandleCycle.rimChart
          ⟨0, standardLoopBallHandleCycle.len_pos⟩ b).source :=
        (standardLoopBallHandleCycle.rim_source _ b).mpr (loopCornerFill_source hq.2)
      exact False.elim (Set.disjoint_left.mp (loopRim_core_disjoint b)
        ((standardLoopBallHandleCycle.rimChart
          ⟨0, standardLoopBallHandleCycle.len_pos⟩ b).map_source hsource) hc)
  · intro hp
    constructor
    · rw [loopCircleRegion_shell_fills]
      left
      change 0 ≤ cliffordHeight p ∧ cliffordHeight p ≤ 3 / 4
      rw [hp]
      norm_num
    · rw [loopComplementVertex_range]
      exact hp.ge

theorem loopCircleRegion_core_disjoint :
    Disjoint (interior loopCircleRegion) (interior (Set.range loopComplementVertex.map)) := by
  apply Set.disjoint_left.mpr
  intro p hr hc
  have hf : p ∈ loopComplementFace := by
    rw [← loopCircleRegion_core_inter]
    exact ⟨interior_subset hr, interior_subset hc⟩
  rw [loopComplementFace_frontier] at hf
  exact hf.2 hc

end GC.GraphManifold.Assembly
