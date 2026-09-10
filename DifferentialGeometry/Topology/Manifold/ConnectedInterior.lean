import DifferentialGeometry.Topology.Connected.Dense
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Analysis.Convex.PathConnected

open Set Filter Topology
open scoped Manifold ContDiff

namespace Poincare.Topology.Manifold

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]

theorem dense_manifold_interior : Dense (I.interior M) := by
  intro x
  let c := extChartAt I x
  have hx : c x ∈ closure (interior c.target) :=
    extChartAt_target_subset_closure_interior (mem_extChartAt_target (I := I) x)
  have hclosure := mem_closure_image (continuousAt_extChartAt_symm (I := I) x) hx
  have hsub : c.symm '' interior c.target ⊆ I.interior M := by
    rintro y ⟨z, hz, rfl⟩
    have hz' : z ∈ c.target := interior_subset hz
    have hs : c.symm z ∈ (chartAt H x).source := by
      simpa only [c, extChartAt_source] using c.map_target hz'
    apply (I.isInteriorPoint_iff_of_mem_atlas (by decide : (1 : ℕ∞ω) ≠ 0)
      (chart_mem_atlas H x) hs).mpr
    change c (c.symm z) ∈ interior c.target
    rwa [c.right_inv hz']
  have h := closure_mono hsub hclosure
  simpa only [c, PartialEquiv.left_inv _ (mem_extChartAt_source x)] using h

theorem isPreconnected_manifold_interior [PreconnectedSpace M] :
    IsPreconnected (I.interior M) := by
  apply Poincare.Topology.isPreconnected_of_dense_of_locally_preconnected_inter
    dense_manifold_interior
  intro x
  let c := extChartAt I x
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhdsWithin_iff.mp
    (extChartAt_target_mem_nhdsWithin (I := I) x)
  let V := c.source ∩ c ⁻¹' Metric.ball (c x) r
  have hV : V ∈ 𝓝 x := inter_mem (extChartAt_source_mem_nhds (I := I) x)
    ((continuousAt_extChartAt (I := I) x).preimage_mem_nhds (Metric.ball_mem_nhds _ hr))
  refine ⟨V, hV, ?_⟩
  have htarget : Metric.ball (c x) r ∩ interior (range I) ⊆ c.target := by
    intro z hz
    exact hball ⟨hz.1, interior_subset hz.2⟩
  have heq : V ∩ I.interior M = c.symm '' (Metric.ball (c x) r ∩ interior (range I)) := by
    ext y
    constructor
    · rintro ⟨⟨hy, hyball⟩, hyint⟩
      refine ⟨c y, ⟨hyball, ?_⟩, c.left_inv hy⟩
      have hi := (I.isInteriorPoint_iff_of_mem_atlas (by decide : (1 : ℕ∞ω) ≠ 0)
        (chart_mem_atlas H x) (by simpa only [c, extChartAt_source] using hy)).mp hyint
      exact interior_mono (extChartAt_target_subset_range x) hi
    · rintro ⟨z, hz, rfl⟩
      have ht := htarget hz
      have hs := c.map_target ht
      refine ⟨⟨hs, ?_⟩, ?_⟩
      · change c (c.symm z) ∈ Metric.ball (c x) r
        rw [c.right_inv ht]
        exact hz.1
      · apply (I.isInteriorPoint_iff_of_mem_atlas (by decide : (1 : ℕ∞ω) ≠ 0)
          (chart_mem_atlas H x) (by simpa only [c, extChartAt_source] using hs)).mpr
        change c (c.symm z) ∈ interior c.target
        rw [c.right_inv ht]
        exact (extChartAt_target_eventuallyEq_of_mem ht).symm.mem_interior hz.2
  rw [heq]
  exact ((convex_ball (c x) r).inter I.convex_range.interior).isPreconnected.image c.symm
    ((continuousOn_extChartAt_symm (I := I) x).mono htarget)

end Poincare.Topology.Manifold
