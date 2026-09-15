import Mathlib.Analysis.LocallyConvex.Separation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Connected.Clopen

open Set Topology Metric

namespace DifferentialGeometry.Analysis

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]

theorem IsCompact.subset_of_frontier_subset_convex_open {C W : Set E}
    (hC : IsCompact C) (hW : Convex ℝ W) (hWo : IsOpen W) (hCW : frontier C ⊆ W) : C ⊆ W := by
  intro x hx
  by_contra hxW
  obtain ⟨z, hz⟩ := nonempty_frontier_iff.mpr ⟨⟨x, hx⟩, hC.ne_univ⟩
  obtain ⟨f, hf⟩ := geometric_hahn_banach_open_point hW hWo hxW
  have hzW := hCW hz
  have hpos : 0 < f x - f z := sub_pos.mpr (hf z hzW)
  obtain ⟨y, hyC, hmax⟩ := hC.exists_isMaxOn ⟨x, hx⟩ f.continuous.continuousOn
  have hybd : y ∈ frontier C := by
    refine ⟨subset_closure hyC, ?_⟩
    intro hyint
    have hcont : Continuous (fun t : ℝ => y + t • (x - z)) :=
      continuous_const.add (continuous_id.smul continuous_const)
    have hnear : (fun t : ℝ => y + t • (x - z)) ⁻¹' C ∈ 𝓝 (0 : ℝ) := by
      apply hcont.continuousAt.preimage_mem_nhds
      simpa only [zero_smul, add_zero] using mem_interior_iff_mem_nhds.mp hyint
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
    have hy' : y + (δ / 2) • (x - z) ∈ C := hball (by
      rw [mem_ball, Real.dist_eq, sub_zero, abs_of_pos (half_pos hδ)]
      linarith)
    have hle : f (y + (δ / 2) • (x - z)) ≤ f y := hmax hy'
    have hcalc : f (y + (δ / 2) • (x - z)) = f y + (δ / 2) * (f x - f z) := by
      simp only [map_add, map_smul, map_sub, smul_eq_mul]
    rw [hcalc] at hle
    have hmul := mul_pos (half_pos hδ) hpos
    linarith
  exact (not_lt_of_ge (hmax hx)) (hf y (hCW hybd))

end DifferentialGeometry.Analysis
