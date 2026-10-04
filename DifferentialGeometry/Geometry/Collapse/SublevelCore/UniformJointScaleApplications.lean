import DifferentialGeometry.Geometry.Collapse.SublevelCore.UniformJointScale
import Mathlib.Topology.MetricSpace.Sequences

/-!
# Consumer of the LC58 kernel

A concrete instance of the negate-the-joint-conclusion principle: on a compact metric space every
sequence of points has a convergent subsequence, so for a continuous `f` ONE scale
`R = max T (f x + 1)` eventually dominates `f` along that subsequence. The LC58 kernel then gives
a uniform interval `[T, V]` of admissible scales, hence a uniform upper bound for `f`.
-/

set_option autoImplicit false

open Filter Set Topology

namespace DifferentialGeometry.Geometry.Collapse

/-- **Consumer of the LC58 kernel.** A continuous function on a compact metric space admits, for
every `T`, one `V ≥ T` such that each point has an admissible scale `s ∈ [T, V]` with `f p ≤ s`. -/
theorem exists_uniform_scale_of_continuous_on_compact {K : Type*} [MetricSpace K] [CompactSpace K]
    (f : K → ℝ) (hf : Continuous f) (T : ℝ) :
    ∃ V : ℝ, T ≤ V ∧ ∀ p : K, ∃ s ∈ Icc T V, f p ≤ s := by
  obtain ⟨V, hTV, α₀, hV⟩ := exists_uniform_scale_interval_of_eventual_witnesses
    (X := fun _ => K) (fun _ p s => f p ≤ s) T (by
      intro a _ p
      obtain ⟨x, -, φ, hφ, hlim⟩ := isCompact_univ.tendsto_subseq (x := p) (fun _ => mem_univ _)
      refine ⟨φ, hφ, max T (f x + 1), le_max_left _ _, ?_⟩
      have hev := ((hf.tendsto x).comp hlim).eventually (gt_mem_nhds (lt_add_one (f x)))
      filter_upwards [hev] with j hj
      exact hj.le.trans (le_max_right _ _))
  exact ⟨V, hTV, fun p => hV (α₀ + 1) (Nat.lt_succ_self α₀) p⟩

end DifferentialGeometry.Geometry.Collapse
