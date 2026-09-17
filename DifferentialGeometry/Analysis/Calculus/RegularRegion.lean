import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Topology.NhdsWithin

open Set
open scoped Topology

namespace DifferentialGeometry.Analysis

theorem interior_frontier_iff_of_local_regular_superlevel
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {D N : Set E} {H : E → ℝ} (hD : IsClosed D) (hN : IsOpen N)
    (hH : Continuous H) (hreg : ∀ p ∈ N, H p = 0 → fderiv ℝ H p ≠ 0)
    (heq : ∀ p ∈ N, p ∈ D ↔ 0 ≤ H p) :
    ∀ p ∈ N, (p ∈ interior D ↔ 0 < H p) ∧
      (p ∈ frontier D ↔ H p = 0) := by
  intro p hp
  have hi : p ∈ interior D ↔ 0 < H p := by
    constructor
    · intro hi
      have hle : 0 ≤ H p := (heq p hp).mp (interior_subset hi)
      by_contra hn
      have hz : H p = 0 := le_antisymm (le_of_not_gt hn) hle
      have hmin : IsLocalMin H p := by
        filter_upwards [hN.mem_nhds hp, mem_interior_iff_mem_nhds.mp hi] with q hqN hqD
        change H p ≤ H q
        rw [hz]
        exact (heq q hqN).mp hqD
      exact hreg p hp hz hmin.fderiv_eq_zero
    · intro hpos
      apply interior_mono (s := N ∩ {q | 0 < H q}) (t := D)
        (fun q hq => (heq q hq.1).mpr hq.2.le)
      rw [(hN.inter (isOpen_lt continuous_const hH)).interior_eq]
      exact ⟨hp, hpos⟩
  refine ⟨hi, ?_⟩
  rw [hD.frontier_eq]
  change (p ∈ D ∧ p ∉ interior D) ↔ H p = 0
  rw [heq p hp, hi, not_lt]
  exact ⟨fun h => le_antisymm h.2 h.1, fun h => ⟨h.ge, h.le⟩⟩

end DifferentialGeometry.Analysis
