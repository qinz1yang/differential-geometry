import Mathlib.Dynamics.Flow
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Instances.Real.Lemmas

open Set Metric

namespace DifferentialGeometry.Topology.Flow

theorem isForwardInvariant_of_frontier
    {X : Type*} [TopologicalSpace X] (φ : _root_.Flow ℝ X)
    {K : Set X} (hK : IsClosed K)
    (hboundary : ∀ x ∈ frontier K, ∃ ε > 0, ∀ t ∈ Icc 0 ε, φ t x ∈ K) :
    IsForwardInvariant φ K := by
  have hlocal (x : X) (hx : x ∈ K) :
      ∃ ε > 0, ∀ t ∈ Icc 0 ε, φ t x ∈ K := by
    by_cases hfr : x ∈ frontier K
    · exact hboundary x hfr
    have hi : x ∈ interior K := (mem_interior_iff_notMem_frontier hx).mpr hfr
    have hnear : (fun t ↦ φ t x) ⁻¹' K ∈ nhds (0 : ℝ) :=
      (φ.continuous continuous_id continuous_const).continuousAt.preimage_mem_nhds
        (by simpa only [id_eq, φ.map_zero_apply] using mem_interior_iff_mem_nhds.mp hi)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hnear
    refine ⟨ε / 2, half_pos hε, fun t ht ↦ hball ?_⟩
    rw [mem_ball, Real.dist_eq, sub_zero, abs_of_nonneg ht.1]
    linarith [ht.2]
  intro t ht x hx
  let S : Set ℝ := {s | φ s x ∈ K}
  have hS : IsClosed S := hK.preimage (φ.continuous continuous_id continuous_const)
  apply (hS.inter isClosed_Icc).mem_of_ge_of_forall_exists_gt
    (a := 0) (b := t) (by simpa only [S, mem_ofPred_eq, φ.map_zero_apply] using hx) ht
  intro s hs
  obtain ⟨ε, hε, hstay⟩ := hlocal (φ s x) hs.1
  let δ := min ε (t - s) / 2
  have hδ : 0 < δ := half_pos (lt_min hε (sub_pos.mpr hs.2.2))
  have hδε : δ ≤ ε := by dsimp [δ]; linarith [min_le_left ε (t - s)]
  have hδt : δ ≤ t - s := by dsimp [δ]; linarith [min_le_right ε (t - s), hs.2.2]
  refine ⟨δ + s, ?_, by linarith, by linarith⟩
  change φ (δ + s) x ∈ K
  rw [φ.map_add]
  exact hstay δ ⟨hδ.le, hδε⟩

end DifferentialGeometry.Topology.Flow
