import DifferentialGeometry.Topology.Manifold.ConnectedInterior
import DifferentialGeometry.Topology.Manifold.SmoothBoundaryAtlas.Inclusion
import DifferentialGeometry.Topology.Connected.RegularClosedComponents

open Set
open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.SmoothBoundaryAtlas

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]
  {n : ℕ} [NeZero n] {K : Set M} (C : SmoothBoundaryAtlas I n K)

theorem ambientChart_eq_zero_iff_mem_frontier (x : K) :
    C.ambientChart x x.val 0 = 0 ↔ x.val ∈ frontier K := by
  have h : (C.ambientChart x).toOpenPartialHomeomorph.IsImage K
      {v : EuclideanSpace ℝ (Fin n) | 0 ≤ v 0} := by
    intro y hy
    exact (C.mem_iff x y hy).symm
  have hf := h.frontier (C.mem_source x)
  rw [frontier_halfSpace] at hf
  change (0 = C.ambientChart x x.val 0 ↔ x.val ∈ frontier K) at hf
  exact eq_comm.trans hf

include C in
theorem isPreconnected_interior_connectedComponentIn
    (x : M) : IsPreconnected (interior (connectedComponentIn K x)) := by
  by_cases hx : x ∈ K
  · let _ := C.toChartedSpace
    let _ := C.isManifold
    let _ : LocallyConnectedSpace K :=
      ChartedSpace.locallyConnectedSpace (EuclideanHalfSpace n) K
    have h := (Manifold.isPreconnected_manifold_interior_inter_connectedComponent
      (I := 𝓡∂ n) (⟨x, hx⟩ : K)).image Subtype.val continuous_subtype_val.continuousOn
    have heq : Subtype.val '' ((𝓡∂ n).interior K ∩ connectedComponent (⟨x, hx⟩ : K)) =
        interior (connectedComponentIn K x) := by
      rw [interior_connectedComponentIn_eq_inter, connectedComponentIn_eq_image hx,
        ← C.image_interior_subtype_val C.ambientChart_eq_zero_iff_mem_frontier,
        image_inter Subtype.val_injective]
    exact heq ▸ h
  · rw [connectedComponentIn_eq_empty hx, interior_empty]
    exact isPreconnected_empty
include C in
theorem connectedComponentIn_interior_eq_interior_connectedComponentIn
    {x : M} (hx : x ∈ interior K) :
    connectedComponentIn (interior K) x = interior (connectedComponentIn K x) := by
  let _ := C.toChartedSpace
  let _ := C.isManifold
  let _ : LocallyConnectedSpace K :=
    ChartedSpace.locallyConnectedSpace (EuclideanHalfSpace n) K
  apply Subset.antisymm
  · rw [interior_connectedComponentIn_eq_inter]
    exact subset_inter (connectedComponentIn_subset (interior K) x)
      (connectedComponentIn_mono x interior_subset)
  · apply (C.isPreconnected_interior_connectedComponentIn x).subset_connectedComponentIn
    · rw [interior_connectedComponentIn_eq_inter]
      exact ⟨hx, mem_connectedComponentIn (interior_subset hx)⟩
    · exact interior_mono (connectedComponentIn_subset K x)

end DifferentialGeometry.Topology.SmoothBoundaryAtlas
