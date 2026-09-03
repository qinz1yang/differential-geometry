import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Separation.Basic

set_option autoImplicit false

noncomputable section

open Set

namespace DifferentialGeometry

theorem exists_isOpen_isConnected_isCompact_closure
    {X : Type*} [TopologicalSpace X] [T2Space X]
    [LocallyCompactSpace X] [LocallyPathConnectedSpace X] [ConnectedSpace X]
    (x y : X) :
    ∃ U : Set X,
      IsOpen U ∧ IsConnected U ∧ x ∈ U ∧ y ∈ U ∧ IsCompact (closure U) := by
  let gamma : Path x y := Nonempty.some
    (PathConnectedSpace.of_locallyPathConnectedSpace.joined x y)
  obtain ⟨V, hVOpen, hgammaV, hVCompact⟩ :=
    exists_isOpen_superset_and_isCompact_closure
      (isCompact_range gamma.continuous)
  let U : Set X := connectedComponentIn V x
  have hxV : x ∈ V := hgammaV gamma.source_mem_range
  have hgammaU : range gamma ⊆ U :=
    (isPreconnected_range gamma.continuous).subset_connectedComponentIn
      gamma.source_mem_range hgammaV
  refine ⟨U, hVOpen.connectedComponentIn,
    isConnected_connectedComponentIn_iff.mpr hxV,
    mem_connectedComponentIn hxV, hgammaU gamma.target_mem_range, ?_⟩
  exact hVCompact.of_isClosed_subset isClosed_closure
    (closure_mono (connectedComponentIn_subset V x))

end DifferentialGeometry
