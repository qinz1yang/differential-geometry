import Mathlib.Topology.Connected.LocallyPathConnected
import Mathlib.Topology.Separation.Basic

set_option autoImplicit false

noncomputable section

open Filter Set

theorem IsPreconnected.forall_of_locally_imp
    {X : Type*} [TopologicalSpace X] {Omega : Set X} (hOmega : IsPreconnected Omega)
    {P : X → Prop}
    (hlocal : ∀ a ∈ Omega, ∃ U : Set X, IsOpen U ∧ a ∈ U ∧ U ⊆ Omega ∧
      ∀ x ∈ U, P x → ∀ y ∈ U, P y)
    {x : X} (hx : x ∈ Omega) (hPx : P x) : ∀ y ∈ Omega, P y := by
  let S : Set X := Omega ∩ {z | P z}
  have hSopen : IsOpen S := by
    apply isOpen_iff_mem_nhds.mpr
    intro a ha
    obtain ⟨U, hUopen, haU, hUOmega, hUprop⟩ := hlocal a ha.1
    exact mem_of_superset (hUopen.mem_nhds haU)
      (fun y hy => ⟨hUOmega hy, hUprop a haU ha.2 y hy⟩)
  have hSclosure : closure S ∩ Omega ⊆ S := by
    intro a ha
    obtain ⟨U, hUopen, haU, -, hUprop⟩ := hlocal a ha.2
    obtain ⟨c, hcU, hcS⟩ := mem_closure_iff.mp ha.1 U hUopen haU
    exact ⟨ha.2, hUprop c hcU hcS.2 a haU⟩
  have hsubset : Omega ⊆ S := hOmega.subset_of_closure_inter_subset
    hSopen ⟨x, hx, hx, hPx⟩ hSclosure
  exact fun y hy => (hsubset hy).2

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
