import DifferentialGeometry.Topology.PiecewiseLinear.Section34AnnularBandComponents
import DifferentialGeometry.Topology.PiecewiseLinear.PolyhedronLocalConnectedness
import DifferentialGeometry.Topology.PiecewiseLinear.Section34PiercingSourceBicollar

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_open_connected_inter_of_locallyConnectedSpace {M : Type*}
    [TopologicalSpace M] {B O : Set M} [LocallyConnectedSpace B]
    (hO : IsOpen O) {x : M} (hxB : x ∈ B) (hxO : x ∈ O) :
    ∃ V : Set M, IsOpen V ∧ x ∈ V ∧ V ⊆ O ∧ IsConnected (B ∩ V) := by
  let x' : B := ⟨x, hxB⟩
  have hpre : (Subtype.val : B → M) ⁻¹' O ∈ 𝓝 x' :=
    (hO.preimage continuous_subtype_val).mem_nhds hxO
  obtain ⟨W, hWO, hW, hxW, hWconn⟩ :=
    locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp inferInstance x' _ hpre
  obtain ⟨V, hV, hVW⟩ := isOpen_induced_iff.mp hW
  have hxV : x ∈ V := show x' ∈ (Subtype.val : B → M) ⁻¹' V from hVW.symm ▸ hxW
  have himage : (Subtype.val : B → M) '' W = B ∩ (V ∩ O) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      have hzV : z ∈ (Subtype.val : B → M) ⁻¹' V := hVW.symm ▸ hz
      exact ⟨z.2, hzV, hWO hz⟩
    · rintro ⟨hyB, hyV, -⟩
      exact ⟨⟨y, hyB⟩, hVW ▸ hyV, rfl⟩
  refine ⟨V ∩ O, hV.inter hO, ⟨hxV, hxO⟩, inter_subset_right, ?_⟩
  rw [← himage]
  exact hWconn.image Subtype.val continuous_subtype_val.continuousOn

end DifferentialGeometry.Topology.PiecewiseLinear
