import DifferentialGeometry.Topology.Connected.FinitePartition
import DifferentialGeometry.Topology.PiecewiseLinear.CurveInclusion

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem setOf_isPLSphere_one_subset_sUnion_eq {C : Set (Set E)} (hC : C.Finite)
    (hCsphere : ∀ S ∈ C, IsPLSphere 1 S) (hdisjoint : C.PairwiseDisjoint id) :
    {S | IsPLSphere 1 S ∧ S ⊆ ⋃₀ C} = C := by
  ext S
  constructor
  · rintro ⟨hS, hSC⟩
    obtain ⟨T, ⟨hTC, hST⟩, -⟩ := existsUnique_subset_of_isConnected_of_finite_closed_partition
      hS.isConnected_one hC (fun T hT => (hCsphere T hT).isPolyhedron.isClosed) hdisjoint hSC
    exact eq_of_subset_of_isPLSphere_one hS (hCsphere T hTC) hST ▸ hTC
  · intro hS
    exact ⟨hCsphere S hS, subset_sUnion_of_mem hS⟩

theorem isPLSphere_one_sUnion_iff_isConnected {C : Set (Set E)} (hC : C.Finite)
    (hCsphere : ∀ S ∈ C, IsPLSphere 1 S) (hdisjoint : C.PairwiseDisjoint id) :
    IsPLSphere 1 (⋃₀ C) ↔ IsConnected (⋃₀ C) := by
  refine ⟨fun h => h.isConnected_one, fun h => ?_⟩
  obtain ⟨T, ⟨hTC, hsub⟩, -⟩ := existsUnique_subset_of_isConnected_of_finite_closed_partition h hC
    (fun T hT => (hCsphere T hT).isPolyhedron.isClosed) hdisjoint Subset.rfl
  exact Subset.antisymm hsub (subset_sUnion_of_mem hTC) ▸ hCsphere T hTC

theorem isPLSphere_one_sUnion_iff_encard_eq_one {C : Set (Set E)} (hC : C.Finite)
    (hCsphere : ∀ S ∈ C, IsPLSphere 1 S) (hdisjoint : C.PairwiseDisjoint id) :
    IsPLSphere 1 (⋃₀ C) ↔ C.encard = 1 := by
  constructor
  · intro h
    apply Set.encard_eq_one.mpr
    refine ⟨⋃₀ C, ?_⟩
    have hmem : ⋃₀ C ∈ C :=
      (setOf_isPLSphere_one_subset_sUnion_eq hC hCsphere hdisjoint).subset ⟨h, Subset.rfl⟩
    apply Subset.antisymm ?_ (singleton_subset_iff.mpr hmem)
    intro T hT
    exact eq_of_subset_of_isPLSphere_one (hCsphere T hT) h (subset_sUnion_of_mem hT)
  · intro h
    obtain ⟨T, rfl⟩ := Set.encard_eq_one.mp h
    simpa only [sUnion_singleton] using hCsphere T (mem_singleton T)

end DifferentialGeometry.Topology.PiecewiseLinear
