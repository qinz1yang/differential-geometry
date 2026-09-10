import Mathlib.Topology.PartitionOfUnity

noncomputable section
open Set Filter Topology

namespace Poincare.Topology

theorem partition_eq_one_near_of_disjoint_tsupport
    {ι X : Type*} [TopologicalSpace X] (ρ : PartitionOfUnity ι X)
    (C : Set X) (i : ι)
    (hdisj : ∀ j, j ≠ i → Disjoint C (tsupport (ρ j))) :
    ∀ᶠ x in 𝓝ˢ C, ρ i x = 1 ∧ ∀ j, j ≠ i → ρ j x = 0 := by
  classical
  let B := ⋃ j : {j : ι // j ≠ i}, tsupport (ρ j.1)
  have hB : IsClosed B :=
    (ρ.locallyFinite.closure.comp_injective Subtype.val_injective).isClosed_iUnion
      (fun _ ↦ isClosed_tsupport _)
  have hCB : C ⊆ Bᶜ := by
    intro x hx hxB
    obtain ⟨j, hj⟩ := mem_iUnion.mp hxB
    exact Set.disjoint_left.mp (hdisj j.1 j.2) hx hj
  filter_upwards [hB.isOpen_compl.mem_nhdsSet.mpr hCB] with x hx
  have hzero : ∀ j, j ≠ i → ρ j x = 0 := by
    intro j hj
    apply image_eq_zero_of_notMem_tsupport
    intro hxj
    exact hx (mem_iUnion.mpr ⟨⟨j, hj⟩, hxj⟩)
  refine ⟨?_, hzero⟩
  have hsum := ρ.sum_eq_one (mem_univ x)
  rwa [finsum_eq_single _ i hzero] at hsum

theorem partition_patch_eq_near_of_disjoint_tsupport
    {ι X F : Type*} [TopologicalSpace X] [AddCommMonoid F] [Module ℝ F]
    (ρ : PartitionOfUnity ι X) (u : ι → X → F) (C : Set X) (i : ι)
    (hdisj : ∀ j, j ≠ i → Disjoint C (tsupport (ρ j))) :
    ∀ᶠ x in 𝓝ˢ C, (∑ᶠ j, ρ j x • u j x) = u i x := by
  filter_upwards [partition_eq_one_near_of_disjoint_tsupport ρ C i hdisj] with x hx
  rw [finsum_eq_single _ i (fun j hj ↦ by rw [hx.2 j hj, zero_smul]), hx.1, one_smul]

end Poincare.Topology
