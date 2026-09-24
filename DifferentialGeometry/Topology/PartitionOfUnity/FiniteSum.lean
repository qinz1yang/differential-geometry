import Mathlib.Topology.PartitionOfUnity

section

set_option autoImplicit false
noncomputable section

open Set
open scoped Topology

namespace PartitionOfUnity

variable {ι M : Type*} [TopologicalSpace M]

theorem sum_finset_le_one {s₀ : Set M} (ρ : PartitionOfUnity ι M s₀)
    (s : Finset ι) (x : M) : (∑ i ∈ s, ρ i x) ≤ 1 := by
  classical
  calc
    _ ≤ ∑ i ∈ s ∪ ρ.finsupport x, ρ i x :=
      Finset.sum_le_sum_of_subset_of_nonneg Finset.subset_union_left
        (fun i _ _ => ρ.nonneg i x)
    _ = ∑ᶠ i, ρ i x := by
      symm
      apply finsum_eq_sum_of_support_subset
      intro i hi
      exact Finset.mem_union.mpr (Or.inr ((ρ.mem_finsupport x).mpr hi))
    _ ≤ 1 := ρ.sum_le_one x

end PartitionOfUnity

end

end
