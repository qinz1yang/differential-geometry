import Mathlib.Topology.PartitionOfUnity
import Mathlib.Algebra.Module.BigOperators

noncomputable section

open Set

namespace PartitionOfUnity

variable {ι X : Type*} [TopologicalSpace X] {s : Set X}

def fintsupportOn (ρ : PartitionOfUnity ι X s) (K : Set X) (hK : IsCompact K) : Finset ι :=
  (ρ.locallyFinite_tsupport.finite_nonempty_inter_compact hK).toFinset

@[simp]
theorem mem_fintsupportOn (ρ : PartitionOfUnity ι X s) (K : Set X) (hK : IsCompact K)
    (i : ι) : i ∈ ρ.fintsupportOn K hK ↔ (tsupport (ρ i) ∩ K).Nonempty :=
  Set.Finite.mem_toFinset _

theorem fintsupport_subset_fintsupportOn (ρ : PartitionOfUnity ι X s)
    {K : Set X} (hK : IsCompact K) {x : X} (hx : x ∈ K) :
    ρ.fintsupport x ⊆ ρ.fintsupportOn K hK := by
  intro i hi
  rw [mem_fintsupportOn]
  exact ⟨x, (ρ.mem_fintsupport_iff x i).mp hi, hx⟩

theorem finsupport_subset_fintsupportOn (ρ : PartitionOfUnity ι X s)
    {K : Set X} (hK : IsCompact K) {x : X} (hx : x ∈ K) :
    ρ.finsupport x ⊆ ρ.fintsupportOn K hK :=
  (ρ.finsupport_subset_fintsupport x).trans (ρ.fintsupport_subset_fintsupportOn hK hx)

theorem sum_fintsupportOn (ρ : PartitionOfUnity ι X s) {K : Set X} (hK : IsCompact K)
    {x : X} (hxK : x ∈ K) (hxs : x ∈ s) :
    ∑ i ∈ ρ.fintsupportOn K hK, ρ i x = 1 :=
  ρ.sum_finsupport' hxs (ρ.finsupport_subset_fintsupportOn hK hxK)

theorem sum_fintsupportOn_smul (ρ : PartitionOfUnity ι X s)
    {A : Type*} [AddCommMonoid A] [Module ℝ A]
    {K : Set X} (hK : IsCompact K) {f : X → A}
    (hfK : Function.support f ⊆ K) (hfs : Function.support f ⊆ s) (x : X) :
    ∑ i ∈ ρ.fintsupportOn K hK, ρ i x • f x = f x := by
  by_cases hfx : f x = 0
  · simp only [hfx, smul_zero, Finset.sum_const_zero]
  · rw [← Finset.sum_smul, ρ.sum_fintsupportOn hK (hfK hfx) (hfs hfx), one_smul]

end PartitionOfUnity
