import Mathlib.Topology.PartitionOfUnity
import Mathlib.Topology.Compactness.LocallyFinite
import Mathlib.Algebra.Module.BigOperators

open Set

namespace PartitionOfUnity

theorem exists_finset_sum_smul_eq
    {A ι F : Type*} [TopologicalSpace A] [AddCommMonoid F] [Module Real F]
    {s : Set A} (rho : PartitionOfUnity ι A s) {f : A → F}
    (hc : HasCompactSupport f) (hs : Function.support f ⊆ s) :
    ∃ t : Finset ι, ∀ x, ∑ i ∈ t, rho i x • f x = f x := by
  classical
  let t := (rho.locallyFinite.closure.finite_nonempty_inter_compact hc).toFinset
  refine ⟨t, fun x => ?_⟩
  by_cases hfx : f x = 0
  · simp only [hfx, smul_zero, Finset.sum_const_zero]
  · have hxs := subset_tsupport f hfx
    have hsub : rho.finsupport x ⊆ t := by
      intro i hi
      have hix : x ∈ tsupport (rho i) := subset_tsupport _ ((rho.mem_finsupport x).mp hi)
      exact (Set.Finite.mem_toFinset _).mpr ⟨x, hix, hxs⟩
    rw [← Finset.sum_smul, rho.sum_finsupport' (hs hfx) hsub, one_smul]

end PartitionOfUnity
