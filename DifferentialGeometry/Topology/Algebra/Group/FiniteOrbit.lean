import Mathlib.GroupTheory.Index

namespace MulAction

variable {G X : Type*} [Group G] [MulAction G X]

theorem finite_orbit_of_finiteIndex (H : Subgroup G) [H.FiniteIndex] (x : X)
    (hx : (orbit H x).Finite) : (orbit G x).Finite := by
  have hrel : (stabilizer G x).relIndex H ≠ 0 := by
    rw [Subgroup.relIndex, stabilizer_subgroupOf, index_stabilizer]
    exact Set.ncard_ne_zero_of_mem (mem_orbit_self x) hx
  have htop : H.relIndex ⊤ ≠ 0 := by
    rw [Subgroup.relIndex_top_right]
    exact Subgroup.FiniteIndex.index_ne_zero
  have hindex := Subgroup.relIndex_ne_zero_trans hrel htop
  rw [Subgroup.relIndex_top_right, index_stabilizer] at hindex
  exact Set.finite_of_ncard_ne_zero hindex

end MulAction
