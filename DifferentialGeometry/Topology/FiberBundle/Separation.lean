import Mathlib.Topology.FiberBundle.Basic
import Mathlib.Topology.Separation.Hausdorff

open Bundle Filter
open scoped Topology

namespace FiberBundle

variable {B F : Type*} [TopologicalSpace B] [TopologicalSpace F]
  {V : B → Type*} [∀ b, TopologicalSpace (V b)]
  [TopologicalSpace (TotalSpace F V)] [FiberBundle F V]

instance instT2SpaceTotalSpace [T2Space B] [T2Space F] : T2Space (TotalSpace F V) := by
  apply t2Space_iff_disjoint_nhds.mpr
  intro z w hne
  by_cases hbase : z.proj = w.proj
  · let e := trivializationAt F V z.proj
    have hz : z ∈ e.source := e.mem_source.mpr (mem_baseSet_trivializationAt F V z.proj)
    have hw : w ∈ e.source := e.mem_source.mpr (by
      rw [← hbase]
      exact mem_baseSet_trivializationAt F V z.proj)
    have he : e z ≠ e w := fun h => hne (e.injOn hz hw h)
    exact (e.continuousAt hz).disjoint (disjoint_nhds_nhds.mpr he) (e.continuousAt hw)
  · exact (continuous_proj F V).continuousAt.disjoint (disjoint_nhds_nhds.mpr hbase)
      (continuous_proj F V).continuousAt

end FiberBundle
