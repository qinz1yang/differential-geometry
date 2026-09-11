import Mathlib.Topology.Connected.Basic
import Mathlib.Data.Fin.SuccPredOrder

open Set

namespace DifferentialGeometry.Topology

theorem isConnected_iUnion_of_finite_chain
    {X : Type*} [TopologicalSpace X] {n : ℕ} (U : Fin (n + 1) → Set X)
    (hU : ∀ i, IsConnected (U i))
    (hmeet : ∀ i : Fin n, (U i.castSucc ∩ U i.succ).Nonempty) :
    IsConnected (⋃ i, U i) := by
  apply IsConnected.iUnion_of_chain hU
  intro i
  by_cases hi : i = Fin.last n
  · subst i
    simpa using (hU (Fin.last n)).nonempty
  · obtain ⟨i, rfl⟩ := Fin.eq_castSucc_of_ne_last hi
    simpa only [Fin.orderSucc_castSucc] using hmeet i

end DifferentialGeometry.Topology
