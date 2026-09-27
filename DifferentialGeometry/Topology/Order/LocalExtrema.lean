import Mathlib.Topology.Order.LocalExtr
import Mathlib.Topology.Order.OrderClosed

open Set

theorem not_isLocalMax_iff_mem_closure_gt {X α : Type*} [TopologicalSpace X]
    [LinearOrder α] {f : X → α} {x : X} :
    ¬ IsLocalMax f x ↔ x ∈ closure {y | f x < f y} := by
  simp only [mem_closure_iff_frequently, Filter.Frequently, mem_ofPred_eq, not_lt,
    IsLocalMax, IsMaxFilter]

theorem not_isLocalMin_iff_mem_closure_lt {X α : Type*} [TopologicalSpace X]
    [LinearOrder α] {f : X → α} {x : X} :
    ¬ IsLocalMin f x ↔ x ∈ closure {y | f y < f x} :=
  not_isLocalMax_iff_mem_closure_gt (α := OrderDual α)

theorem Continuous.closure_gt_eq_ge_of_not_isLocalMax {X α : Type*} [TopologicalSpace X]
    [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α]
    {f : X → α} (hf : Continuous f) {a : α}
    (ha : ∀ x, f x = a → ¬ IsLocalMax f x) :
    closure {x | a < f x} = {x | a ≤ f x} := by
  apply Subset.antisymm
  · exact closure_minimal (fun x hx => hx.le) (isClosed_le continuous_const hf)
  · intro x hx
    rcases eq_or_lt_of_le hx with h | h
    · have hc := not_isLocalMax_iff_mem_closure_gt.mp (ha x h.symm)
      simpa [h] using hc
    · exact subset_closure h

theorem Continuous.closure_lt_eq_le_of_not_isLocalMin {X α : Type*} [TopologicalSpace X]
    [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α]
    {f : X → α} (hf : Continuous f) {a : α}
    (ha : ∀ x, f x = a → ¬ IsLocalMin f x) :
    closure {x | f x < a} = {x | f x ≤ a} :=
  hf.closure_gt_eq_ge_of_not_isLocalMax (α := OrderDual α) ha
