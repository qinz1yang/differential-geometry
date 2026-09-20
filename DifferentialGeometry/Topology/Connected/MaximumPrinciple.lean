import DifferentialGeometry.Topology.Connected.ComponentIn
import Mathlib.Topology.Connected.LocallyConnected
import Mathlib.Topology.Order.Compact

section

open Set

variable {X α : Type*} [TopologicalSpace X] [LocallyConnectedSpace X]
  [LinearOrder α] [TopologicalSpace α] [OrderClosedTopology α]

theorem Continuous.connectedComponentIn_gt_inter_nonempty_of_maximum_principle
    {f : X → α} (hf : Continuous f) {a : α} (ha : IsCompact {x | a ≤ f x})
    {B : Set X}
    (hmax : ∀ Ω : Set X, IsOpen Ω → IsCompact (closure Ω) → Ω ⊆ Bᶜ →
      ∀ c : α, (∀ x ∈ frontier Ω, f x ≤ c) → ∀ x ∈ Ω, f x ≤ c)
    {x : X} (hx : a < f x) :
    (connectedComponentIn {y | a < f y} x ∩ B).Nonempty := by
  let U := {y | a < f y}
  let C := connectedComponentIn U x
  have hU : IsOpen U := isOpen_lt continuous_const hf
  have hC : IsOpen C := hU.connectedComponentIn
  have hxC : x ∈ C := mem_connectedComponentIn hx
  have hcompact : IsCompact (closure C) := ha.of_isClosed_subset isClosed_closure
    (closure_minimal (fun y hy => (show a < f y from connectedComponentIn_subset U x hy).le)
      (isClosed_le continuous_const hf))
  by_contra hne
  have hCB : C ⊆ Bᶜ := fun y hy hB => hne ⟨y, hy, hB⟩
  have hboundary (y : X) (hy : y ∈ frontier C) : f y ≤ a := by
    apply le_of_not_gt
    intro hyU
    have hyC : y ∈ C := (closure_connectedComponentIn_inter U x).subset ⟨hy.1, hyU⟩
    exact hy.2 (hC.interior_eq.symm ▸ hyC)
  exact (not_le_of_gt hx) (hmax C hC hcompact hCB a hboundary x hxC)

theorem Continuous.isPreconnected_gt_of_maximum_principle
    {f : X → α} (hf : Continuous f) {a : α} (ha : IsCompact {x | a ≤ f x})
    {B : Set X}
    (hmax : ∀ Ω : Set X, IsOpen Ω → IsCompact (closure Ω) → Ω ⊆ Bᶜ →
      ∀ c : α, (∀ x ∈ frontier Ω, f x ≤ c) → ∀ x ∈ Ω, f x ≤ c)
    (hB : IsPreconnected (B ∩ {x | a < f x})) : IsPreconnected {x | a < f x} := by
  by_cases hne : ({x | a < f x} : Set X).Nonempty
  · obtain ⟨x, hx⟩ := hne
    obtain ⟨p, hpC, hpB⟩ := hf.connectedComponentIn_gt_inter_nonempty_of_maximum_principle
      ha hmax hx
    have hpU : a < f p := connectedComponentIn_subset {y | a < f y} x hpC
    have hcap : B ∩ {y | a < f y} ⊆ connectedComponentIn {y | a < f y} p :=
      hB.subset_connectedComponentIn ⟨hpB, hpU⟩ inter_subset_right
    have heq : connectedComponentIn {y | a < f y} x = {y | a < f y} := by
      apply Subset.antisymm (connectedComponentIn_subset _ _)
      intro y hy
      obtain ⟨q, hqC, hqB⟩ := hf.connectedComponentIn_gt_inter_nonempty_of_maximum_principle
        ha hmax hy
      have hqU : a < f q := connectedComponentIn_subset {z | a < f z} y hqC
      have hqCx : q ∈ connectedComponentIn {z | a < f z} x := by
        rw [connectedComponentIn_eq hpC]
        exact hcap ⟨hqB, hqU⟩
      rw [(connectedComponentIn_eq hqCx).trans (connectedComponentIn_eq hqC).symm]
      exact mem_connectedComponentIn hy
    rw [← heq]
    exact isPreconnected_connectedComponentIn
  · rw [not_nonempty_iff_eq_empty.mp hne]
    exact isPreconnected_empty

theorem Continuous.connectedComponentIn_lt_inter_nonempty_of_minimum_principle
    {f : X → α} (hf : Continuous f) {a : α} (ha : IsCompact {x | f x ≤ a})
    {B : Set X}
    (hmin : ∀ Ω : Set X, IsOpen Ω → IsCompact (closure Ω) → Ω ⊆ Bᶜ →
      ∀ c : α, (∀ x ∈ frontier Ω, c ≤ f x) → ∀ x ∈ Ω, c ≤ f x)
    {x : X} (hx : f x < a) :
    (connectedComponentIn {y | f y < a} x ∩ B).Nonempty :=
  Continuous.connectedComponentIn_gt_inter_nonempty_of_maximum_principle
    (α := OrderDual α) hf ha hmin hx

theorem Continuous.isPreconnected_lt_of_minimum_principle
    {f : X → α} (hf : Continuous f) {a : α} (ha : IsCompact {x | f x ≤ a})
    {B : Set X}
    (hmin : ∀ Ω : Set X, IsOpen Ω → IsCompact (closure Ω) → Ω ⊆ Bᶜ →
      ∀ c : α, (∀ x ∈ frontier Ω, c ≤ f x) → ∀ x ∈ Ω, c ≤ f x)
    (hB : IsPreconnected (B ∩ {x | f x < a})) : IsPreconnected {x | f x < a} :=
  Continuous.isPreconnected_gt_of_maximum_principle (α := OrderDual α) hf ha hmin hB

end
