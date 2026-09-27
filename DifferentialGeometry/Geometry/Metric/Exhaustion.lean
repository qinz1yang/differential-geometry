import Mathlib.Topology.MetricSpace.Defs
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.ProperSpace

set_option autoImplicit false

namespace DifferentialGeometry

structure MetricExhaustion (X : Type*) [MetricSpace X] where
  carrier : ℕ → Set X
  compact : ∀ n, IsCompact (carrier n)
  mono : Monotone carrier
  union_eq_univ : ⋃ n, carrier n = Set.univ

namespace MetricExhaustion

variable {X : Type*} [MetricSpace X] [ProperSpace X]

noncomputable def closedBall (x : X) : MetricExhaustion X where
  carrier := fun n => Metric.closedBall x (n : ℝ)
  compact := fun n => isCompact_closedBall x (n : ℝ)
  mono := by
    intro m n hmn
    exact Metric.closedBall_subset_closedBall (by exact_mod_cast hmn)
  union_eq_univ := by
    apply Set.eq_univ_of_forall
    intro y
    obtain ⟨n, hn⟩ := exists_nat_ge (dist y x)
    rw [Set.mem_iUnion]
    refine ⟨n, ?_⟩
    rw [Metric.mem_closedBall]
    exact (dist_comm y x).symm ▸ hn

@[simp] theorem closedBall_carrier (x : X) (n : ℕ) :
    (closedBall x).carrier n = Metric.closedBall x (n : ℝ) := rfl

theorem compact_subset_closedBall (x : X) {K : Set X} (hK : IsCompact K) :
    ∃ n, K ⊆ (closedBall x).carrier n := by
  obtain ⟨r, hr, hKr⟩ := hK.isBounded.subset_closedBall_lt 0 x
  obtain ⟨n, hn⟩ := exists_nat_ge r
  refine ⟨n, hKr.trans ?_⟩
  exact Metric.closedBall_subset_closedBall hn

end MetricExhaustion

end DifferentialGeometry
