import DifferentialGeometry.Topology.ThreeManifold.ConnectedSum.BallMarkingSupport

set_option autoImplicit false
noncomputable section
open Set Metric
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.Topology

universe u

private abbrev E₃ := EuclideanSpace ℝ (Fin 3)

variable {M : ClosedOrientedManifold.{u} 3} {I : Type u} [Fintype I]

theorem BallMarking.disjoint_reserve_of_disjoint_support_regions {B B' : BallMarking M I}
    {V : I → Set M.Carrier} (hV : ∀ k, B.reserve k ∪ B'.reserve k ⊆ V k)
    (hdisj : ∀ k l, k ≠ l → Disjoint (V k) (V l)) {i j : I} (hij : i ≠ j) :
    Disjoint (B'.reserve i) (B.reserve j) :=
  (hdisj i j hij).mono (fun _ hy => hV i (subset_union_right hy))
    (fun _ hy => hV j (subset_union_left hy))

theorem BallMarking.not_exists_disjoint_support_regions_of_not_disjoint {B B' : BallMarking M I}
    {i j : I} (hij : i ≠ j) (h : ¬ Disjoint (B'.reserve i) (B.reserve j)) :
    ¬ ∃ V : I → Set M.Carrier,
      (∀ k, B.reserve k ∪ B'.reserve k ⊆ V k) ∧
      (∀ k l, k ≠ l → Disjoint (V k) (V l)) := by
  rintro ⟨V, hV, hdisj⟩
  exact h (BallMarking.disjoint_reserve_of_disjoint_support_regions hV hdisj hij)

end DifferentialGeometry.Topology
