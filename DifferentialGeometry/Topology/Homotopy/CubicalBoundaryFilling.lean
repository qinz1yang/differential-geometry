import DifferentialGeometry.Topology.Homotopy.CubicalBoundary
import DifferentialGeometry.Topology.Homotopy.SquareFilling

noncomputable section
open scoped unitInterval
namespace DifferentialGeometry.Topology
variable {N X : Type*} [TopologicalSpace X] [DecidableEq N] {x : X}

theorem genLoop_transAt_homotopic_of_group_eq [Nonempty N]
    (i : N) (a b c d : GenLoop N X x)
    (h : ((· * ·) : _ → _ → HomotopyGroup N X x) ⟦d⟧ ⟦a⟧ =
      ((· * ·) : _ → _ → HomotopyGroup N X x) ⟦b⟧ ⟦c⟧) :
    GenLoop.Homotopic (GenLoop.transAt i a d) (GenLoop.transAt i c b) := by
  rw [HomotopyGroup.mul_spec (i := i), HomotopyGroup.mul_spec (i := i)] at h
  exact Quotient.exact h

theorem exists_square_of_homotopyGroup_mul_eq_mul [Nonempty N]
    (i : N) (a b c d : GenLoop N X x)
    (h : ((· * ·) : _ → _ → HomotopyGroup N X x) ⟦d⟧ ⟦a⟧ =
      ((· * ·) : _ → _ → HomotopyGroup N X x) ⟦b⟧ ⟦c⟧) :
    ∃ F : C(unitInterval × unitInterval, GenLoop {j : N // j ≠ i} X x),
      (∀ t, F (0, t) = GenLoop.toLoop i a t) ∧
      (∀ t, F (1, t) = GenLoop.toLoop i b t) ∧
      (∀ t, F (t, 0) = GenLoop.toLoop i c t) ∧
      (∀ t, F (t, 1) = GenLoop.toLoop i d t) := by
  apply exists_square_of_boundary_homotopic
  have hloop := GenLoop.homotopicTo i (genLoop_transAt_homotopic_of_group_eq i a b c d h)
  rwa [← GenLoop.fromLoop_trans_toLoop, GenLoop.to_from,
    ← GenLoop.fromLoop_trans_toLoop, GenLoop.to_from] at hloop

end DifferentialGeometry.Topology
