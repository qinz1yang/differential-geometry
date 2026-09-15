import DifferentialGeometry.Topology.Homotopy.SquareBoundary
import Mathlib.Topology.Homotopy.HomotopyGroup

noncomputable section

open scoped unitInterval

namespace DifferentialGeometry.Topology

variable {N X : Type*} [TopologicalSpace X] [DecidableEq N] {x : X}

theorem genLoop_transAt_homotopic_of_square (i : N) (a b c d : GenLoop N X x)
    (F : C(I × I, GenLoop {j : N // j ≠ i} X x))
    (hbottom : ∀ t, F (0, t) = GenLoop.toLoop i a t)
    (htop : ∀ t, F (1, t) = GenLoop.toLoop i b t)
    (hleft : ∀ t, F (t, 0) = GenLoop.toLoop i c t)
    (hright : ∀ t, F (t, 1) = GenLoop.toLoop i d t) :
    GenLoop.Homotopic (GenLoop.transAt i a d) (GenLoop.transAt i c b) := by
  apply GenLoop.homotopicFrom i
  rw [← GenLoop.fromLoop_trans_toLoop, GenLoop.to_from,
    ← GenLoop.fromLoop_trans_toLoop, GenLoop.to_from]
  exact square_boundary_homotopic (GenLoop.toLoop i a) (GenLoop.toLoop i b)
    (GenLoop.toLoop i c) (GenLoop.toLoop i d) F hbottom htop hleft hright

theorem homotopyGroup_mul_eq_mul_of_square [Nonempty N] (i : N) (a b c d : GenLoop N X x)
    (F : C(I × I, GenLoop {j : N // j ≠ i} X x))
    (hbottom : ∀ t, F (0, t) = GenLoop.toLoop i a t)
    (htop : ∀ t, F (1, t) = GenLoop.toLoop i b t)
    (hleft : ∀ t, F (t, 0) = GenLoop.toLoop i c t)
    (hright : ∀ t, F (t, 1) = GenLoop.toLoop i d t) :
    ((· * ·) : _ → _ → HomotopyGroup N X x) ⟦d⟧ ⟦a⟧ =
      ((· * ·) : _ → _ → HomotopyGroup N X x) ⟦b⟧ ⟦c⟧ := by
  rw [HomotopyGroup.mul_spec (i := i), HomotopyGroup.mul_spec (i := i)]
  exact Quotient.sound (genLoop_transAt_homotopic_of_square i a b c d F
    hbottom htop hleft hright)

end DifferentialGeometry.Topology
