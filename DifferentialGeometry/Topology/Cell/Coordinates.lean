import DifferentialGeometry.Topology.Simplex.NormedBall
import DifferentialGeometry.Topology.Attachment.Basic

set_option autoImplicit false
noncomputable section
open Set Metric DifferentialGeometry.Topology
namespace Poincare.Cell


def stdSimplexClosedCellHomeomorph (n : ℕ) : stdSimplex ℝ (Fin (n + 1)) ≃ₜ ClosedCell n :=
  (Poincare.Simplex.stdSimplexNormedBallHomeomorph (EuclideanSpace.equiv (Fin n) ℝ).symm).trans
    (Homeomorph.setCongr (by ext x; change dist x 0 ≤ 1 ↔ ‖x‖ ≤ 1; rw [dist_zero_right]))


def stdSimplexCellBoundaryHomeomorph (n : ℕ) :
    Poincare.Simplex.boundary (Fin (n + 1)) ≃ₜ CellBoundary n :=
  (Poincare.Simplex.stdSimplexNormedBoundarySphereHomeomorph (EuclideanSpace.equiv (Fin n) ℝ).symm).trans
    (Homeomorph.setCongr (by ext x; change dist x 0 = 1 ↔ ‖x‖ = 1; rw [dist_zero_right]))


@[simp]
theorem stdSimplexCellBoundaryHomeomorph_inclusion (n : ℕ)
    (x : Poincare.Simplex.boundary (Fin (n + 1))) :
    cellBoundaryInclusion n (stdSimplexCellBoundaryHomeomorph n x) =
      stdSimplexClosedCellHomeomorph n x.val := rfl

end Poincare.Cell
