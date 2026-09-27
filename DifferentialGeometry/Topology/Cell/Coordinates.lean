import DifferentialGeometry.Topology.Simplex.NormedBall
import DifferentialGeometry.Topology.Attachment.Basic

set_option autoImplicit false
noncomputable section
open Set Metric DifferentialGeometry.Topology
namespace DifferentialGeometry.Cell


def stdSimplexClosedCellHomeomorph (n : ℕ) : stdSimplex ℝ (Fin (n + 1)) ≃ₜ ClosedCell n :=
  (DifferentialGeometry.Simplex.stdSimplexNormedBallHomeomorph (EuclideanSpace.equiv (Fin n) ℝ).symm).trans
    (Homeomorph.setCongr (by ext x; change dist x 0 ≤ 1 ↔ ‖x‖ ≤ 1; rw [dist_zero_right]))


def stdSimplexCellBoundaryHomeomorph (n : ℕ) :
    DifferentialGeometry.Simplex.boundary (Fin (n + 1)) ≃ₜ CellBoundary n :=
  (DifferentialGeometry.Simplex.stdSimplexNormedBoundarySphereHomeomorph (EuclideanSpace.equiv (Fin n) ℝ).symm).trans
    (Homeomorph.setCongr (by ext x; change dist x 0 = 1 ↔ ‖x‖ = 1; rw [dist_zero_right]))


@[simp]
theorem stdSimplexCellBoundaryHomeomorph_inclusion (n : ℕ)
    (x : DifferentialGeometry.Simplex.boundary (Fin (n + 1))) :
    cellBoundaryInclusion n (stdSimplexCellBoundaryHomeomorph n x) =
      stdSimplexClosedCellHomeomorph n x.val := rfl

end DifferentialGeometry.Cell
