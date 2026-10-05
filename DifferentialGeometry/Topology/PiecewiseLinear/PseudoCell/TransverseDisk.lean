import DifferentialGeometry.Topology.PiecewiseLinear.GeneralPositionBallPseudoCell
import DifferentialGeometry.Topology.PiecewiseLinear.ReducedDiskPseudoCell

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem IsPseudoCell.exists_transverse_plDisk
    {Ec Eint Ebd : Set E3} {P : E3} (hE : IsPseudoCell Ec Eint Ebd P)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (Δ Δbd : Set E3)
      (r : (Fin 3 → ℝ) → E3),
      IsPLHomeomorphOn r (Convexity.StdSimplex.coordinateSet ℝ (Fin 3)) Δ ∧
      Δbd = r '' stdSimplexBoundary 2 ∧
      Δ ⊆ Metric.ball P δ ∧
      Δbd = Δ ∩ Ec ∧
      ∃ DJ DJint : Set E3,
        IsTopologicalCellWithInterior 2 DJ DJint ∧ DJ ⊆ Ec ∧ DJ \ DJint = Δbd ∧ P ∈ DJint := by
  obtain ⟨Bl, Dc, Dcint, hBl, hBδ, hPB, hDc, hDcE, hDcδ, hPDc, hBE, hgp⟩ :=
    exists_generalPosition_ball_pseudoCell hE hδ
  obtain ⟨Δ, Δbd, r, hr, hΔbd, hΔδ, hΔE, DJ, DJint, hDJ, hDJE, hDJbd, hPDJ⟩ :=
    exists_reducedDisk_of_crossesPseudoCell hE hBl hPB hDc hDcE hPDc hBE hgp
      Metric.isOpen_ball hBδ hDcδ
  exact ⟨Δ, Δbd, r, hr, hΔbd, hΔδ, hΔE, DJ, DJint, hDJ, hDJE, hDJbd, hPDJ⟩

end DifferentialGeometry.Topology.PiecewiseLinear
