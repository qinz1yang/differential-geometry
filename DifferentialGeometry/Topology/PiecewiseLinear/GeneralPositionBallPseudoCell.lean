/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCellNeighborhoodDisk
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCellTransverseBall

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_generalPosition_ball_pseudoCell {Ec Eint Ebd : Set E3} {P : E3}
    (hE : IsPseudoCell Ec Eint Ebd P) {δ : ℝ} (hδ : 0 < δ) :
    ∃ Bl Dc Dcint : Set E3, IsPLBall 3 Bl ∧ Bl ⊆ Metric.ball P δ ∧ P ∈ interior Bl ∧
      IsTopologicalCellWithInterior 2 Dc Dcint ∧ Dc ⊆ Eint ∧ Dc ⊆ Metric.ball P δ ∧
      P ∈ Dcint ∧ Bl ∩ Ec ⊆ Dc ∧ CrossesPseudoCell (frontier Bl) Ec Eint P := by
  obtain ⟨Dc, Dcint, hDc, hDcE, hDcδ, hPDc, ε, hε, hεD⟩ :=
    hE.exists_neighborhood_subdisk hδ
  obtain ⟨Bl, hBl, hBlδ, hPBl, hcross⟩ :=
    hE.exists_small_transverse_ball (lt_min hδ hε)
  refine ⟨Bl, Dc, Dcint, hBl,
    hBlδ.trans (Metric.ball_subset_ball (min_le_left δ ε)), hPBl,
    hDc, hDcE, hDcδ, hPDc, ?_, hcross⟩
  exact (inter_subset_inter_left Ec
    (hBlδ.trans (Metric.ball_subset_ball (min_le_right δ ε)))).trans hεD

end DifferentialGeometry.Topology.PiecewiseLinear
