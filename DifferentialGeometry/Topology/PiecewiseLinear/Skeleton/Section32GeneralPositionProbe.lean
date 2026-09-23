/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCell

/-!
# Reconnaissance of a general-position ball around a pseudo-cell center

The local transverse sphere and its absorbing interior subdisk are separate
geometric obligations. The final existential conjunction follows from them.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear.Section32GeneralPositionProbe

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_small_transverse_ball
    {Ec Eint Ebd : Set E3} {P : E3}
    (hE : IsPseudoCell Ec Eint Ebd P) {δ : ℝ} (hδ : 0 < δ) :
    ∃ Bl : Set E3, IsPLBall 3 Bl ∧ Bl ⊆ Metric.ball P δ ∧
      P ∈ interior Bl ∧ CrossesPseudoCell (frontier Bl) Ec Eint P := by
  sorry

theorem exists_trace_absorbing_subdisk
    {Ec Eint Ebd Bl : Set E3} {P : E3}
    (hE : IsPseudoCell Ec Eint Ebd P) {δ : ℝ} (hδ : 0 < δ)
    (hBl : IsPLBall 3 Bl) (hBlδ : Bl ⊆ Metric.ball P δ)
    (hPBl : P ∈ interior Bl)
    (hcross : CrossesPseudoCell (frontier Bl) Ec Eint P) :
    ∃ Dc Dcint : Set E3,
      IsTopologicalCellWithInterior 2 Dc Dcint ∧ Dc ⊆ Eint ∧
      Dc ⊆ Metric.ball P δ ∧ P ∈ Dcint ∧ Bl ∩ Ec ⊆ Dc := by
  sorry

theorem general_position_ball_of_subleaves
    {Ec Eint Ebd : Set E3} {P : E3}
    (hE : IsPseudoCell Ec Eint Ebd P) {δ : ℝ} (hδ : 0 < δ) :
    ∃ Bl Dc Dcint : Set E3, IsPLBall 3 Bl ∧ Bl ⊆ Metric.ball P δ ∧
      P ∈ interior Bl ∧ IsTopologicalCellWithInterior 2 Dc Dcint ∧
      Dc ⊆ Eint ∧ Dc ⊆ Metric.ball P δ ∧ P ∈ Dcint ∧
      Bl ∩ Ec ⊆ Dc ∧ CrossesPseudoCell (frontier Bl) Ec Eint P := by
  obtain ⟨Bl, hBl, hBlδ, hPBl, hcross⟩ := exists_small_transverse_ball hE hδ
  obtain ⟨Dc, Dcint, hDc, hDcE, hDcδ, hPDc, hBE⟩ :=
    exists_trace_absorbing_subdisk hE hδ hBl hBlδ hPBl hcross
  exact ⟨Bl, Dc, Dcint, hBl, hBlδ, hPBl, hDc, hDcE, hDcδ,
    hPDc, hBE, hcross⟩

end DifferentialGeometry.Topology.PiecewiseLinear.Section32GeneralPositionProbe
