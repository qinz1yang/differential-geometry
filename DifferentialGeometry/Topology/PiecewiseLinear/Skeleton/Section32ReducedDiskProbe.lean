/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PseudoCell

/-!
# Reconnaissance of disk reduction across a pseudo-cell

The outermost PL disk and the disk it bounds in the pseudo-cell are separate
geometric obligations. Their conjunction has the exact Section 32 output.
-/

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear.Section32ReducedDiskProbe

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem exists_outermost_disk_with_intrinsic_rim
    {Ec Eint Ebd Bl Dc Dcint Ω : Set E3} {P : E3}
    (hE : IsPseudoCell Ec Eint Ebd P) (hBl : IsPLBall 3 Bl)
    (hP : P ∈ interior Bl)
    (hDc : IsTopologicalCellWithInterior 2 Dc Dcint) (hDcE : Dc ⊆ Eint)
    (hPDc : P ∈ Dcint) (hBE : Bl ∩ Ec ⊆ Dc)
    (hgp : CrossesPseudoCell (frontier Bl) Ec Eint P)
    (hΩ : IsOpen Ω) (hBlΩ : Bl ⊆ Ω) (hDcΩ : Dc ⊆ Ω) :
    ∃ (Δ Δbd : Set E3) (r : (Fin 3 → ℝ) → E3),
      IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) Δ ∧
      Δbd = r '' stdSimplexBoundary 2 ∧
      Δ ⊆ Ω ∧ Δbd = Δ ∩ Ec := by
  sorry

theorem exists_pseudoCell_subdisk_with_rim
    {Ec Eint Ebd Bl Dc Dcint Ω Δ Δbd : Set E3} {P : E3}
    (hE : IsPseudoCell Ec Eint Ebd P) (hBl : IsPLBall 3 Bl)
    (hP : P ∈ interior Bl)
    (hDc : IsTopologicalCellWithInterior 2 Dc Dcint) (hDcE : Dc ⊆ Eint)
    (hPDc : P ∈ Dcint) (hBE : Bl ∩ Ec ⊆ Dc)
    (hgp : CrossesPseudoCell (frontier Bl) Ec Eint P)
    (hΩ : IsOpen Ω) (hBlΩ : Bl ⊆ Ω) (hDcΩ : Dc ⊆ Ω)
    (hΔ : Δ ⊆ Ω) (hΔbd : Δbd = Δ ∩ Ec) :
    ∃ DJ DJint : Set E3, IsTopologicalCellWithInterior 2 DJ DJint ∧
      DJ ⊆ Ec ∧ DJ \ DJint = Δbd ∧ P ∈ DJint := by
  sorry

theorem reduced_disk_of_subleaves
    {Ec Eint Ebd Bl Dc Dcint Ω : Set E3} {P : E3}
    (hE : IsPseudoCell Ec Eint Ebd P) (hBl : IsPLBall 3 Bl)
    (hP : P ∈ interior Bl)
    (hDc : IsTopologicalCellWithInterior 2 Dc Dcint) (hDcE : Dc ⊆ Eint)
    (hPDc : P ∈ Dcint) (hBE : Bl ∩ Ec ⊆ Dc)
    (hgp : CrossesPseudoCell (frontier Bl) Ec Eint P)
    (hΩ : IsOpen Ω) (hBlΩ : Bl ⊆ Ω) (hDcΩ : Dc ⊆ Ω) :
    ∃ (Δ Δbd : Set E3) (r : (Fin 3 → ℝ) → E3),
      IsPLHomeomorphOn r (stdSimplex ℝ (Fin 3)) Δ ∧
      Δbd = r '' stdSimplexBoundary 2 ∧
      Δ ⊆ Ω ∧ Δbd = Δ ∩ Ec ∧
      ∃ DJ DJint : Set E3, IsTopologicalCellWithInterior 2 DJ DJint ∧
        DJ ⊆ Ec ∧ DJ \ DJint = Δbd ∧ P ∈ DJint := by
  obtain ⟨Δ, Δbd, r, hr, hrim, hΔΩ, hΔEc⟩ :=
    exists_outermost_disk_with_intrinsic_rim hE hBl hP hDc hDcE hPDc hBE
      hgp hΩ hBlΩ hDcΩ
  obtain ⟨DJ, DJint, hDJ, hDJE, hDJrim, hPDJ⟩ :=
    exists_pseudoCell_subdisk_with_rim hE hBl hP hDc hDcE hPDc hBE
      hgp hΩ hBlΩ hDcΩ hΔΩ hΔEc
  exact ⟨Δ, Δbd, r, hr, hrim, hΔΩ, hΔEc,
    DJ, DJint, hDJ, hDJE, hDJrim, hPDJ⟩

end DifferentialGeometry.Topology.PiecewiseLinear.Section32ReducedDiskProbe
