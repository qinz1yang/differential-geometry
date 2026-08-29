-- Modified 2026-04-28: updated internal import paths for project namespace
import DifferentialGeometry.External.DeGiorgi.BallScaling
import DifferentialGeometry.External.DeGiorgi.DeGiorgiIteration
import DifferentialGeometry.External.DeGiorgi.Localization

/-!
# Moser Iteration Constants

This module contains the anchor constants for the Chapter 06 Moser iteration.
-/

noncomputable section

open MeasureTheory

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

/-- The anchor constant coming from the normalized De Giorgi `L² → L∞` bound. -/
noncomputable def CMoserAnchor (d : ℕ) [NeZero d] : ℝ :=
  max 1
    (max ((CDeGiorgiSubsolutionNormalized d) ^ 2)
      (8 * (Mst : ℝ) ^ 2 * (CGns d 2) ^ 2))

/-- The geometric decay ratio `q = (d-2)/d` used in the Moser iteration. -/
noncomputable def moserDecayRatio (d : ℕ) [hNeZero : NeZero d] : ℝ := by
  let _ := hNeZero
  exact ((d : ℝ) - 2) / (d : ℝ)

/-- Dimension-only constant `C(d)` for the basic Moser `L^p → L∞` estimate.

It is chosen large enough to absorb both the existing `p = 2` De Giorgi anchor
and the purely geometric product appearing in the exact Moser iteration. -/
noncomputable def CMoser (d : ℕ) [NeZero d] : ℝ :=
  let base := CMoserAnchor d
  if _hd : 2 < (d : ℝ) then
    max base
      (((32 : ℝ) * base) ^ ((d : ℝ) / 2) *
        4 ^ (∑' n : ℕ, (n : ℝ) * moserDecayRatio d ^ n))
  else
    base

theorem one_le_C_MoserAnchor : 1 ≤ CMoserAnchor d := by
  simp [CMoserAnchor]

theorem C_DeGiorgi_subsolution_normalized_sq_le_C_MoserAnchor :
    (CDeGiorgiSubsolutionNormalized d) ^ 2 ≤ CMoserAnchor d := by
  simp [CMoserAnchor]

theorem cutoff_sobolev_anchor_le_C_MoserAnchor :
    8 * (Mst : ℝ) ^ 2 * (CGns d 2) ^ 2 ≤ CMoserAnchor d := by
  simp [CMoserAnchor]

theorem C_MoserAnchor_le_C_Moser :
    CMoserAnchor d ≤ CMoser d := by
  by_cases hd : 2 < (d : ℝ)
  · simp [CMoser, hd]
  · simp [CMoser, hd]

theorem one_le_C_Moser : 1 ≤ CMoser d := by
  exact (one_le_C_MoserAnchor (d := d)).trans (C_MoserAnchor_le_C_Moser (d := d))

theorem C_DeGiorgi_subsolution_normalized_sq_le_C_Moser :
    (CDeGiorgiSubsolutionNormalized d) ^ 2 ≤ CMoser d := by
  exact
    (C_DeGiorgi_subsolution_normalized_sq_le_C_MoserAnchor (d := d)).trans
      (C_MoserAnchor_le_C_Moser (d := d))

end DeGiorgi
