-- Modified 2026-04-28: updated internal import paths for project namespace
-- Modified 2026-05-16: style-warning cleanup
import DifferentialGeometry.External.DeGiorgi.BallExtension.SmoothApproximation

/-!
# Chapter 02: Ball Extension

This file collects the main extension estimates built from the core, geometry,
rough-input, and smooth-approximation layers.
-/

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace DeGiorgi

variable {d : ℕ} [NeZero d]

local notation "E" => EuclideanSpace ℝ (Fin d)

-- === Main extension estimates ===
-- Pre-compiled in the geometry file where PiLp instance synthesis is already resolved.


end DeGiorgi
