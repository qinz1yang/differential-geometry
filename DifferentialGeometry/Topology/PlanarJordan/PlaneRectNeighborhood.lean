/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PlanarJordan.PlanarArcSmoothing

open Set Metric

namespace DifferentialGeometry.Topology.PlanarJordan

open Schoenflies (Plane)

theorem ball_subset_planeRect {x : Plane} {r a b c d : ℝ}
    (ha : a ≤ x 0 - r) (hb : x 0 + r ≤ b)
    (hc : c ≤ x 1 - r) (hd : x 1 + r ≤ d) :
    ball x r ⊆ planeRect a b c d := by
  intro y hy
  have h0 := (planeAbsSub_le_dist y x 0).trans_lt (mem_ball.mp hy)
  have h1 := (planeAbsSub_le_dist y x 1).trans_lt (mem_ball.mp hy)
  rw [abs_lt] at h0 h1
  exact ⟨by linarith [h0.1], by linarith [h0.2],
    by linarith [h1.1], by linarith [h1.2]⟩

end DifferentialGeometry.Topology.PlanarJordan
