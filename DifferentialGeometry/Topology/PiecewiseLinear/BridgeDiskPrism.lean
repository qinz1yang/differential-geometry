/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.BridgeDiskEquivalence
import DifferentialGeometry.Topology.PiecewiseLinear.StandardMarkedBridge

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "V2" => Fin 3 → ℝ

theorem IsBridgeDisk.exists_prism_axis
    {C A B : Set E3} {a b : E3} (h : IsBridgeDisk C A B a b) (hC : IsPLBall 3 C) :
    ∃ ρ : V2 × ℝ → E3,
      IsPLHomeomorphOn ρ (Convexity.StdSimplex.coordinateSet ℝ (Fin 3) ×ˢ Icc (0 : ℝ) 1) C ∧
      ρ '' ({stdCenter 1} ×ˢ Icc (0 : ℝ) 1) = A ∧
      ρ (stdCenter 1, 0) = a ∧ ρ (stdCenter 1, 1) = b := by
  obtain ⟨C₀, B₀, ρ₀, hC₀, hρ₀, hb₀⟩ := exists_isBridgeDisk_prism_axis
  obtain ⟨G, hG, hGA, hGa, hGb⟩ := hb₀.exists_isPLHomeomorphOn_map_arc h hC₀ hC
  refine ⟨G ∘ ρ₀, hρ₀.trans hG, ?_, hGa, hGb⟩
  rw [image_comp]
  exact hGA

end DifferentialGeometry.Topology.PiecewiseLinear
