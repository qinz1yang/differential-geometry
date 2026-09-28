/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CyclicMarkedPrisms
import DifferentialGeometry.Topology.PiecewiseLinear.MarkedCylindricalBuffer

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "E2" => EuclideanSpace ℝ (Fin 2)
local notation "Δ" => Convexity.StdSimplex.coordinateSet ℝ (Fin 3)
local notation "p" => (stdCenter 1 : Fin 3 → ℝ)

theorem exists_thickening_marked_cycle
    (n : ℕ) (C : Fin (n + 3) → Set E3)
    (ρ : Fin (n + 3) → (Fin 3 → ℝ) × ℝ → E3)
    (hρ : ∀ i, IsPLHomeomorphOn (ρ i) (Δ ×ˢ Icc (0 : ℝ) 1) (C i))
    (hmeet : ∀ i, C i ∩ C (i + 1) = ρ i '' (Δ ×ˢ {(1 : ℝ)}))
    (hcap : ∀ i, ρ i '' (Δ ×ˢ {(1 : ℝ)}) = ρ (i + 1) '' (Δ ×ˢ {(0 : ℝ)}))
    (hfar : ∀ i j, i ≠ j → j ≠ i + 1 → i ≠ j + 1 → Disjoint (C i) (C j))
    (hmark : ∀ i, ρ i (p, 1) = ρ (i + 1) (p, 0))
    {U : Set E3} (hU : IsOpen U) (hCU : ∀ i, C i ⊆ U) :
    ∃ P : Set E3, P ⊆ U ∧ (⋃ i, C i) ⊆ interior P ∧
      ∃ Φ : (Metric.closedBall (0 : E2) 1 × Metric.sphere (0 : E2) 1) ≃ₜ P,
        (⋃ i, ρ i '' ({p} ×ˢ Icc (0 : ℝ) 1)) =
          Subtype.val '' (Φ '' {z | (z.1 : E2) = 0}) := by
  have hp : p ∈ Δ :=
    openSimplex_stdVertices_subset_stdSimplex (stdCenter_mem_openSimplex 1)
  obtain ⟨f, hf, hclosed, haxis⟩ := exists_cylindricalDiagram_iUnion_of_marked_cycle
    (isPLBall_stdSimplex 2).isPolyhedron hp n C ρ hρ hmeet hcap hfar hmark
  obtain ⟨P, hPU, hCP, Φ, hΦ⟩ :=
    hf.exists_thickening_marked_stdCenter hclosed hU (iUnion_subset hCU)
  exact ⟨P, hPU, hCP, Φ, haxis.symm.trans hΦ⟩

end DifferentialGeometry.Topology.PiecewiseLinear
