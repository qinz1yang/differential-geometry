/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SolidTorus
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldWithBoundary
import Mathlib.Combinatorics.SimpleGraph.CycleGraph

/-! Combinatorial solid tori with cyclic decompositions into three-dimensional cells. -/

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

open Classical in
def IsCombinatorialSolidTorus (S : Set E) : Prop :=
  IsTopologicalSolidTorus S ∧
    ∃ n : ℕ, 3 ≤ n ∧ ∃ C : Fin n → Geometry.SimplicialComplex ℝ E,
      (∀ i, (C i).faces.Finite) ∧ (⋃ i, (C i).space) = S ∧
      (∀ i, IsPLBall 3 (C i).space) ∧
      ∀ i j, i ≠ j →
        (((C i).space ∩ (C j).space).Nonempty ↔ (SimpleGraph.cycleGraph n).Adj i j) ∧
        ((SimpleGraph.cycleGraph n).Adj i j →
          IsPLBall 2 ((C i).space ∩ (C j).space) ∧
          (C i).space ∩ (C j).space ⊆ (boundaryComplex 3 (C i)).space ∧
          (C i).space ∩ (C j).space ⊆ (boundaryComplex 3 (C j)).space)

end DifferentialGeometry.Topology.PiecewiseLinear
