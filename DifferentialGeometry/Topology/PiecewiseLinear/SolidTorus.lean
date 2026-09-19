/-
Copyright (c) 2026 Yuan Liao. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yuan Liao
-/
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.Homeomorph.Lemmas

/-! Topological solid tori. -/

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

def IsTopologicalSolidTorus {E : Type u} [TopologicalSpace E] (S : Set E) : Prop :=
  Nonempty (S ≃ₜ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 2)) 1 ×
    Metric.sphere (0 : EuclideanSpace ℝ (Fin 2)) 1))

end DifferentialGeometry.Topology.PiecewiseLinear
