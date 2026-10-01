import DifferentialGeometry.Topology.Manifold.ClosedOriented

set_option autoImplicit false

noncomputable section

open Bundle Manifold Set
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Topology.ClosedOrientedManifold

universe u

variable (n : ℕ)

local instance : ChartedSpace (EuclideanSpace ℝ (Fin n)) PEmpty.{u + 1} where
  atlas := ∅
  chartAt := fun x => PEmpty.elim x
  mem_chart_source := fun x => PEmpty.elim x
  chart_mem_atlas := fun x => PEmpty.elim x

local instance : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ PEmpty.{u + 1} where
  compatible := by
    intro e _ he _
    exact he.elim

def empty : ClosedOrientedManifold.{u} n where
  Carrier := PEmpty.{u + 1}
  orientation :=
    { dimension_eq := by simp
      orientation := fun x => PEmpty.elim x
      locally_constant := fun p => PEmpty.elim p }

end DifferentialGeometry.Topology.ClosedOrientedManifold
