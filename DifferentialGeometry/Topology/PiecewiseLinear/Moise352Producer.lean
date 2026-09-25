/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ApproximationManifold
import DifferentialGeometry.Topology.PiecewiseLinear.Moise352OfOpen
import DifferentialGeometry.Topology.PiecewiseLinear.PLSmoothingCompact
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Endpoint
import DifferentialGeometry.Topology.PiecewiseLinear.Section34Terminal

/-!
# Moise 35.2 and smooth structures on compact three-manifolds

The cell diagram of Section 34 (`section34CellDiagram`) gives the open case of Moise 35.2
(`moise352Open`), hence Moise 35.2 itself (`moise352`) and the piecewise linear approximation
theorem for three-manifolds in its manifold and chart forms (`plApproximationManifold_three`,
`plApproximation_three`).  Together with the compact smoothing theorem
`plSmoothingModelCompact_three`, every compact Hausdorff topological three-manifold carries a
smooth structure (`exists_isManifold_three`).
-/

open scoped Manifold ContDiff

namespace DifferentialGeometry.Topology.PiecewiseLinear

universe u

theorem moise352Open : Moise352Open.{u} 3 :=
  moise352Open_of_section34CellDiagram section34CellDiagram

theorem moise352 : Moise352.{u} 3 :=
  moise352_three_of_open moise352Open

theorem plApproximationManifold_three : PLApproximationManifold.{u} 3 :=
  plApproximationManifold_three_of_open moise352Open

theorem plApproximation_three : PLApproximation.{u} 3 :=
  plApproximation_of_plApproximationManifold plApproximationManifold_three

theorem plSmoothingCompact_three : PLSmoothingCompact.{u} 3 :=
  plSmoothingCompact_of_plSmoothingModelCompact plSmoothingModelCompact_three

theorem exists_isManifold_three {M : Type u} [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M] :
    ∃ C : ChartedSpace (EuclideanSpace ℝ (Fin 3)) M,
      letI := C
      IsManifold (𝓡 3) ∞ M :=
  exists_isManifold_of_plApproximation_of_plSmoothingCompact plApproximation_three
    plSmoothingCompact_three

end DifferentialGeometry.Topology.PiecewiseLinear
