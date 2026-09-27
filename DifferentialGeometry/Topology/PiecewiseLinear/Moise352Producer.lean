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
