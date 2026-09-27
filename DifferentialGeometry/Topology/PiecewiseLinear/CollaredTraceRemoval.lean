/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.CollaredTraceLocality

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem HasFiniteCollaredTrace.sdiff_of_disjoint {L T C : Set E3}
    (h : HasFiniteCollaredTrace L T) (hC : IsClosed C) (hCT : Disjoint C T)
    (hrem : IsPolyhedron (L \ C)) : HasFiniteCollaredTrace (L \ C) T := by
  apply h.of_locally_eq hrem hC.isOpen_compl (fun x hx => disjoint_left.mp hCT.symm hx)
  ext x
  exact ⟨fun hx => ⟨hx.1.1, hx.2⟩, fun hx => ⟨⟨hx.1, hx.2⟩, hx.2⟩⟩

end DifferentialGeometry.Topology.PiecewiseLinear
