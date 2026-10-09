/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.ManifoldConnectivity

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

open Classical in
theorem IsCombinatorialManifold.exists_face_superset_card_eq {n : ℕ}
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (hK : IsCombinatorialManifold n K) {s : Finset E} (hs : s ∈ K.faces) :
    ∃ t ∈ K.faces, s ⊆ t ∧ t.card = n + 1 :=
  hK.isCombinatorialManifoldWithBoundary.exists_face_superset_card_eq hs

end DifferentialGeometry.Topology.PiecewiseLinear
