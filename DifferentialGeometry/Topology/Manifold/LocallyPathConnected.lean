/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Analysis.Convex.PathConnected
import Mathlib.Topology.Homeomorph.Lemmas

/-! Locally Path Connected. -/

open Set Topology

namespace DifferentialGeometry.Topology.Manifold

theorem locallyPathConnectedSpace_of_modelWithCorners
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
    [TopologicalSpace M] [ChartedSpace H M] : LocallyPathConnectedSpace M := by
  have : LocallyPathConnectedSpace (range I) := I.convex_range.locallyPathConnectedSpace
  have : LocallyPathConnectedSpace H :=
    I.isClosedEmbedding.isEmbedding.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  exact ChartedSpace.locallyPathConnectedSpace H M

end DifferentialGeometry.Topology.Manifold
