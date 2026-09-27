/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Mesh
import DifferentialGeometry.Topology.Manifold.ChartPartialDiffeomorph
import Mathlib.Geometry.Manifold.Instances.Real

open Set
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {E N : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace N] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) N]
  [IsManifold (𝓡 2) ∞ N]

theorem exists_isSubdivision_closedStars_subset_chart_preimages
    (K : Geometry.SimplicialComplex ℝ E) [Finite K.faces]
    (e : OpenPartialHomeomorph E N) (hK : K.space ⊆ e.source) :
    ∃ R : Geometry.SimplicialComplex ℝ E, IsSubdivision R K ∧ R.faces.Finite ∧
      ∀ s ∈ R.faces, ∃ y : N,
        (⋃ v ∈ s, closedStar R v) ⊆ e.source ∧
        e '' (⋃ v ∈ s, closedStar R v) ⊆
          (extChartAtPartialDiffeomorph (𝓡 2) ∞ y).source := by
  let U : N → Set E := fun y =>
    e.source ∩ e ⁻¹' (extChartAtPartialDiffeomorph (𝓡 2) ∞ y).source
  have hU (y : N) : IsOpen (((↑) : K.space → E) ⁻¹' U y) :=
    (e.isOpen_inter_preimage (extChartAtPartialDiffeomorph (𝓡 2) ∞ y).open_source).preimage
      continuous_subtype_val
  have hcover : K.space ⊆ ⋃ y, U y := by
    intro z hz
    exact mem_iUnion.mpr ⟨e z, hK hz, mem_extChartAt_source (I := 𝓡 2) (e z)⟩
  obtain ⟨R, hR, hfinite, hstars⟩ :=
    exists_isSubdivision_closedStars_subset_cover K U hU hcover
  refine ⟨R, hR, hfinite, fun s hs => ?_⟩
  obtain ⟨y, hy⟩ := hstars s hs
  refine ⟨y, fun z hz => (hy hz).1, ?_⟩
  rintro _ ⟨z, hz, rfl⟩
  exact (hy hz).2

end DifferentialGeometry.Topology.PiecewiseLinear
