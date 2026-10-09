/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.MapApproximation
import Mathlib.Topology.MetricSpace.Thickening

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

theorem exists_isPiecewiseAffineOn_mapsTo_eqOn
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {P Q : Set E} (hP : IsPolyhedron P) (hQ : IsPolyhedron Q) (hQP : Q ⊆ P)
    {U : Set F} (hU : IsOpen U) {f : E → F} (hf : ContinuousOn f P)
    (hfQ : IsPiecewiseAffineOn f Q) (hmap : MapsTo f P U) :
    ∃ g : E → F, IsPiecewiseAffineOn g P ∧ EqOn g f Q ∧ MapsTo g P U := by
  obtain ⟨ε, hε, hεU⟩ :=
    (hP.isCompact.image_of_continuousOn hf).exists_thickening_subset_open hU hmap.image_subset
  obtain ⟨g, hg, heq, hdist⟩ :=
    exists_isPiecewiseAffineOn_dist_lt_eqOn hP hQ hQP hP.isCompact hf hfQ hε
  refine ⟨g, hg, heq, fun x hx => hεU ?_⟩
  exact Metric.mem_thickening_iff.mpr ⟨f x, mem_image_of_mem f hx, hdist x hx⟩

end DifferentialGeometry.Topology.PiecewiseLinear
