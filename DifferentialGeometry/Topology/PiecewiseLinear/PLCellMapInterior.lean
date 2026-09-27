/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PLCellOnBoundary
import DifferentialGeometry.Topology.Manifold.EmbeddingLocalHomeomorph

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)

variable {M N : Type*} [TopologicalSpace M] [ChartedSpace E3 M]
  [TopologicalSpace N] [ChartedSpace E3 N]

theorem IsPLHomeomorphInto.image_interior_of_cell
    {P PB : Set M} {f : M → N} (hf : IsPLHomeomorphInto 3 f P)
    (hP : IsPLCellOn 3 P PB) : f '' interior P = interior (f '' P) := by
  rw [← hP.sdiff_boundary_eq_interior, hf.injOn.image_sdiff_subset hP.boundary_subset]
  exact (hP.image hf).sdiff_boundary_eq_interior

theorem IsPLCellOn.exists_openPartialHomeomorph_of_map
    {P PB : Set M} (hP : IsPLCellOn 3 P PB) {f : M → N}
    (hf : IsPLHomeomorphInto 3 f P) :
    ∃ F : OpenPartialHomeomorph M N,
      F.source = interior P ∧ F.target = interior (f '' P) ∧ ∀ x, F x = f x := by
  have : Nonempty M := ⟨hP.nonempty.choose⟩
  obtain ⟨F, hFs, hFt, hF⟩ := exists_openPartialHomeomorph_of_continuousOn_injOn
    (E := E3) isOpen_interior (hf.continuousOn.mono interior_subset)
      (hf.injOn.mono interior_subset)
  exact ⟨F, hFs, hFt.trans (hf.image_interior_of_cell hP), hF⟩

omit [TopologicalSpace N] [ChartedSpace E3 N] in
theorem IsPLCellOn.exists_interior_chart {P PB : Set M} (hP : IsPLCellOn 3 P PB) :
    ∃ c : OpenPartialHomeomorph M E3, c.source = interior P := by
  obtain ⟨A, r, u, hr, hu, hP, -⟩ := hP
  obtain ⟨F, -, hFt, -⟩ :=
    (isPLCellOn_id_of_isPLBall hr).exists_openPartialHomeomorph_of_map hu
  refine ⟨F.symm, ?_⟩
  change F.target = interior P
  simpa only [hP] using hFt

end DifferentialGeometry.Topology.PiecewiseLinear
