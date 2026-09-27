/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.Section34CapDeletion

open Set Topology

namespace DifferentialGeometry.Topology.PiecewiseLinear

variable {M Y : Type*} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 3)) M]
  [TopologicalSpace Y]

theorem IsPLCellOn.exists_image_interior_mem_open
    {S B : Set M} (hS : IsPLCellOn 3 S B)
    {f : M → Y} {x : M} (hx : x ∈ S) (hf : ContinuousAt f x)
    {O : Set Y} (hO : IsOpen O) (hfx : f x ∈ O) :
    (f '' interior S ∩ O).Nonempty := by
  have hxcl : x ∈ closure (interior S) := hS.subset_closure_interior hx
  have hpre : f ⁻¹' O ∈ 𝓝 x := hf (hO.mem_nhds hfx)
  obtain ⟨z, hzpre, hzint⟩ := (mem_closure_iff_nhds.mp hxcl) (f ⁻¹' O) hpre
  exact ⟨f z, ⟨z, hzint, rfl⟩, hzpre⟩

end DifferentialGeometry.Topology.PiecewiseLinear
