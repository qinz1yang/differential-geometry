/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PlanarDiskOrientation
import DifferentialGeometry.Topology.LocalDegree.BoundaryTraceOrientationAt

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open DifferentialGeometry.LocalDegree

local notation "Plane" => EuclideanSpace ℝ (Fin 2)
local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem isPLCirclePositive_iff_halfspace_orientationParity_eq_zero_at
    {P : Set Plane} (hP : IsPLBall 2 P) {f : Plane → Plane}
    (hf : ContinuousOn f P) (hfi : InjOn f P)
    (hB : MapsTo f (interior P) (interior P)) (hS : BijOn f (frontier P) (frontier P))
    {x : Plane} (hx : x ∈ interior P)
    {F : E3 → E3} {U : Set E3} (hU : IsOpen U)
    (hF : ContinuousOn F U) (hFi : InjOn F U) (hUx : euclideanProductPoint 1 x 0 ∈ U)
    (htrace : ∀ y ∈ U, (euclideanProductChart 1 y).2 = 0 →
      F y = euclideanProductPoint 1 (f (euclideanProductChart 1 y).1) 0)
    (hpos : ∀ y ∈ U, 0 < (euclideanProductChart 1 y).2 →
      0 < (euclideanProductChart 1 (F y)).2)
    (hneg : ∀ y ∈ U, (euclideanProductChart 1 y).2 < 0 →
      (euclideanProductChart 1 (F y)).2 < 0) :
    IsPLCirclePositive (frontier P) f ↔
      embeddingOrientationParity hU hF hFi ⟨euclideanProductPoint 1 x 0, hUx⟩ = 0 := by
  have hsign := embeddingOrientationParity_eq_of_boundary_trace_at isOpen_interior hU
    (hf.mono interior_subset) (hfi.mono interior_subset) hF hFi hx hUx htrace hpos hneg
  exact (isPLCirclePositive_frontier_iff_orientationParity_eq_zero hP hf hfi hB hS hx).trans
    (by rw [hsign])

theorem isPLCirclePositive_iff_halfspace_orientationParity_eq_zero
    {P : Set Plane} (hP : IsPLBall 2 P) {f : Plane → Plane}
    (hf : ContinuousOn f P) (hfi : InjOn f P)
    (hB : MapsTo f (interior P) (interior P)) (hS : BijOn f (frontier P) (frontier P))
    (hP0 : (0 : Plane) ∈ interior P)
    {F : E3 → E3} {U : Set E3} (hU : IsOpen U)
    (hF : ContinuousOn F U) (hFi : InjOn F U) (hU0 : (0 : E3) ∈ U)
    (htrace : ∀ y ∈ U, (euclideanProductChart 1 y).2 = 0 →
      F y = euclideanProductPoint 1 (f (euclideanProductChart 1 y).1) 0)
    (hpos : ∀ y ∈ U, 0 < (euclideanProductChart 1 y).2 →
      0 < (euclideanProductChart 1 (F y)).2)
    (hneg : ∀ y ∈ U, (euclideanProductChart 1 y).2 < 0 →
      (euclideanProductChart 1 (F y)).2 < 0) :
    IsPLCirclePositive (frontier P) f ↔
      embeddingOrientationParity hU hF hFi ⟨0, hU0⟩ = 0 := by
  have hzero : euclideanProductPoint 1 (0 : Plane) 0 = 0 := by simp [euclideanProductPoint]
  have hpoint : euclideanProductPoint 1 (0 : Plane) 0 ∈ U := hzero.symm ▸ hU0
  simpa only [hzero] using isPLCirclePositive_iff_halfspace_orientationParity_eq_zero_at
    hP hf hfi hB hS hP0 hU hF hFi hpoint htrace hpos hneg

end DifferentialGeometry.Topology.PiecewiseLinear
