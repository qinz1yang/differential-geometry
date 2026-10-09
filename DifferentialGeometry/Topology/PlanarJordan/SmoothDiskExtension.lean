/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.Homeomorph.PlanarExtension
import DifferentialGeometry.Topology.PlanarJordan.Transport
import Mathlib.Geometry.Manifold.LocalDiffeomorph

open Set Metric
open scoped ContDiff Manifold

namespace DifferentialGeometry.Topology.PlanarJordan

open Schoenflies (Plane)

theorem image_closedBall_eq_closure_inside_of_boundary_eq (F : Plane ≃ₜ Plane)
    {e : sphere (0 : Plane) 1 → Plane} (he : ∀ z : sphere (0 : Plane) 1, F z = e z) :
    F '' closedBall (0 : Plane) 1 = closure (Schoenflies.inside (range e)) := by
  have hJ : Schoenflies.IsJordanCurve (sphere (0 : Plane) 1) := by
    simpa only [Subtype.range_coe] using isJordanCurve_range_of_isEmbedding_circle
      (Topology.IsEmbedding.subtypeVal :
        Topology.IsEmbedding (Subtype.val : sphere (0 : Plane) 1 → Plane))
  have hfrontier := frontier_closedBall (0 : Plane) one_ne_zero
  have hnonempty : (interior (closedBall (0 : Plane) 1)).Nonempty := by
    rw [interior_closedBall (0 : Plane) one_ne_zero]
    exact nonempty_ball.mpr one_pos
  have hclosed : closure (Schoenflies.inside (sphere (0 : Plane) 1)) = closedBall 0 1 := by
    simpa only [hfrontier] using closure_inside_frontier_eq_of_isCompact
      (isCompact_closedBall (0 : Plane) 1) (hfrontier.symm ▸ hJ) hnonempty
  have hboundary : F '' sphere (0 : Plane) 1 = range e := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, (he ⟨x, hx⟩).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.property, he x⟩
  calc
    F '' closedBall (0 : Plane) 1 =
        F '' closure (Schoenflies.inside (sphere (0 : Plane) 1)) := by rw [hclosed]
    _ = closure (Schoenflies.inside (F '' sphere (0 : Plane) 1)) := by
      rw [F.image_closure, image_inside]
    _ = closure (Schoenflies.inside (range e)) := by rw [hboundary]

theorem exists_homeomorph_closedBall_closure_inside_of_partialDiffeomorph
    (φ : PartialDiffeomorph 𝓘(ℝ, Plane) 𝓘(ℝ, Plane) Plane Plane ∞)
    (hφ : closedBall (0 : Plane) 1 ⊆ φ.source)
    {e : sphere (0 : Plane) 1 → Plane}
    (he : ∀ z : sphere (0 : Plane) 1, φ z = e z) :
    ∃ F : closedBall (0 : Plane) 1 ≃ₜ closure (Schoenflies.inside (range e)),
      (∀ z : closedBall (0 : Plane) 1, (F z : Plane) = φ z) ∧
        ∀ z : closure (Schoenflies.inside (range e)), (F.symm z : Plane) = φ.symm z := by
  obtain ⟨G, hG⟩ := φ.toOpenPartialHomeomorph.exists_homeomorph_eqOn_closedBall 0
    zero_lt_one hφ
  have hboundary : ∀ z : sphere (0 : Plane) 1, G z = e z := fun z =>
    (hG (sphere_subset_closedBall z.property)).trans (he z)
  have himage : φ '' closedBall (0 : Plane) 1 = closure (Schoenflies.inside (range e)) :=
    (image_congr hG).symm.trans
      (image_closedBall_eq_closure_inside_of_boundary_eq G hboundary)
  exact ⟨φ.toOpenPartialHomeomorph.homeomorphOfImageSubsetSource hφ himage,
    fun _ => rfl, fun _ => rfl⟩

end DifferentialGeometry.Topology.PlanarJordan
