/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.SphericalDiskPlaneChart

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Plane" => EuclideanSpace ℝ (Fin 2)

theorem IsPLBall.exists_boundary_disk_trace_chart
    {Y D : Set E3} (hY : IsPLBall 3 Y) (hD : IsPLBall 2 D) (hDY : D ⊆ frontier Y) :
    ∃ (A : Set Plane) (p : E3 → Plane) (c : OpenPartialHomeomorph E3 (Plane × ℝ)),
      IsPLBall 2 A ∧ IsPLHomeomorphOn p D A ∧ D ⊆ c.source ∧
      (∀ x, p x = (c x).1) ∧
      (∀ x ∈ c.source, x ∈ frontier Y ↔ (c x).2 = 0) ∧
      ∀ x ∈ c.source, x ∈ Y ↔ 0 ≤ (c x).2 := by
  obtain ⟨c, hDc, -, hc, -, hcfr, hcY⟩ :=
    hY.exists_openPartialHomeomorph_boundary_disk_plane hD hDY isOpen_univ (subset_univ D)
  let p : E3 → Plane := fun x => (c x).1
  have hcp : IsPiecewiseAffineOn c D := hc.mono_of_isPolyhedron hD.isPolyhedron hDc
  have hp : IsPiecewiseAffineOn p D := by
    have h := (isPiecewiseAffineOn_of_affine (LinearMap.fst ℝ Plane ℝ).toAffineMap
      isOpen_univ).comp hcp
    rw [preimage_univ, inter_univ] at h
    exact h.congr fun _ _ => rfl
  have hpi : InjOn p D := by
    intro x hx y hy hxy
    apply c.injOn (hDc hx) (hDc hy)
    exact Prod.ext hxy (((hcfr x (hDc hx)).mp (hDY hx)).trans
      ((hcfr y (hDc hy)).mp (hDY hy)).symm)
  have hpl : IsPLHomeomorphOn p D (p '' D) :=
    isPLHomeomorphOn_of_isPiecewiseAffineOn_of_bijOn hD.isPolyhedron hp hpi.bijOn_image
  exact ⟨p '' D, p, c, hD.of_isPLHomeomorphOn hpl, hpl, hDc, fun _ => rfl, hcfr, hcY⟩

end DifferentialGeometry.Topology.PiecewiseLinear
