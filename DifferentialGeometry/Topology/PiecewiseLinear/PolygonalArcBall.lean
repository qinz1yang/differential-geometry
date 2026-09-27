/-
Copyright (c) 2026 DifferentialGeometry contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: DifferentialGeometry contributors
-/
import DifferentialGeometry.Topology.PiecewiseLinear.PolygonalSchoenflies
import DifferentialGeometry.External.Schoenflies.PolyArcRealize

open Set

namespace DifferentialGeometry.Topology.PiecewiseLinear

open Schoenflies

theorem isPLBall_one_polyArc_carrier {n : ℕ} (A : PolyArc n) : IsPLBall 1 A.carrier := by
  have hprefix : ∀ k ≤ n, IsPLBall 1 (A.prefixCarrier k) := by
    intro k
    induction k with
    | zero =>
      intro _
      rw [A.prefixCarrier_zero]
      exact isPLBall_segment A.vertex_ne
    | succ k ih =>
      intro hk
      rw [A.prefixCarrier_succ]
      exact isPLBall_union_of_isArcBetween (ih (by omega)) (isPLBall_segment A.vertex_ne)
        (A.isArcBetween_prefixCarrier k (by omega))
        (isArcBetween_segment A.vertex_ne) (A.prefixCarrier_meet hk)
  exact hprefix n le_rfl

theorem isPLBall_one_of_isArcBetween_of_isPolygonal {A : Set Plane} {p q : Plane}
    (hA : IsArcBetween A p q) (hpoly : IsPolygonal A) : IsPLBall 1 A := by
  obtain ⟨n, P, hP, _, _⟩ := isPolyArcCarrier_of_isPolygonal hA hpoly
  exact hP ▸ isPLBall_one_polyArc_carrier P

end DifferentialGeometry.Topology.PiecewiseLinear
