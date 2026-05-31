import Mathlib.Geometry.Manifold.VectorBundle.Riemannian
import Mathlib.Geometry.Manifold.VectorBundle.Tangent

set_option autoImplicit false

/-!
# RicciFlower metrics

This file contains the RicciFlower-facing alias for smooth Riemannian metrics.
It is not a realized object; realized metric families import this definition.
-/

namespace RicciFlower

open Bundle
open scoped Manifold ContDiff

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
variable {H : Type*} [TopologicalSpace H]

/-- RicciFlower-facing alias for a smooth Riemannian metric on `TM`. -/
abbrev SmoothRiemannianMetric
    (I : ModelWithCorners Real E H) (M : Type*)
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] : Type _ :=
  Bundle.ContMDiffRiemannianMetric I ∞ E (TangentSpace I : M -> Type _)

/-! ## Metric-space ball helpers -/

/-- Metric balls are monotone in the radius. -/
theorem ball_subset_of_le
    {X : Type*} [PseudoMetricSpace X] {x : X} {r R : Real}
    (hr : r ≤ R) :
    Metric.ball x r ⊆ Metric.ball x R := by
  intro y hy
  rw [Metric.mem_ball] at hy ⊢
  exact lt_of_lt_of_le hy hr

/-- Closed metric balls are monotone in the radius. -/
theorem cball_subset_of_le
    {X : Type*} [PseudoMetricSpace X] {x : X} {r R : Real}
    (hr : r ≤ R) :
    Metric.closedBall x r ⊆ Metric.closedBall x R := by
  intro y hy
  rw [Metric.mem_closedBall] at hy ⊢
  exact le_trans hy hr

end RicciFlower
