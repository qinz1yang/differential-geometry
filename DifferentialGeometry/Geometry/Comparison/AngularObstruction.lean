import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic

set_option autoImplicit false

namespace Metric

open Set

variable {D : Type*} [MetricSpace D]

def AngularObstruction (D : Type*) [MetricSpace D] (m : ℕ) (θ : ℝ) : Prop :=
  ¬ ∃ (ξ : D) (ζ : Fin (m + 1) → D),
    (∀ i j, i ≠ j → Real.pi / 2 + θ < dist (ζ i) (ζ j)) ∧
    ∀ j, Real.pi / 2 - θ < dist ξ (ζ j)

theorem AngularObstruction.exists_acute_anchor {m : ℕ} {θ : ℝ}
    (h : AngularObstruction D m θ) (ζ : Fin (m + 1) → D)
    (hζ : ∀ i j, i ≠ j → Real.pi / 2 + θ < dist (ζ i) (ζ j)) (ξ : D) :
    ∃ j, dist ξ (ζ j) ≤ Real.pi / 2 - θ := by
  by_contra hn
  apply h
  exact ⟨ξ, ζ, hζ, fun j => lt_of_not_ge (fun hj => hn ⟨j, hj⟩)⟩

end Metric
