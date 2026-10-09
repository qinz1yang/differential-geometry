import DifferentialGeometry.Geometry.Metric.TangentCone
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Basic.ENNReal.Basic

set_option autoImplicit false

open Set Metric
open scoped ENNReal

namespace Metric

noncomputable def linearDimension (X : Type*) [MetricSpace X] [∀ p : X, HasAnglesAt p] : ℝ≥0∞ :=
  ⨆ p : X, ⨆ k : ℕ, ⨆ (_ : ∃ f : EuclideanSpace ℝ (Fin k) → TangentCone p, Isometry f),
    (k : ℝ≥0∞)

theorem linearDimension_le_iff
    {X : Type*} [MetricSpace X] [∀ p : X, HasAnglesAt p] {d : ℝ≥0∞} :
    linearDimension X ≤ d ↔ ∀ p : X, ∀ k : ℕ,
      ∀ f : EuclideanSpace ℝ (Fin k) → TangentCone p, Isometry f → (k : ℝ≥0∞) ≤ d := by
  simp only [linearDimension, iSup_le_iff, forall_exists_index]

end Metric
