import DifferentialGeometry.Analysis.Parabolic.QuasiLinear.GraphicalCurveShortening.Lp
noncomputable section
open MeasureTheory
open scoped ENNReal
namespace DifferentialGeometry.Analysis.Parabolic

theorem graphRemainderAction_circle_tame
    {n : ℕ} {α : Type*} [MeasurableSpace α] {μ : Measure α}
    (p q : Lp (EuclideanSpace ℝ (Fin n)) ∞ μ)
    (f h : Lp ℝ 2 μ) :
    ‖graphDiffusionRemainderAction p f - graphDiffusionRemainderAction q h‖ ≤
      ‖p‖ ^ 2 * ‖f - h‖ + (‖p‖ + ‖q‖) * ‖p - q‖ * ‖h‖ := by
  exact graphDiffusionRemainderAction_sub_norm_le p q f h

end DifferentialGeometry.Analysis.Parabolic
