import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Mathlib.MeasureTheory.Integral.Bochner.Set

noncomputable section
open Set Filter MeasureTheory
open scoped Topology ENNReal NNReal ContDiff

namespace DifferentialGeometry.Analysis

theorem integral_ball_add_collar
    (f : EuclideanSpace ℝ (Fin 2) → ℝ) {r R : ℝ} (hrR : r ≤ R)
    (hi : IntegrableOn f (Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R)) :
    (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) r, f x) +
      (∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R \ Metric.closedBall 0 r, f x) =
      ∫ x in Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R, f x := by
  have hnull := measure_eq_zero_iff_ae_notMem.mp
    (Measure.addHaar_sphere volume (0 : EuclideanSpace ℝ (Fin 2)) r)
  have heq : Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R \ Metric.closedBall 0 r =ᵐ[volume]
      Metric.ball (0 : EuclideanSpace ℝ (Fin 2)) R \ Metric.ball 0 r := by
    filter_upwards [hnull] with x hx
    apply propext
    have hn : dist x (0 : EuclideanSpace ℝ (Fin 2)) ≠ r := hx
    change (dist x (0 : EuclideanSpace ℝ (Fin 2)) < R ∧ ¬ dist x 0 ≤ r) ↔
      (dist x (0 : EuclideanSpace ℝ (Fin 2)) < R ∧ ¬ dist x 0 < r)
    exact and_congr_right fun _ =>
      ⟨fun h => (lt_of_not_ge h).le |> not_lt.mpr,
        fun h => not_le.mpr (lt_of_le_of_ne (not_lt.mp h) hn.symm)⟩
  have heqi := setIntegral_congr_set (f := f) heq
  have hsplit := setIntegral_sdiff Metric.isOpen_ball.measurableSet hi (Metric.ball_subset_ball hrR)
  have h := eq_sub_iff_add_eq.mp (heqi.trans hsplit)
  convert h using 1
  exact add_comm _ _

end DifferentialGeometry.Analysis

end
