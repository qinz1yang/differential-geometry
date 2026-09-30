import DifferentialGeometry.Geometry.Comparison.IntrinsicLocalComparison
import DifferentialGeometry.Geometry.Comparison.IntrinsicBufferComparison

set_option autoImplicit false

open Set Metric

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

theorem fourPointComparison_two_ball_of_local_256_buffer
    {X : Type*} [MetricSpace X] [CompleteSpace X]
    (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
      ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
        eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
    (o : X) {κ R : ℝ} (hκ : 0 ≤ κ) (hR : 0 < R)
    [LocallyCompactSpace (ball o (256 * R))]
    (hlocal : ∀ z ∈ ball o (256 * R),
      ∃ Ω : Set X, IsOpen Ω ∧ fourPointComparison κ Ω ∧ z ∈ Ω) :
    fourPointComparison κ (ball o (2 * R)) := by
  apply fourPointComparison_ambient_two_ball_of_intrinsic_256_buffer hcurves o hκ hR
  intro z
  exact (exists_local_fourPointComparison_intrinsicBall_iff hcurves o
    (by positivity : 0 < 256 * R) z).mpr (hlocal z z.property)

end DifferentialGeometry.Geometry.Comparison.Toponogov
