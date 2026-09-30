import DifferentialGeometry.Geometry.Comparison.ExpandedIntrinsicEightInterpolation
import DifferentialGeometry.Geometry.Comparison.HyperbolicInterpolation

set_option autoImplicit false


open Set Metric Real Topology
open DifferentialGeometry.Analysis.ODE

namespace DifferentialGeometry.Geometry.Comparison.Toponogov

variable {X : Type*} [MetricSpace X] [CompleteSpace X]
variable (hcurves : ∀ a b : X, ∀ ε : ℝ, 0 < ε →
  ∃ c : unitInterval → X, Continuous c ∧ c 0 = a ∧ c 1 = b ∧
    eVariationOn c univ < ENNReal.ofReal (dist a b + ε))
variable (o : X) {κ R : ℝ} (hκ : 0 < κ) (hR : 0 < R)
variable [LocallyCompactSpace (ball o (8 * R))]
variable (hlocal : ∀ z : ball o (8 * R), ∃ Ω : Set (ball o (8 * R)),
  @IsOpen (ball o (8 * R))
    (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 8 * R)).toUniformSpace.toTopologicalSpace Ω ∧
  @fourPointComparison (ball o (8 * R))
    (intrinsicBallMetricSpace hcurves o (by positivity : 0 < 8 * R)) κ Ω ∧ z ∈ Ω)

include hcurves hκ hR hlocal

theorem comparisonAngleNegCurvature_le_of_expanded_intrinsic_8_buffer_segment
    {A : ℝ} (hA : 0 < A) (σ : Icc (0 : ℝ) A → X) (hσ : Isometry σ)
    (hσmem : ∀ s, σ s ∈ closedBall o (3 * R / 2)) {z : X} (hz : z ∈ closedBall o (3 * R / 2))
    (hzero : dist z (σ ⟨0, ⟨le_rfl, hA.le⟩⟩) ≤ 5 * R / 2)
    (hend : dist z (σ ⟨A, ⟨hA.le, le_rfl⟩⟩) ≤ 5 * R / 2)
    (hne : σ ⟨0, ⟨le_rfl, hA.le⟩⟩ ≠ z) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) A) :
    comparisonAngleNegCurvature κ A (dist (σ ⟨0, ⟨le_rfl, hA.le⟩⟩) z)
        (dist (σ ⟨A, ⟨hA.le, le_rfl⟩⟩) z) ≤
      comparisonAngleNegCurvature κ t (dist (σ ⟨0, ⟨le_rfl, hA.le⟩⟩) z)
        (dist (σ ⟨t, ⟨ht.1.le, ht.2⟩⟩) z) := by
  apply comparisonAngleNegCurvature_le_of_cosh_interpolate hκ ht.1 ht.2 (dist_pos.mpr hne)
  have h := hyperbolicInterpolate_le_of_expanded_intrinsic_8_buffer
    hcurves o hκ hR hlocal hA σ hσ hσmem hz hzero hend t ⟨ht.1.le, ht.2⟩
  rw [IccExtend_of_mem hA.le σ ⟨ht.1.le, ht.2⟩] at h
  simpa only [dist_comm] using h

end DifferentialGeometry.Geometry.Comparison.Toponogov
