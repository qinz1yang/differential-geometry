import DifferentialGeometry.Geometry.Comparison.IntrinsicEightInterpolation
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

theorem comparisonAngleNegCurvature_le_of_intrinsic_8_buffer_segment
    {A : ℝ} (hA : 0 < A) (σ : Icc (0 : ℝ) A → X) (hσ : Isometry σ)
    (hσmem : ∀ s, σ s ∈ closedBall o (3 * R / 2)) {z : X} (hz : z ∈ closedBall o R)
    (hzero : dist z (σ ⟨0, ⟨le_rfl, hA.le⟩⟩) ≤ 2 * R)
    (hend : dist z (σ ⟨A, ⟨hA.le, le_rfl⟩⟩) ≤ 2 * R)
    (hne : σ ⟨0, ⟨le_rfl, hA.le⟩⟩ ≠ z) {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) A) :
    comparisonAngleNegCurvature κ A (dist (σ ⟨0, ⟨le_rfl, hA.le⟩⟩) z)
        (dist (σ ⟨A, ⟨hA.le, le_rfl⟩⟩) z) ≤
      comparisonAngleNegCurvature κ t (dist (σ ⟨0, ⟨le_rfl, hA.le⟩⟩) z)
        (dist (σ ⟨t, ⟨ht.1.le, ht.2⟩⟩) z) := by
  apply comparisonAngleNegCurvature_le_of_cosh_interpolate hκ ht.1 ht.2 (dist_pos.mpr hne)
  have h := hyperbolicInterpolate_le_of_intrinsic_8_buffer
    hcurves o hκ hR hlocal hA σ hσ hσmem hz hzero hend t ⟨ht.1.le, ht.2⟩
  rw [IccExtend_of_mem hA.le σ ⟨ht.1.le, ht.2⟩] at h
  simpa only [dist_comm] using h

theorem comparisonAngleNegCurvature_le_of_radial_isometries_intrinsic_8_buffer
    (γ β : Icc (0 : ℝ) R → X) (hγ : Isometry γ) (hβ : Isometry β)
    (hγ0 : γ ⟨0, ⟨le_rfl, hR.le⟩⟩ = o) (hβ0 : β ⟨0, ⟨le_rfl, hR.le⟩⟩ = o)
    {s t : ℝ} (hs : s ∈ Ioc (0 : ℝ) R) (ht : t ∈ Ioc (0 : ℝ) R) :
    comparisonAngleNegCurvature κ R R
        (dist (γ ⟨R, ⟨hR.le, le_rfl⟩⟩) (β ⟨R, ⟨hR.le, le_rfl⟩⟩)) ≤
      comparisonAngleNegCurvature κ s t
        (dist (γ ⟨s, ⟨hs.1.le, hs.2⟩⟩) (β ⟨t, ⟨ht.1.le, ht.2⟩⟩)) := by
  have hγrad (u : Icc (0 : ℝ) R) : dist o (γ u) = u.val := by
    rw [← hγ0, hγ.dist_eq, Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg,
      abs_of_nonneg u.property.1]
  have hβrad (u : Icc (0 : ℝ) R) : dist o (β u) = u.val := by
    rw [← hβ0, hβ.dist_eq, Subtype.dist_eq, Real.dist_eq, zero_sub, abs_neg,
      abs_of_nonneg u.property.1]
  have hγmem (u : Icc (0 : ℝ) R) : γ u ∈ closedBall o R := by
    rw [mem_closedBall, dist_comm, hγrad]
    exact u.property.2
  have hβmem (u : Icc (0 : ℝ) R) : β u ∈ closedBall o R := by
    rw [mem_closedBall, dist_comm, hβrad]
    exact u.property.2
  have hγlarge (u : Icc (0 : ℝ) R) : γ u ∈ closedBall o (3 * R / 2) :=
    (closedBall_subset_closedBall (by linarith)) (hγmem u)
  have hβlarge (u : Icc (0 : ℝ) R) : β u ∈ closedBall o (3 * R / 2) :=
    (closedBall_subset_closedBall (by linarith)) (hβmem u)
  have hdist (u v : Icc (0 : ℝ) R) : dist (γ u) (β v) ≤ 2 * R := by
    have h := dist_triangle (γ u) o (β v)
    rw [dist_comm (γ u) o, hγrad, hβrad] at h
    linarith [u.property.2, v.property.2]
  have hfirst := comparisonAngleNegCurvature_le_of_intrinsic_8_buffer_segment
    hcurves o hκ hR hlocal hR γ hγ hγlarge
    (hβmem ⟨R, ⟨hR.le, le_rfl⟩⟩)
    (by rw [hγ0, dist_comm, hβrad]; linarith)
    (by rw [dist_comm]; exact hdist _ _)
    (by rw [hγ0]; exact dist_pos.mp (by rw [hβrad]; exact hR)) hs
  rw [hγ0, hβrad] at hfirst
  have hsecond := comparisonAngleNegCurvature_le_of_intrinsic_8_buffer_segment
    hcurves o hκ hR hlocal hR β hβ hβlarge
    (hγmem ⟨s, ⟨hs.1.le, hs.2⟩⟩)
    (by rw [hβ0, dist_comm, hγrad]; linarith [hs.2])
    (hdist _ _)
    (by rw [hβ0]; exact dist_pos.mp (by rw [hγrad]; exact hs.1)) ht
  rw [hβ0, hγrad] at hsecond
  have hsecond' : comparisonAngleNegCurvature κ s R
      (dist (γ ⟨s, ⟨hs.1.le, hs.2⟩⟩) (β ⟨R, ⟨hR.le, le_rfl⟩⟩)) ≤
      comparisonAngleNegCurvature κ s t
      (dist (γ ⟨s, ⟨hs.1.le, hs.2⟩⟩) (β ⟨t, ⟨ht.1.le, ht.2⟩⟩)) := by
    simpa only [comparisonAngleNegCurvature_comm κ R s,
      comparisonAngleNegCurvature_comm κ t s, dist_comm] using hsecond
  exact hfirst.trans hsecond'

end DifferentialGeometry.Geometry.Comparison.Toponogov
